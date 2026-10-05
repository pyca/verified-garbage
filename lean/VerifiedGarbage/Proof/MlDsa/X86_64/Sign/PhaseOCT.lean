import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.Sign.Vals
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Lay`. -/
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

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Sign.Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the function writes (`scratch` and `sig`):
a buffer it only reads may overlap another such buffer, but not one of
these. -/
abbrev wRegs : List Reg := [.rbx, .r14]

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Sign.Ptr) (l : Nat) (q : VG.Impl.MlDsa.X86_64.Sign.Ptr) (k : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB bs p l && VG.Proof.MlDsa.X86_64.Sign.inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.wRegs) || decide (q.1 ∈ VG.Proof.MlDsa.X86_64.Sign.wRegs))) ||
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
      exact List.mem_cons_of_mem _ (VG.Proof.MlDsa.X86_64.Sign.lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold VG.Proof.MlDsa.X86_64.Sign.inB at h
  split at h
  · rename_i n hn; exact ⟨n, VG.Proof.MlDsa.X86_64.Sign.lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l k : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.sepB bs p l q k = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB bs p l = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.wRegs ∨ q.1 ∈ VG.Proof.MlDsa.X86_64.Sign.wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1 |> fun h1 => ⟨h1, h.1.2, h.2⟩

/-! ## Regions -/

theorem contains_offset' {base : Addr} {off len n : Nat} (h : off + len ≤ n) (hn : n < 2 ^ 64) :
    (⟨base, n⟩ : Region).Contains (base + BitVec.ofNat 64 off) len := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem sub_offset' {base : Addr} {off len n : Nat} (h : off + len ≤ n) (hn : n < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, n⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - (base + BitVec.ofNat 64 off)).toNat + off) (2 ^ 64)
  omega

theorem off_disj {base : Addr} {a b la lb : Nat} (h : a + la ≤ b) (hb : b + lb < 2 ^ 64) :
    Region.Disjoint ⟨base + BitVec.ofNat 64 a, la⟩ ⟨base + BitVec.ofNat 64 b, lb⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have e : x - (base + BitVec.ofNat 64 a) = (x - (base + BitVec.ofNat 64 b)) + BitVec.ofNat 64 (b - a) := by
    rw [show BitVec.ofNat 64 (b - a) = BitVec.ofNat 64 b - BitVec.ofNat 64 a by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega]
    bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b - a) (by omega),
    Nat.mod_eq_of_lt (by omega)] at h₁
  omega

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 off - r.base = (a - r.base) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

/-! ## Layouts -/

section
variable (D : Nat)

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other, from the return address and
from the `D` bytes of stack below `rsp`, not wrapping around, and
permitted; and `D` bytes of stack below `rsp` that do not wrap around. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.wRegs ∨ b'.1 ∈ VG.Proof.MlDsa.X86_64.Sign.wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) D).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨s.gpr b.1, b.2⟩
  sp : D ≤ (s.gpr .rsp).toNat
  dsm : D < 2 ^ 32

end

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
include L

theorem Lay.sub {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ ⟨s.gpr p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec h
  exact ⟨n, hm, VG.Proof.MlDsa.X86_64.Sign.sub_offset' hl (by have := L.small _ hm; omega)⟩

theorem Lay.disj {p q : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l k : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ ⟨VG.Proof.MlDsa.X86_64.Sign.pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := VG.Proof.MlDsa.X86_64.Sign.sepB_spec h
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec hp
  obtain ⟨m, hm, hk⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (VG.Proof.MlDsa.X86_64.Sign.sub_offset' hl (by omega))).sub_right (VG.Proof.MlDsa.X86_64.Sign.sub_offset' hk (by omega))
  · show Region.Disjoint ⟨s.gpr p.1 + _, l⟩ ⟨s.gpr q.1 + _, k⟩
    rw [← e]
    rcases hs with h1 | h2
    · exact VG.Proof.MlDsa.X86_64.Sign.off_disj h1 (by omega)
    · exact (VG.Proof.MlDsa.X86_64.Sign.off_disj h2 (by omega)).symm

theorem Lay.stkD {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) :
    (below (s.gpr .rsp) D).Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.retD {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) :
    (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.ret _ hn).sub_right hsub

theorem Lay.nwp {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) : (VG.Proof.MlDsa.X86_64.Sign.pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.iR {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s p) l := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec h
  exact VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega)

theorem Lay.iW {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB wbs p l = true) : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s p) l := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec h
  exact VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega)

theorem Lay.cR {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) : Covers [⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩] (s.rd ++ s.wr) :=
  Covers.one (L.iR h)

theorem Lay.cW {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB wbs p l = true) : Covers [⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩] s.wr :=
  Covers.one (L.iW h)

end

/-! ## What a piece of code leaves -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat) : Region := ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w.1, w.2⟩

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the `D` bytes of stack. -/
structure PostB (D : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ VG.Proof.MlDsa.X86_64.Sign.bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) D]) s.mem s'.mem

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (D : Nat) (s s' : State) (ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) : Prop := VG.Proof.MlDsa.X86_64.Sign.PostB D s s' (ws.map (VG.Proof.MlDsa.X86_64.Sign.toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) (p : VG.Impl.MlDsa.X86_64.Sign.Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && VG.Proof.MlDsa.X86_64.Sign.inB bs p l && ws.all fun w => VG.Proof.MlDsa.X86_64.Sign.sepB bs p l w.1 w.2

theorem PostB.pa {D : Nat} {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.X86_64.Sign.PostB D s s' W) {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) :
    VG.Proof.MlDsa.X86_64.Sign.pa s' p = VG.Proof.MlDsa.X86_64.Sign.pa s p := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, hP.bs _ h]

theorem PostB.refl (D : Nat) (s : State) (W : List Region) : VG.Proof.MlDsa.X86_64.Sign.PostB D s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.trans {D : Nat} {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : VG.Proof.MlDsa.X86_64.Sign.PostB D s s₁ W₁)
    (h₂ : VG.Proof.MlDsa.X86_64.Sign.PostB D s₁ s₂ W₂) (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : VG.Proof.MlDsa.X86_64.Sign.PostB D s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.rsp.trans h₁.rsp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

theorem map_toR_post {D : Nat} {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.X86_64.Sign.PostB D s s' W) {ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) : ws.map (VG.Proof.MlDsa.X86_64.Sign.toR s') = ws.map (VG.Proof.MlDsa.X86_64.Sign.toR s) :=
  List.map_congr_left fun w hw => by simp only [VG.Proof.MlDsa.X86_64.Sign.toR, hP.pa (h w hw)]

/-- `PostB.trans`, with the regions written given as pointers. -/
theorem PPostB.trans {D : Nat} {s s₁ s₂ : State} {ws₁ ws₂ ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₁ ws₁)
    (h₂ : VG.Proof.MlDsa.X86_64.Sign.PPostB D s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₂ ws := by
  have h₂' : VG.Proof.MlDsa.X86_64.Sign.PostB D s₁ s₂ (ws₂.map (VG.Proof.MlDsa.X86_64.Sign.toR s)) := by rw [← VG.Proof.MlDsa.X86_64.Sign.map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem Lay.post {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} {W : List Region} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
    (hP : VG.Proof.MlDsa.X86_64.Sign.PostB D s s' W) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (hcs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, ?_, ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · simp only [VG.Proof.MlDsa.X86_64.Sign.retR, e b hb, hP.rsp]; exact L.ret b hb
  · rw [hP.rsp]; exact L.sp
  · exact L.dsm

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)}
  {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (VG.Proof.MlDsa.X86_64.Sign.toR s) ++ [below (s.gpr .rsp) D], Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ r := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

omit L in
theorem keepB_cs (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p l = true) : p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

omit L in
theorem keepB_in (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p l = true) : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.keepB, Bool.and_eq_true] at hc; exact hc.1.2

theorem Lay.keepBytes (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' p) l = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) l := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Sign.keepB_cs hc)]
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec (VG.Proof.MlDsa.X86_64.Sign.keepB_in hc)
  exact VG.Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : VG.Spec.MlDsa.Poly} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : PolyIs s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) f) : PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' p) f := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Sign.keepB_cs hc)]
  exact polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepRed (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p)) : Reduced s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' p) := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Sign.keepB_cs hc)]
  exact reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p 1024 = true) :
    polyAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' p) = polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Sign.keepB_cs hc)]
  exact polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepW (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s' p) 64 = s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s p) 64 := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Sign.keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
    {ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hin : ∀ w ∈ ws, VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := VG.Proof.MlDsa.X86_64.Sign.retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
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
  lx : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs x
  ly : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs y
  regs : ∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1
  rsp : x.gpr .rsp = y.gpr .rsp

theorem LRel.eq {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y) {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := VG.Proof.MlDsa.X86_64.Sign.inB_spec hp
  exact h.regs (p.1, n) hn

theorem LRel.pa {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y) {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) : VG.Proof.MlDsa.X86_64.Sign.pa x p = VG.Proof.MlDsa.X86_64.Sign.pa y p := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, h.eq hp]

theorem LRel.post {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (hx : VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W₁) (hy : VG.Proof.MlDsa.X86_64.Sign.PostB D y y' W₂) :
    VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x' y' :=
  ⟨h.lx.post hx hcs, h.ly.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb), h.regs b hb],
    by rw [hx.rsp, hy.rsp, h.rsp]⟩

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Call`. -/
section

/-!
# ML-DSA signing on x86-64: calls of verified code

A primitive the function calls is any code verified against its shared contract
(`Spec/MlDsa/Poly.lean`) for some stack of `S` bytes that leaves 8 bytes for
the return address in the `D` bytes the function gives its calls, and that
never writes `rsp` (`Callee`). A call, with the moves of its arguments before
it (`glueCall_ok`), leaves the permissions and the callee-saved registers as
they were, and changes memory only within the buffers it writes and the `D`
bytes of stack below `rsp`. Two runs of it leak the same when the callee's
public data agree (`glueCall_tr`), and a callee whose result is public in its
own runs (`RetPub`) returns the same in both (`glueCallRet_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ VG.Proof.MlDsa.X86_64.Sign.argRegs := by decide

theorem bases_cs : ∀ r ∈ VG.Proof.MlDsa.X86_64.Sign.bases, r ∈ calleeSaved := by decide

/-- Code verified against the contract `k S` for a stack of `S` bytes, with
8 bytes to spare in `D`, which never writes `rsp` and whose calls nest
within `D` bytes. -/
structure Callee (k : Nat → Contract isa) (D : Nat) (c : Prog isa) where
  /-- The stack its contract gives it. -/
  S : Nat
  hS : S + 8 ≤ D
  ver : Verified X86_64.target c (k S)
  nosp : NoSp c
  depth : 8 * (c.depth + 1) ≤ D

/-- The result of `c` (the low 32 bits of `rax`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32

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
  exact ⟨(VG.Proof.MlDsa.X86_64.Sign.execBlock_nomem h e₁).trans (VG.Proof.MlDsa.X86_64.Sign.execBlock_nomem h e₂).symm, trivial⟩

theorem nomem_append {a b : List Instr} (ha : ∀ i ∈ a, ∀ s, isa.addrs i s = [])
    (hb : ∀ i ∈ b, ∀ s, isa.addrs i s = []) : ∀ i ∈ a ++ b, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h s, hb i h s]

theorem lea_nomem (d : Reg) (p : VG.Impl.MlDsa.X86_64.Sign.Ptr) : ∀ i ∈ VG.Impl.MlDsa.X86_64.Sign.lea d p, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [VG.Impl.MlDsa.X86_64.Sign.lea, List.mem_cons, List.not_mem_nil, or_false] at hi
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
        rw [this]; omega]
      bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := D - 8) (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem ce_below {sp : Addr} {D S : Nat} {R : Region} (h : (below sp D).Disjoint R) (hS : S + 8 ≤ D)
    (hDs : D < 2 ^ 32) : (below (sp - 8) S).Disjoint R :=
  (h.sub_left (below_sub hS (by omega))).sub_left (below_callee sp S)

theorem ce_stackBelow {sp : Addr} {D S : Nat} {R : Region} (h : (below sp D).Disjoint R) (hS : S + 8 ≤ D)
    (hDs : D < 2 ^ 32) : ∀ r ∈ stackBelow (sp - 8) S, r.Disjoint R := by
  intro r hr
  cases S with
  | zero => simp [stackBelow] at hr
  | succ S =>
    simp only [stackBelow, List.mem_singleton] at hr
    subst hr
    exact VG.Proof.MlDsa.X86_64.Sign.ce_below h hS hDs

theorem ce_wf {sp : Addr} {D S : Nat} (hS : S + 8 ≤ D) (hsp : D ≤ sp.toNat) :
    S ≤ (sp - 8).toNat := by
  rw [BitVec.toNat_sub]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  have := sp.isLt
  omega

theorem abi_wf_of {ws : List Nat} (hws : ws.length ≤ 6) {S : Nat} {s : State} (h : S ≤ (s.gpr .rsp).toNat) :
    X86_64.abi.wf ws S s := by
  simp only [X86_64.abi, VG.X86_64.argRegs, List.length_cons, List.length_nil, Nat.reduceAdd, hws, ite_true]
  cases S <;> simp_all

/-- The facts about the stack a callee's contract needs, on entry: its
stack pointer leaves `S` bytes below it. -/
theorem ce_wfS {ws : List Nat} (hws : ws.length ≤ 6) {D S : Nat} (hS : S + 8 ≤ D) {s : State}
    (hsp : D ≤ (s.gpr .rsp).toNat) (rd wr : List Region) : X86_64.abi.wf ws S (s.callEntry.withRegions rd wr) :=
  VG.Proof.MlDsa.X86_64.Sign.abi_wf_of hws (by simp only [State.withRegions_gpr, State.callEntry_rsp]; exact VG.Proof.MlDsa.X86_64.Sign.ce_wf hS hsp)

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
    (by simpa using (VG.Proof.MlDsa.X86_64.Sign.ce_ret h hD hDs).symm) hR hi

theorem ce_polyAt (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (VG.Proof.MlDsa.Sign.pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : polyAt s.callEntry.mem p = polyAt s.mem p :=
  polyAt_congr fun _ hi => VG.Proof.MlDsa.X86_64.Sign.ce_byte s (R := VG.Proof.MlDsa.Sign.pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi

theorem ce_natPolyAt (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (VG.Proof.MlDsa.Sign.pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : natPolyAt s.callEntry.mem p = natPolyAt s.mem p :=
  natPolyAt_congr fun _ hi => VG.Proof.MlDsa.X86_64.Sign.ce_byte s (R := VG.Proof.MlDsa.Sign.pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi

theorem ce_reduced (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (VG.Proof.MlDsa.Sign.pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : Reduced s.callEntry.mem p ↔ Reduced s.mem p :=
  ⟨reduced_congr fun _ hi => (VG.Proof.MlDsa.X86_64.Sign.ce_byte s (R := VG.Proof.MlDsa.Sign.pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi).symm,
    reduced_congr fun _ hi => VG.Proof.MlDsa.X86_64.Sign.ce_byte s (R := VG.Proof.MlDsa.Sign.pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi⟩

theorem ce_bytesAt (s : State) {D : Nat} {p : Addr} {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : (below (s.gpr .rsp) D).Disjoint ⟨p, n⟩) (hD : 8 ≤ D) (hDs : D < 2 ^ 32) :
    bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  VG.Proof.MlKem.bytesAt_congr fun _ hi => VG.Proof.MlDsa.X86_64.Sign.ce_byte s (R := ⟨p, n⟩) h hD hDs hn hi

/-! ## A call, with the moves of its arguments -/

/-- The moves of the arguments, then a call of verified code. -/
theorem glueCall_ok {D : Nat} {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PostB D s s' wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono hg fun s1 ⟨⟨hV, hm⟩, k1⟩ => ?_)
  refine WP.call hv hsp (by omega) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr), k1.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr))],
      by rw [hcs .rsp (by decide), k1.gpr (by decide)], ?_⟩,
      fun r hr => by rw [hcs r hr, k1.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r hr)], s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf hd (by omega)

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
    (hr : VG.Proof.MlDsa.X86_64.Sign.RetPub k c) {P : State → State → Prop}
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
      · simp only [isa, VG.X86_64.ret] at r₁ r₂
        split at r₁ <;> [skip; cases r₁]
        split at r₂ <;> [skip; cases r₂]
        cases r₁; cases r₂
        simp only [State.setReg]
        rw [← g₁, ← g₂]; exact hrax

/-- The moves of the arguments then a call whose result is public: the same
trace, and the same result, in both runs. -/
theorem glueCallRet_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : VG.Proof.MlDsa.X86_64.Sign.RetPub k c) {P : State → State → Prop} {V : State → State → Prop}
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

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Glue`. -/
section

/-!
# ML-DSA signing on x86-64: the moves of a call's arguments

`setArgs as` moves each argument (a pointer or an immediate) into its
register: afterwards each argument register holds the argument's value in the
state before the moves (`setArgs_ok`), and nothing else changed but those
registers. With it, a call of verified code (`callP_ok`, `callP_tr`,
`callPRet_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)
open VG.Spec.MlDsa

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86_64.Sign.Arg.val (s : State) : Arg → BitVec 64
  | .ptr p => VG.Proof.MlDsa.X86_64.Sign.pa s p
  | .imm v => BitVec.ofNat 64 v

/-- A pointer in a register of `bases`, with an offset that is an
immediate; or an immediate of 32 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Sign.Arg.ok : Arg → Bool
  | .ptr p => decide (p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (p.2 < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 32)

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs6) (s : State) :
    WP isa (.block (a.mov d)) s fun s1 => (s1.gpr d = a.val s ∧ s1.mem = s.mem) ∧ Keep [d] s s1 := by
  have hd' : d ∉ VG.Proof.MlDsa.X86_64.Sign.bases := fun h => by revert h hd; cases d <;> decide
  refine WP.keep [d] ?_ (by cases a <;> cases d <;> rfl)
  cases a with
  | ptr p =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    have hne : p.1 ≠ d := fun e => hd' (e ▸ ha.1)
    simp only [Arg.mov, VG.Impl.MlDsa.X86_64.Sign.lea, Arg.val]
    xrun [VG.Proof.MlDsa.X86_64.Sign.sx_ofNat ha.2]
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, movi, Arg.val]
    xrun [VG.Proof.MlDsa.X86_64.Sign.sw_ofNat ha]

theorem Keep.of_sub {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s s' := h.mono hs

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
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setArgsGen_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1)
      fun s2 ⟨⟨h2, hm2⟩, k2⟩ => ⟨⟨fun da hda => ?_, hm2.trans hm1⟩, (k1.trans k2).mono fun r hr => by simpa using hr⟩
    -- The values in `s1` are those in `s`: the moves keep the bases.
    have hval : ∀ b : Arg, b.ok = true → b.val s1 = b.val s := fun b hb => by
      cases b with
      | ptr p =>
        simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [Arg.val, VG.Proof.MlDsa.X86_64.Sign.pa]
        have hdb : d ∉ VG.Proof.MlDsa.X86_64.Sign.bases := fun h => by have := hd d (List.mem_cons_self ..); revert h this; cases d <;> decide
        rw [k1.gpr (by simp only [List.mem_singleton]; exact fun e => hdb (e ▸ hb.1))]
      | imm v => rfl
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr hn.1, h1]
    · have := List.of_mem_zip hda
      rw [h2 da hda, hval da.2 (List.all_eq_true.mp ha.2 _ this.2)]

theorem argRegs6_nodup : argRegs6.Nodup := by decide


theorem argRegs6_sub : ∀ as : List Arg, ∀ r ∈ (argRegs6.zip as).map (·.1), r ∈ VG.Proof.MlDsa.X86_64.Sign.argRegs := by
  intro as r hr
  obtain ⟨⟨d, a⟩, hm, rfl⟩ := List.mem_map.mp hr
  have := (List.of_mem_zip hm).1
  simp only [argRegs6, VG.Proof.MlDsa.X86_64.Sign.argRegs, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  rcases this with h | h | h | h | h | h <;> simp [h]

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgs as)) s fun s1 =>
      ((∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1 := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setArgsGen_ok argRegs6 as VG.Proof.MlDsa.X86_64.Sign.argRegs6_nodup (fun _ h => h) ha s) fun s1 ⟨h, k⟩ => ⟨h, ?_⟩
  refine ⟨fun r hr => k.gpr fun hm => hr ?_, k.2⟩
  simp only [argRegs6, VG.Proof.MlDsa.X86_64.Sign.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with h | h | h | h | h | h <;> simp [h]

theorem setArgs_nomem (as : List Arg) : ∀ i ∈ setArgs as, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, _, hi⟩ := hi
  cases a with
  | ptr p => exact VG.Proof.MlDsa.X86_64.Sign.lea_nomem d p i hi s
  | imm v => exact VG.Proof.MlDsa.X86_64.Sign.movi_nomem d v i hi s

/-! ## Calls -/

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn2 {a b : Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [a, b] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6])⟩

theorem argsIn3 {a b c : Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [a, b, c] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6])⟩

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [a, b, c, d] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s ∧ s1.gpr .r9 = f.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6]), h (.r9, f) (by simp [argRegs6])⟩

theorem callP_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32) {as : List Arg} (ha : as.all Arg.ok = true)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1, VG.Proof.MlDsa.X86_64.Sign.ArgsIn as s s1 → s1.mem = s.mem → Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callP n c as) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PostB D s s' wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∃ s1, VG.Proof.MlDsa.X86_64.Sign.ArgsIn as s s1 ∧ s1.mem = s.mem ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ :=
  VG.Proof.MlDsa.X86_64.Sign.glueCall_ok hv hsp hd hD (VG.Proof.MlDsa.X86_64.Sign.setArgs_ok as ha s) hpre hc hw

theorem callP_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → (VG.Proof.MlDsa.X86_64.Sign.ArgsIn as x x1 ∧ x1.mem = x.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs x x1 →
      (VG.Proof.MlDsa.X86_64.Sign.ArgsIn as y y1 ∧ y1.mem = y.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (callP n c as) fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Sign.glueCall_tr hv hct (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr (VG.Proof.MlDsa.X86_64.Sign.setArgs_nomem as)) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Sign.setArgs_ok as ha x, VG.Proof.MlDsa.X86_64.Sign.setArgs_ok as ha y⟩) hP

theorem callPRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : VG.Proof.MlDsa.X86_64.Sign.RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → (VG.Proof.MlDsa.X86_64.Sign.ArgsIn as x x1 ∧ x1.mem = x.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs x x1 →
      (VG.Proof.MlDsa.X86_64.Sign.ArgsIn as y y1 ∧ y1.mem = y.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Sign.argRegs y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (callP n c as) fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 :=
  VG.Proof.MlDsa.X86_64.Sign.glueCallRet_tr hv hr (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr (VG.Proof.MlDsa.X86_64.Sign.setArgs_nomem as)) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Sign.setArgs_ok as ha x, VG.Proof.MlDsa.X86_64.Sign.setArgs_ok as ha y⟩)
    hP

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Keccak`. -/
section

/-!
# ML-DSA signing on x86-64: SHAKE256 through the sponge functions

Zeroing the Keccak state at `scratch` (`kzero_ok`), and the calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` on it, with the
working space at `scratch + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from the
sponge functions' own call lemmas, `Proof/MlKem/X86_64/KCall.lean`); then
`shakeAt ps out len`, which zeroes the state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: the output of the sponge from the padded
state of their concatenation (`shake_ok`), leaking only the addresses
(`shake_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_call
  pad_call squeeze_call)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-! ## Checks -/

/-- The Keccak state and the sponge functions' working space. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 && VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640

/-- A piece of `len` bytes at `src` that `vg_keccak_absorb` reads. -/
def kabsChk (bs : List (Reg × Nat)) (src : VG.Impl.MlDsa.X86_64.Sign.Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB bs src len && decide (src.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (src.2 < 2 ^ 31) && decide (len < 2 ^ 31) &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs src len (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 && VG.Proof.MlDsa.X86_64.Sign.sepB bs src len (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640

/-- The `len` bytes at `dst` that `vg_keccak_squeeze` writes. -/
def ksqzChk (bs wbs : List (Reg × Nat)) (dst : VG.Impl.MlDsa.X86_64.Sign.Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs dst len && VG.Proof.MlDsa.X86_64.Sign.inB bs dst len && decide (dst.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (dst.2 < 2 ^ 31) && decide (len < 2 ^ 31) &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 dst len && VG.Proof.MlDsa.X86_64.Sign.sepB bs dst len (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem kChk_spec {bs wbs : List (Reg × Nat)} (h : VG.Proof.MlDsa.X86_64.Sign.kChk bs wbs = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.kChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem kabsChk_spec {bs : List (Reg × Nat)} {src : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.kabsChk bs src len = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB bs src len = true ∧ src.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ src.2 < 2 ^ 31 ∧ len < 2 ^ 31 ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs src len (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs src len (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ksqzChk_spec {bs wbs : List (Reg × Nat)} {dst : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.ksqzChk bs wbs dst len = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs dst len = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs dst len = true ∧ dst.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ dst.2 < 2 ^ 31 ∧ len < 2 ^ 31 ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 dst len = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs dst len (VG.Impl.MlDsa.X86_64.Sign.sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The 16 bytes of stack of a call of a sponge function, from the layout. -/
theorem k16 {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true)
    {s1 : State} (hsp : s1.gpr .rsp = s.gpr .rsp) : (below (s1.gpr .rsp) 16).Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ := by
  rw [hsp]; exact (L.stkD h).sub_left (below_sub (by omega) (by have := L.dsm; omega))

theorem rate_small {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 31 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-! ## Zeroing the state -/

theorem zeroStep_ok (b : Reg) (d : Nat) (s : State) (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (VG.Impl.MlKem.X86_64.at_ b d) .rax]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr .rax)) ∧ Keep [] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hw]

theorem lane_sep (p : Addr) {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * i)) (64 / 8) (p + BitVec.ofNat 64 (8 * j)) (64 / 8) := by
  intro x hx hy
  simp only [Nat.reduceDiv] at hx hy
  bv_omega

/-- The lanes at `b + off`, zeroed. -/
theorem zeroSt_ok (b : Reg) (off : Nat) (s : State) (h0 : s.gpr .rax = 0)
    (hw : ∀ i < 25, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (VG.Impl.MlDsa.X86_64.Sign.zeroSt b off)) s fun s' =>
      stateAt s'.mem (s.gpr b + BitVec.ofNat 64 off) = Spec.Sha3.zero ∧
        Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧ Keep [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 64 = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, hz⟩ => ⟨?_, hf, hk⟩
  · have hb : s'.gpr b = s.gpr b := hk'.gpr (by simp)
    have ha : s'.gpr .rax = 0 := by rw [hk'.gpr (by simp), h0]
    have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
      fun s'' ⟨hm, hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
    · rw [hm, hb, e]
      exact hf.writeW (List.mem_singleton_self _) _ (VG.Proof.MlDsa.X86_64.Sign.contains_offset' (by omega) (by omega))
    · rw [hm, hb, e, ha]
      by_cases hjk : j = k
      · subst hjk; rw [Mem.readW_writeW_self64]
      · rw [Mem.readW_writeW_sep (VG.Proof.MlDsa.X86_64.Sign.lane_sep _ (by omega) hk hjk) (by decide), hz j (by omega)]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact hz i hi

theorem kzero_ok {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sign.kzero) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) = Spec.Sha3.zero := by
  obtain ⟨w0, _, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  rw [VG.Impl.MlDsa.X86_64.Sign.kzero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = s.mem ∧ s1.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm, hax⟩, k1⟩ => ?_
  have hbx : s1.gpr .rbx = s.gpr .rbx := k1.gpr (by decide)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.zeroSt_ok .rbx 0 s1 hax fun i hi => ?_) fun s2 ⟨hz, hf, k2⟩ => ?_
  · rw [k1.2.2, hbx]
    have h0 := L.iW w0
    exact VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (off := 8 * i) (l := 8) h0 (by omega) (by decide)
  · have k : Keep [.rax] s s2 := (k1.trans k2).mono fun r hr => by simpa using hr
    rw [hbx] at hz hf
    have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => k.gpr fun h => by
      simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    refine ⟨⟨k.2.1, k.2.2, fun r hr => hcs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr), hcs .rsp (by decide), ?_⟩, hcs, hz⟩
    rw [hm] at hf
    exact hf.mono fun r hr => List.mem_append_left _ hr

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block VG.Impl.MlDsa.X86_64.Sign.kzero) fun _ _ => True :=
  VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h x y hp) (by taint_decide)

/-! ## Absorbing -/

theorem kabsArgs {s s1 : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {src : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate pos : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc 200)] s s1)
    (hsp : s1.gpr .rsp = s.gpr .rsp) :
    AbsorbArgs s1 (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s src) (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200)) rate pos len := by
  obtain ⟨_, _, i0, i1, d01⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨is, _, _, hl, d0, d1⟩ := VG.Proof.MlDsa.X86_64.Sign.kabsChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn6 hA
  exact ⟨e1, e2, e3, e4, e5, e6, hrate, hpos,
    by omega, L.disj d01, L.disj d0, L.disj d1, VG.Proof.MlDsa.X86_64.Sign.k16 L hD i0 hsp, VG.Proof.MlDsa.X86_64.Sign.k16 L hD is hsp, VG.Proof.MlDsa.X86_64.Sign.k16 L hD i1 hsp⟩

theorem kabsOk {bs : List (Reg × Nat)} {src : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate pos : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.kabsChk bs src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) : [Arg.ptr (VG.Impl.MlDsa.X86_64.Sign.sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc 200)].all Arg.ok = true := by
  obtain ⟨_, b1, o1, hl, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kabsChk_spec hc
  have := VG.Proof.MlDsa.X86_64.Sign.rate_small hrate
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true,
    decide_eq_true (show rate < 2 ^ 32 by omega), decide_eq_true (show pos < 2 ^ 32 by omega),
    decide_eq_true (show len < 2 ^ 32 by omega)]
  decide

theorem kabs_ok {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {src : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate pos : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    WP isa (VG.Impl.MlDsa.X86_64.Sign.kabs src len rate pos) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∀ msg, Repr s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) rate msg → pos = msg.length % rate →
        Repr s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) rate (msg ++ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s src) len) := by
  obtain ⟨w0, w1, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨is, _, _, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kabsChk_spec hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.setArgs_ok _ (VG.Proof.MlDsa.X86_64.Sign.kabsOk hc hrate hpos) s) fun s1 ⟨⟨hA, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have cW : Covers [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200), 640⟩] s1.wr := by
    rw [k.2.2]; exact Covers.cons (L.cW w0) (L.cW w1)
  refine absorb_call (VG.Proof.MlDsa.X86_64.Sign.kabsArgs L hD hk hc hrate hpos hA hsp)
    (Covers.append_left (by rw [k.2.1, k.2.2]; exact L.cR is) (Covers.right cW)) cW
    fun s' hrd hwr hcs hf hR _ => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr), k.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr))],
      by rw [hcs .rsp (by decide), hsp], ?_⟩, fun r hr => by rw [hcs r hr, k.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r hr)], ?_⟩
  · rw [← hm, ← hsp]
    have := Frame.below_mono (wr := [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200), 640⟩]) (by simpa using hf)
      (show 16 ≤ D by omega) (by have := L.dsm; omega)
    exact this
  · intro msg hmsg hpos'
    rw [← hm] at hmsg ⊢
    exact hR msg hmsg hpos'

theorem kabs_tr (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true) {src : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate pos : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (VG.Impl.MlDsa.X86_64.Sign.kabs src len rate pos) fun _ _ => True := by
  obtain ⟨w0, w1, i0, i1, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨is, _, _, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kabsChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
    (VG.Proof.MlDsa.X86_64.Sign.kabsOk hc hrate hpos) fun x y x1 y1 R ⟨⟨hAx, _⟩, kx⟩ ⟨⟨hAy, _⟩, ky⟩ => ?_
  have hsx : x1.gpr .rsp = x.gpr .rsp := kx.gpr (by decide)
  have hsy : y1.gpr .rsp = y.gpr .rsp := ky.gpr (by decide)
  have ax := VG.Proof.MlDsa.X86_64.Sign.kabsArgs R.lx hD hk hc hrate hpos hAx hsx
  have ay := VG.Proof.MlDsa.X86_64.Sign.kabsArgs R.ly hD hk hc hrate hpos hAy hsy
  refine ⟨_, _, _, _, absorb_pre ax, absorb_pre ay, ?_,
    Covers.append_left (by rw [kx.2.1, kx.2.2]; exact R.lx.cR is) (Covers.right (by rw [kx.2.2]; exact Covers.cons (R.lx.cW w0) (R.lx.cW w1))),
    by rw [kx.2.2]; exact Covers.cons (R.lx.cW w0) (R.lx.cW w1),
    Covers.append_left (by rw [ky.2.1, ky.2.2]; exact R.ly.cR is) (Covers.right (by rw [ky.2.2]; exact Covers.cons (R.ly.cW w0) (R.ly.cW w1))),
    by rw [ky.2.2]; exact Covers.cons (R.ly.cW w0) (R.ly.cW w1), by rw [hsx, hsy, R.rsp]⟩
  simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    ax.rdi, ax.rsi, ax.rdx, ax.rcx, ax.r8, ax.r9, ay.rdi, ay.rsi, ay.rdx, ay.rcx, ay.r8, ay.r9, R.pa i0, R.pa i1,
    R.pa is, hsx, hsy, R.rsp, and_self]

/-! ## Padding -/

theorem kpadArgs {s s1 : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc 0), .imm rate, .imm pos, .imm suffix, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc 200)] s s1)
    (hsp : s1.gpr .rsp = s.gpr .rsp) :
    PadArgs s1 (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200)) rate pos := by
  obtain ⟨_, _, i0, i1, d01⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨e1, e2, e3, _, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  exact ⟨e1, e2, e3, e5, hrate, hpos, L.disj d01, VG.Proof.MlDsa.X86_64.Sign.k16 L hD i0 hsp, VG.Proof.MlDsa.X86_64.Sign.k16 L hD i1 hsp⟩

theorem kpadOk {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    [Arg.ptr (VG.Impl.MlDsa.X86_64.Sign.sc 0), .imm rate, .imm pos, .imm suffix, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc 200)].all Arg.ok = true := by
  have := VG.Proof.MlDsa.X86_64.Sign.rate_small hrate
  simp only [List.all_cons, List.all_nil, Arg.ok, Bool.and_true,
    decide_eq_true (show rate < 2 ^ 32 by omega), decide_eq_true (show pos < 2 ^ 32 by omega),
    decide_eq_true (show suffix < 2 ^ 32 by omega)]
  decide

theorem b8_ofNat64 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 64 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem kpad_ok {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    WP isa (VG.Impl.MlDsa.X86_64.Sign.kpad rate pos suffix) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∀ msg, Repr s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  obtain ⟨w0, w1, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.setArgs_ok _ (VG.Proof.MlDsa.X86_64.Sign.kpadOk hrate hpos hs) s) fun s1 ⟨⟨hA, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have cW : Covers [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200), 640⟩] s1.wr := by
    rw [k.2.2]; exact Covers.cons (L.cW w0) (L.cW w1)
  have hcx : s1.gpr .rcx = BitVec.ofNat 64 suffix := (VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA).2.2.2.1
  refine pad_call (VG.Proof.MlDsa.X86_64.Sign.kpadArgs L hD hk hrate hpos hA hsp) (Covers.append_left Covers.nil (Covers.right cW)) cW
    fun s' hrd hwr hcs hf hR => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr), k.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr))],
      by rw [hcs .rsp (by decide), hsp], ?_⟩, fun r hr => by rw [hcs r hr, k.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r hr)], ?_⟩
  · rw [← hm, ← hsp]
    exact Frame.below_mono (wr := [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200), 640⟩]) (by simpa using hf)
      (show 16 ≤ D by omega) (by have := L.dsm; omega)
  · intro msg hmsg hpos'
    rw [← hm] at hmsg
    rw [hR msg hmsg hpos', hcx, VG.Proof.MlDsa.X86_64.Sign.b8_ofNat64 hs]

theorem kpad_tr (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true) {rate pos suffix : Nat} (hrate : rate ∈ rates)
    (hpos : pos < rate) (hs : suffix < 256) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (VG.Impl.MlDsa.X86_64.Sign.kpad rate pos suffix) fun _ _ => True := by
  obtain ⟨w0, w1, i0, i1, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (VG.Proof.MlDsa.X86_64.Sign.kpadOk hrate hpos hs) fun x y x1 y1 R ⟨⟨hAx, _⟩, kx⟩ ⟨⟨hAy, _⟩, ky⟩ => ?_
  have hsx : x1.gpr .rsp = x.gpr .rsp := kx.gpr (by decide)
  have hsy : y1.gpr .rsp = y.gpr .rsp := ky.gpr (by decide)
  have ax := VG.Proof.MlDsa.X86_64.Sign.kpadArgs R.lx hD hk hrate hpos hAx hsx
  have ay := VG.Proof.MlDsa.X86_64.Sign.kpadArgs R.ly hD hk hrate hpos hAy hsy
  refine ⟨_, _, _, _, pad_pre ax, pad_pre ay, ?_,
    Covers.append_left Covers.nil (Covers.right (by rw [kx.2.2]; exact Covers.cons (R.lx.cW w0) (R.lx.cW w1))),
    by rw [kx.2.2]; exact Covers.cons (R.lx.cW w0) (R.lx.cW w1),
    Covers.append_left Covers.nil (Covers.right (by rw [ky.2.2]; exact Covers.cons (R.ly.cW w0) (R.ly.cW w1))),
    by rw [ky.2.2]; exact Covers.cons (R.ly.cW w0) (R.ly.cW w1), by rw [hsx, hsy, R.rsp]⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    ax.rdi, ax.rsi, ax.rdx, ax.r8, ay.rdi, ay.rsi, ay.rdx, ay.r8, R.pa i0, R.pa i1, hsx, hsy, R.rsp, and_self]

/-! ## Squeezing -/

theorem ksqzArgs {s s1 : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {dst : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc 200)] s s1)
    (hsp : s1.gpr .rsp = s.gpr .rsp) :
    SqueezeArgs s1 (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s dst) (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200)) rate 0 len := by
  obtain ⟨_, _, i0, i1, d01⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨_, id, _, _, hl, d0, d1⟩ := VG.Proof.MlDsa.X86_64.Sign.ksqzChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn6 hA
  exact ⟨e1, e2, e3, e4, e5, e6, hrate, Nat.zero_le _,
    by omega, L.disj d0, L.disj d01, L.disj d1, VG.Proof.MlDsa.X86_64.Sign.k16 L hD i0 hsp, VG.Proof.MlDsa.X86_64.Sign.k16 L hD id hsp, VG.Proof.MlDsa.X86_64.Sign.k16 L hD i1 hsp⟩

theorem ksqzOk {bs wbs : List (Reg × Nat)} {dst : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.ksqzChk bs wbs dst len = true) (hrate : rate ∈ rates) :
    [Arg.ptr (VG.Impl.MlDsa.X86_64.Sign.sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc 200)].all Arg.ok = true := by
  obtain ⟨_, _, b1, o1, hl, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.ksqzChk_spec hc
  have := VG.Proof.MlDsa.X86_64.Sign.rate_small hrate
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true,
    decide_eq_true (show rate < 2 ^ 32 by omega), decide_eq_true (show len < 2 ^ 32 by omega)]
  decide

theorem ksqz_ok {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {dst : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    WP isa (VG.Impl.MlDsa.X86_64.Sign.ksqz rate dst len) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (dst, len), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s dst) len = squeezeFrom rate (stateAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0))) 0 len := by
  obtain ⟨w0, w1, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨wd, _, _, _, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.ksqzChk_spec hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.setArgs_ok _ (VG.Proof.MlDsa.X86_64.Sign.ksqzOk hc hrate) s) fun s1 ⟨⟨hA, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have cW : Covers [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s dst, len⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200), 640⟩] s1.wr := by
    rw [k.2.2]; exact Covers.cons (L.cW w0) (Covers.cons (L.cW wd) (L.cW w1))
  refine squeeze_call (VG.Proof.MlDsa.X86_64.Sign.ksqzArgs L hD hk hc hrate hA hsp) (Covers.append_left Covers.nil (Covers.right cW)) cW
    fun s' hrd hwr hcs hf ho => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr), k.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr))],
      by rw [hcs .rsp (by decide), hsp], ?_⟩, fun r hr => by rw [hcs r hr, k.gpr (VG.Proof.MlDsa.X86_64.Sign.argRegs_cs r hr)], ?_⟩
  · rw [← hm, ← hsp]
    exact Frame.below_mono (wr := [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s dst, len⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 200), 640⟩]) (by simpa using hf)
      (show 16 ≤ D by omega) (by have := L.dsm; omega)
  · rw [ho, hm]

theorem ksqz_tr (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true) {dst : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len rate : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (VG.Impl.MlDsa.X86_64.Sign.ksqz rate dst len) fun _ _ => True := by
  obtain ⟨w0, w1, i0, i1, _⟩ := VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk
  obtain ⟨wd, id, _, _, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.ksqzChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
    (VG.Proof.MlDsa.X86_64.Sign.ksqzOk hc hrate) fun x y x1 y1 R ⟨⟨hAx, _⟩, kx⟩ ⟨⟨hAy, _⟩, ky⟩ => ?_
  have hsx : x1.gpr .rsp = x.gpr .rsp := kx.gpr (by decide)
  have hsy : y1.gpr .rsp = y.gpr .rsp := ky.gpr (by decide)
  have ax := VG.Proof.MlDsa.X86_64.Sign.ksqzArgs R.lx hD hk hc hrate hAx hsx
  have ay := VG.Proof.MlDsa.X86_64.Sign.ksqzArgs R.ly hD hk hc hrate hAy hsy
  refine ⟨_, _, _, _, squeeze_pre ax, squeeze_pre ay, ?_,
    Covers.append_left Covers.nil (Covers.right (by rw [kx.2.2]; exact Covers.cons (R.lx.cW w0) (Covers.cons (R.lx.cW wd) (R.lx.cW w1)))),
    by rw [kx.2.2]; exact Covers.cons (R.lx.cW w0) (Covers.cons (R.lx.cW wd) (R.lx.cW w1)),
    Covers.append_left Covers.nil (Covers.right (by rw [ky.2.2]; exact Covers.cons (R.ly.cW w0) (Covers.cons (R.ly.cW wd) (R.ly.cW w1)))),
    by rw [ky.2.2]; exact Covers.cons (R.ly.cW w0) (Covers.cons (R.ly.cW wd) (R.ly.cW w1)), by rw [hsx, hsy, R.rsp]⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    ax.rdi, ax.rsi, ax.rdx, ax.rcx, ax.r8, ax.r9, ay.rdi, ay.rsi, ay.rdx, ay.rcx, ay.r8, ay.r9, R.pa i0, R.pa i1,
    R.pa id, hsx, hsy, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Hash`. -/
section

/-!
# ML-DSA signing on x86-64: `H` of pieces of memory

`shakeAt ps out len` zeroes the Keccak state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: `H` of their concatenation (`shake_ok`),
leaking only the addresses (`shake_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : Spec.Sha3.State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d) = SHAKE256(s, 8d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (m : List Byte) (d : Nat) : H m d = squeezeFrom 136 (VG.Proof.MlDsa.X86_64.Sign.padded 136 (BitVec.ofNat 8 0x1f) m) 0 d := by
  rw [VG.Proof.MlDsa.X86_64.Sign.squeezeFrom_zero]; rfl

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.kabsChk bs p.1 p.2 && decide (p.1.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases)

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) : (VG.Proof.MlDsa.X86_64.Sign.pieces s ps).length = VG.Impl.MlDsa.X86_64.Sign.totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [VG.Proof.MlDsa.X86_64.Sign.pieces, List.flatMap_cons, List.length_append, VG.Proof.MlKem.bytesAt_length] at ih ⊢
    rw [ih]; simp [VG.Impl.MlDsa.X86_64.Sign.totLen]

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem pieceChk_keep {p : VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat} (h : VG.Proof.MlDsa.X86_64.Sign.pieceChk (rbs ++ wbs) p = true) :
    VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] p.1 p.2 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pieceChk, VG.Proof.MlDsa.X86_64.Sign.kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hin, _⟩, _⟩, _⟩, s1⟩, s2⟩, hcs⟩ := h
  simp only [VG.Proof.MlDsa.X86_64.Sign.keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

theorem pieces_keep {s s' : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) :
    ∀ {ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)}, (∀ p ∈ ps, VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws p.1 p.2 = true) → VG.Proof.MlDsa.X86_64.Sign.pieces s' ps = VG.Proof.MlDsa.X86_64.Sign.pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [VG.Proof.MlDsa.X86_64.Sign.pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (VG.Proof.MlDsa.X86_64.Sign.pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hcs_trans {s s₁ s₂ : State} (h₁ : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (h₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r) : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem bases_all : ∀ w ∈ [((VG.Impl.MlDsa.X86_64.Sign.sc 0 : VG.Impl.MlDsa.X86_64.Sign.Ptr), 200), ((VG.Impl.MlDsa.X86_64.Sign.sc 200 : VG.Impl.MlDsa.X86_64.Sign.Ptr), 640)], w.1.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by
  decide

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (D : Nat) (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) : Prop :=
  ∀ (s : State) (_ : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (VG.Proof.MlDsa.X86_64.Sign.pieceChk (rbs ++ wbs)) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) rate msg →
    WP isa (VG.Impl.MlDsa.X86_64.Sign.absAll rate ps pos) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ Repr s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0)) rate (msg ++ VG.Proof.MlDsa.X86_64.Sign.pieces s ps)

theorem absAll_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) : ∀ (ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)), VG.Proof.MlDsa.X86_64.Sign.AbsOk D rbs wbs rate ps
  | [] => fun _ _ _ _ _ _ _ hR => WP.block_nil ⟨PostB.refl _ _ _, fun _ _ => rfl, by simpa using hR⟩
  | (p, l) :: ps => by
    intro s L pos msg hps hpos hm hR
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : VG.Proof.MlDsa.X86_64.Sign.kabsChk (rbs ++ wbs) p l = true := by
      simp only [VG.Proof.MlDsa.X86_64.Sign.pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [VG.Impl.MlDsa.X86_64.Sign.absAll]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.kabs_ok L hD hk hkc hrate hpos) fun s₁ ⟨hP₁, hc₁, hR₁⟩ => ?_)
    have L₁ := L.post hP₁ hcs
    have e0 : VG.Proof.MlDsa.X86_64.Sign.pa s₁ (VG.Impl.MlDsa.X86_64.Sign.sc 0) = VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0) := hP₁.pa (by decide)
    have hR₁' := hR₁ msg hR hm
    rw [← e0] at hR₁'
    have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) l).length % rate := by
      rw [List.length_append, VG.Proof.MlKem.bytesAt_length, hm, Nat.mod_add_mod]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.absAll_ok hcs hD hk hrate ps s₁ L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) l) hps.2
      (Nat.mod_lt _ hr0) h3 hR₁') fun s₂ ⟨hP₂, hc₂, hR₂⟩ =>
        ⟨PPostB.trans hP₁ hP₂ VG.Proof.MlDsa.X86_64.Sign.bases_all (fun w hw => hw) (fun w hw => hw), VG.Proof.MlDsa.X86_64.Sign.hcs_trans hc₁ hc₂, ?_⟩
    rw [e0, VG.Proof.MlDsa.X86_64.Sign.pieces_keep L hP₁ fun q hq => VG.Proof.MlDsa.X86_64.Sign.pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
    simpa only [VG.Proof.MlDsa.X86_64.Sign.pieces, List.flatMap_cons, List.append_assoc] using hR₂

/-- The output: `len` bytes to `out`. -/
def shakeChk (bs wbs : List (Reg × Nat)) (ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) (out : VG.Impl.MlDsa.X86_64.Sign.Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.kChk bs wbs && ps.all (VG.Proof.MlDsa.X86_64.Sign.pieceChk bs) && VG.Proof.MlDsa.X86_64.Sign.ksqzChk bs wbs out len

theorem shakeChk_spec {bs wbs : List (Reg × Nat)} {ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} {out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len : Nat}
    (h : VG.Proof.MlDsa.X86_64.Sign.shakeChk bs wbs ps out len = true) :
    VG.Proof.MlDsa.X86_64.Sign.kChk bs wbs = true ∧ ps.all (VG.Proof.MlDsa.X86_64.Sign.pieceChk bs) = true ∧ VG.Proof.MlDsa.X86_64.Sign.ksqzChk bs wbs out len = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.shakeChk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem shake_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (hD : 24 ≤ D) {ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} {out : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    {len : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.shakeChk (rbs ++ wbs) wbs ps out len = true) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) :
    WP isa (shakeAt ps out len) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640), (out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s out) len = H (VG.Proof.MlDsa.X86_64.Sign.pieces s ps) len := by
  obtain ⟨hk, hps, hsq⟩ := VG.Proof.MlDsa.X86_64.Sign.shakeChk_spec hc
  have hocs : out.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by
    simp only [VG.Proof.MlDsa.X86_64.Sign.ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at hsq; exact hsq.1.1.1.1.2
  have hrate : (136 : Nat) ∈ rates := by decide
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.kzero_ok L hk) fun s₁ ⟨hP₁, hc₁, hz⟩ => ?_)
  have L₁ := L.post hP₁ hcs
  have e1 : VG.Proof.MlDsa.X86_64.Sign.pa s₁ (VG.Impl.MlDsa.X86_64.Sign.sc 0) = VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := VG.Proof.MlDsa.X86_64.Sign.pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [VG.Proof.MlDsa.X86_64.Sign.keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : VG.Proof.MlDsa.X86_64.Sign.pieces s₁ ps = VG.Proof.MlDsa.X86_64.Sign.pieces s ps := VG.Proof.MlDsa.X86_64.Sign.pieces_keep L hP₁ hpk
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.absAll_ok hcs hD hk hrate ps s₁ L₁ 0 [] hps (by decide) rfl
    (by rw [e1]; exact VG.Proof.MlDsa.X86_64.Sign.repr_nil hz)) fun s₂ ⟨hP₂, hc₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂ hcs
  have e2 : VG.Proof.MlDsa.X86_64.Sign.pa s₂ (VG.Impl.MlDsa.X86_64.Sign.sc 0) = VG.Proof.MlDsa.X86_64.Sign.pa s₁ (VG.Impl.MlDsa.X86_64.Sign.sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.kpad_ok L₂ hD hk hrate (pos := VG.Impl.MlDsa.X86_64.Sign.totLen ps % 136) (Nat.mod_lt _ (by decide))
    (show 0x1f < 256 by decide)) fun s₃ ⟨hP₃, hc₃, hS₃⟩ => ?_)
  have L₃ := L₂.post hP₃ hcs
  have e3 : VG.Proof.MlDsa.X86_64.Sign.pa s₃ (VG.Impl.MlDsa.X86_64.Sign.sc 0) = VG.Proof.MlDsa.X86_64.Sign.pa s₂ (VG.Impl.MlDsa.X86_64.Sign.sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (VG.Proof.MlDsa.X86_64.Sign.pieces s ps) (by rw [e2]; exact hR₂) (by rw [VG.Proof.MlDsa.X86_64.Sign.pieces_length])
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ksqz_ok L₃ hD hk hsq hrate) fun s₄ ⟨hP₄, hc₄, ho⟩ => ?_
  have eo : VG.Proof.MlDsa.X86_64.Sign.pa s₃ out = VG.Proof.MlDsa.X86_64.Sign.pa s out := by rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  have h12 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₂ [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] :=
    PPostB.trans hP₁ hP₂ VG.Proof.MlDsa.X86_64.Sign.bases_all (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..)
      (fun w hw => hw)
  have h123 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₃ [(VG.Impl.MlDsa.X86_64.Sign.sc 0, 200), (VG.Impl.MlDsa.X86_64.Sign.sc 200, 640)] := PPostB.trans h12 hP₃ VG.Proof.MlDsa.X86_64.Sign.bases_all (fun w hw => hw) (fun w hw => hw)
  have hcs4 : ∀ w ∈ [((VG.Impl.MlDsa.X86_64.Sign.sc 0 : VG.Impl.MlDsa.X86_64.Sign.Ptr), 200), (out, len), ((VG.Impl.MlDsa.X86_64.Sign.sc 200 : VG.Impl.MlDsa.X86_64.Sign.Ptr), 640)], w.1.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    exacts [by decide, hocs, by decide]
  refine ⟨PPostB.trans h123 hP₄ hcs4 (fun w hw => ?_) (fun w hw => ?_),
    VG.Proof.MlDsa.X86_64.Sign.hcs_trans (VG.Proof.MlDsa.X86_64.Sign.hcs_trans (VG.Proof.MlDsa.X86_64.Sign.hcs_trans hc₁ hc₂) hc₃) hc₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h <;> simp [h]
  rw [← eo, ho, e3, hS, VG.Proof.MlDsa.X86_64.Sign.H_eq]

/-! ## Constant time -/

theorem LRel.step (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) {c : Prog isa}
    (htr : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) c fun _ _ => True)
    (hok : ∀ x, VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs x → WP isa c x fun x' => ∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) c (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) :=
  VG.Proof.MlKem.X86_64.RelCT.postDep htr (F := fun x x' => ∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  VG.Proof.MlKem.X86_64.RelCT.postDep (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr fun _ hi => absurd hi List.not_mem_nil)
    (F := fun x x' => x' = x) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem absAll_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (hD : 24 ≤ D) (hk : VG.Proof.MlDsa.X86_64.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) :
    ∀ (ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) (pos : Nat), ps.all (VG.Proof.MlDsa.X86_64.Sign.pieceChk (rbs ++ wbs)) = true → pos < rate →
      RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (VG.Impl.MlDsa.X86_64.Sign.absAll rate ps pos) (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs)
  | [], _, _, _ => VG.Proof.MlDsa.X86_64.Sign.nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : VG.Proof.MlDsa.X86_64.Sign.kabsChk (rbs ++ wbs) p l = true := by
      simp only [VG.Proof.MlDsa.X86_64.Sign.pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [VG.Impl.MlDsa.X86_64.Sign.absAll]
    exact RelCT.seq (LRel.step hcs (VG.Proof.MlDsa.X86_64.Sign.kabs_tr hD hk hkc hrate hpos)
      fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Sign.kabs_ok Lx hD hk hkc hrate hpos) fun _ h => ⟨_, h.1⟩)
      (VG.Proof.MlDsa.X86_64.Sign.absAll_tr hcs hD hk hrate ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem shake_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (hD : 24 ≤ D) {ps : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} {out : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    {len : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.shakeChk (rbs ++ wbs) wbs ps out len = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (shakeAt ps out len) (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) := by
  obtain ⟨hk, hps, hsq⟩ := VG.Proof.MlDsa.X86_64.Sign.shakeChk_spec hc
  have hrate : (136 : Nat) ∈ rates := by decide
  have i0 : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Sign.sc 0) 200 = true := (VG.Proof.MlDsa.X86_64.Sign.kChk_spec hk).2.2.1
  refine RelCT.seq (LRel.step hcs (VG.Proof.MlDsa.X86_64.Sign.kzero_tr fun x y h => h.eq i0)
    fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Sign.kzero_ok Lx hk) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.absAll_tr hcs hD hk hrate ps 0 hps (by decide)) (RelCT.seq (LRel.step hcs
      (VG.Proof.MlDsa.X86_64.Sign.kpad_tr hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
      fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Sign.kpad_ok Lx hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
        fun _ h => ⟨_, h.1⟩)
      (LRel.step hcs (VG.Proof.MlDsa.X86_64.Sign.ksqz_tr hD hk hsq hrate) fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Sign.ksqz_ok Lx hD hk hsq hrate) fun _ h => ⟨_, h.1⟩)))

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top`. -/
section

/-!
# ML-DSA signing on x86-64: the function's contract, layout, entry and exit

The contract the proof is written against (`signK`, which the shared contract
implies), the layout of the function's buffers (`sk`, `mu`, `rnd` read, in
`rbp`, `r12`, `r13`; `scratch` and `sig` written, in `rbx` and `r14`), what
holds of the state throughout (`Top`: the permissions and the stack pointer of
entry, the pointers in their registers, the caller's callee-saved registers
saved in `scratch`, and the return address), the saves (`pro_ok`), the return
(`topEpi_ok`), branches on `r15` (`ifOkElse_ok`, `ifOkElse_tr`) and sequences
of pieces indexed by a number (`seqR_ok`, `seqR_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_sign(sk = rdi, mu = rsi, rnd = rdx, sig = rcx, scratch = r8) -> eax`, with `D` bytes
of stack, and the leakage `signLeakT`. -/
def signK (p : Params) (D : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, p.skLen⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 32⟩] ∧
    s.wr = [⟨s.gpr .rcx, p.sigLen⟩, ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∧
    (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨s.gpr .rdi, p.skLen⟩ ∧ (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (VG.Proof.MlDsa.X86_64.Sign.retR s).Disjoint ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdi, p.skLen⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∧
    (s.gpr .rdi).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + VG.Proof.MlDsa.X86_64.Sign.scrLen p ≤ 2 ^ 64 ∧
    D ≤ (s.gpr .rsp).toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .rdi) p.skLen) (bytesAt s.mem (s.gpr .rsi) 64)
      (bytesAt s.mem (s.gpr .rdx) 32)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rcx) p.sigLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    signLeakT p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) 64)
        (bytesAt s₁.mem (s₁.gpr .rdx) 32) =
      signLeakT p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) 64)
        (bytesAt s₂.mem (s₂.gpr .rdx) 32)

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.rbp, p.skLen), (.r12, 64), (.r13, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.rbx, VG.Proof.MlDsa.X86_64.Sign.scrLen p), (.r14, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := VG.Proof.MlDsa.X86_64.Sign.sgR p ++ VG.Proof.MlDsa.X86_64.Sign.sgW p

/-- The pointers the function keeps, and the registers they arrive in. -/
abbrev sgM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx), (.r14, .rcx)]

theorem sgB_bases (p : Params) : ∀ b ∈ VG.Proof.MlDsa.X86_64.Sign.sgB p, b.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by
  intro b hb; simp only [VG.Proof.MlDsa.X86_64.Sign.sgB, VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
theorem sgM_bases : ∀ m ∈ VG.Proof.MlDsa.X86_64.Sign.sgM, m.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by decide

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  regs : ∀ m ∈ VG.Proof.MlDsa.X86_64.Sign.sgM, s.gpr m.1 = σ.gpr m.2
  saved : ∀ k < 6, s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc (VG.Impl.MlDsa.X86_64.Sign.oSV + 8 * k))) 64 = σ.gpr (VG.Proof.MlDsa.X86_64.Sign.savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64

theorem pairwise_sym {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with e | ha'
    · rcases List.mem_cons.mp hb with e' | hb'
      · exact absurd (e.trans e'.symm) hne
      · rw [e]; exact h.1 _ hb'
    · rcases List.mem_cons.mp hb with e' | hb'
      · rw [e']; exact hs _ _ (h.1 _ ha')
      · exact VG.Proof.MlDsa.X86_64.Sign.pairwise_sym hs h.2 ha' hb' hne

section
variable {p : Params} {D : Nat} {σ : State} (hp : (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ)
include hp

theorem sgLay (hD : D < 2 ^ 32) (hsz : VG.Proof.MlDsa.X86_64.Sign.scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.Top σ s) : VG.Proof.MlDsa.X86_64.Sign.Lay D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rcx := h.regs (.r14, .rcx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, by rw [h.rsp]; exact hsp, hD⟩
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlDsa.X86_64.Sign.wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e1, e2, e3, e4, e5]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5, h.rsp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [n1, n2, n3, n5, n4]
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [mem ⟨σ.gpr .rdi, p.skLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 64⟩ (by rw [hrd]; simp),
      mem ⟨σ.gpr .rdx, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ (by rw [hwr]; simp),
      mem ⟨σ.gpr .rcx, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e1, e5]
    exacts [memw ⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ (by rw [hwr]; simp), memw ⟨σ.gpr .rcx, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlDsa.X86_64.Sign.retR, e1, e2, e3, e4, e5, h.rsp]
    exacts [r1, r2, r3, r5, r4]

end

/-- The saved registers and the return address are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => VG.Proof.MlDsa.X86_64.Sign.keepB bs ws (VG.Impl.MlDsa.X86_64.Sign.sc (VG.Impl.MlDsa.X86_64.Sign.oSV + 8 * k)) 8) && ws.all fun w => VG.Proof.MlDsa.X86_64.Sign.inB bs w.1 w.2

theorem Top.step {D : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : VG.Proof.MlDsa.X86_64.Sign.Top σ s)
    (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {ws : List (VG.Impl.MlDsa.X86_64.Sign.Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws)
    (hc : VG.Proof.MlDsa.X86_64.Sign.topChk (rbs ++ wbs) ws = true) : VG.Proof.MlDsa.X86_64.Sign.Top σ s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp,
    fun m hm => (hP.bs _ (VG.Proof.MlDsa.X86_64.Sign.sgM_bases m hm)).trans (h.regs m hm), fun k hk => ?_, ?_⟩
  · rw [L.keepW hP (hc.1 k hk)]; exact h.saved k hk
  · have := L.keepRet hP hc.2
    rw [h.rsp] at this
    rw [this, h.ret]

/-! ## Saving the registers -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (VG.Proof.MlDsa.X86_64.Sign.off_disj (base := a) h (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (VG.Proof.MlDsa.X86_64.Sign.off_disj (base := a) h (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `topPro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (VG.Impl.MlDsa.X86_64.Sign.oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [VG.Impl.MlDsa.X86_64.Sign.oSV, Nat.reduceMul, Nat.reduceAdd, VG.Proof.MlDsa.X86_64.Sign.readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_eq : VG.Impl.MlDsa.X86_64.Sign.pro = [.store (VG.Impl.MlKem.X86_64.at_ .r8 840) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .r8 848) .rbp,
    .store (VG.Impl.MlKem.X86_64.at_ .r8 856) .r12, .store (VG.Impl.MlKem.X86_64.at_ .r8 864) .r13,
    .store (VG.Impl.MlKem.X86_64.at_ .r8 872) .r14, .store (VG.Impl.MlKem.X86_64.at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov .r14 (.reg .rcx),
    .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {p : Params} {D : Nat} {σ : State} (hp : (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ) (hsz : VG.Proof.MlDsa.X86_64.Sign.scrLen p < 2 ^ 32) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sign.pro) σ fun s => VG.Proof.MlDsa.X86_64.Sign.Top σ s ∧ s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 ∧
      Frame [⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩] σ.mem s.mem ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, _, r5, _, _, _, _, _, _, _, _, _, _, _⟩ := hp'
  have hS : ⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 888 → (⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => VG.Proof.MlDsa.X86_64.Sign.contains_offset' (by have : 888 ≤ VG.Proof.MlDsa.X86_64.Sign.scrLen p := by unfold VG.Proof.MlDsa.X86_64.Sign.scrLen scratchWords; omega
                                                                omega) (by omega)
  have w : ∀ o, o + 8 ≤ 888 → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [VG.Proof.MlDsa.X86_64.Sign.pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r14 = σ.gpr .rcx ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 :=
    hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fun m hm => ?_, fun j hj => ?_, hret⟩, hret, hf, h15⟩
  · simp only [VG.Proof.MlDsa.X86_64.Sign.sgM, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, h12, h13, h14]
  · simp only [VG.Proof.MlDsa.X86_64.Sign.pa, hbx, hm]
    exact VG.Proof.MlDsa.X86_64.Sign.stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (VG.Proof.MlDsa.X86_64.Sign.savedReg j)) j hj

/-! ## The return -/

theorem topEpi_eq : VG.Impl.MlDsa.X86_64.Sign.topEpi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 880)),
    .mov .r14 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 872)), .mov .r13 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 864)),
    .mov .r12 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 856)), .mov .rbp (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 848)),
    .mov .rbx (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 840))] := rfl

theorem topEpi_ok {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sign.Top σ s)
    (hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc (VG.Impl.MlDsa.X86_64.Sign.oSV + 8 * k))) 8) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sign.topEpi) s fun s' => (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32 ∧
      gprPreserved σ s' ∧ s'.mem = s.mem := by
  have e : ∀ k < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (VG.Proof.MlDsa.X86_64.Sign.savedReg k) :=
    fun k hk => h.saved k hk
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 8 := hin
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show VG.Proof.MlDsa.X86_64.Sign.savedReg 0 = .rbx from rfl] at e0; rw [show VG.Proof.MlDsa.X86_64.Sign.savedReg 1 = .rbp from rfl] at e1
  rw [show VG.Proof.MlDsa.X86_64.Sign.savedReg 2 = .r12 from rfl] at e2; rw [show VG.Proof.MlDsa.X86_64.Sign.savedReg 3 = .r13 from rfl] at e3
  rw [show VG.Proof.MlDsa.X86_64.Sign.savedReg 4 = .r14 from rfl] at e4; rw [show VG.Proof.MlDsa.X86_64.Sign.savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [VG.Proof.MlDsa.X86_64.Sign.topEpi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩, hm⟩
  · rw [hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## Branches on `r15` -/

/-- A block that writes only `r15`'s flags keeps `PostB`. -/
theorem test15_ok (s : State) (D : Nat) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₁ [] ∧
      (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) := by
  refine WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun s₁ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
        simp only [VG.Proof.MlDsa.X86_64.Sign.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
        by rw [hm]; exact Frame.refl _ _⟩,
      fun r hr => by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact h15 | exact k.gpr (by decide), hm, by rw [hz, BitVec.and_self]⟩

theorem ifOkElse_ok {D : Nat} {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₁ [] → (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem →
      (s.gpr .r15).setWidth 32 ≠ 0 → WP isa t s₁ Q)
    (he : ∀ s₁, VG.Proof.MlDsa.X86_64.Sign.PPostB D s s₁ [] → (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem →
      (s.gpr .r15).setWidth 32 = 0 → WP isa e s₁ Q) : WP isa (ifOkElse t e) s Q := by
  unfold ifOkElse
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.test15_ok s D) fun s₁ ⟨hP, hcs, hm, hz⟩ => ?_)
  refine WP.ite (M := isa) (!((s.gpr .r15).setWidth 32 == 0))
    (show s₁.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP hcs hm (by simpa using hb)
  · exact he s₁ hP hcs hm (by simpa using hb)

theorem ifOkElse_tr {D : Nat} {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (VG.Proof.MlDsa.X86_64.Sign.PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧
      x.mem = x₀.mem) ∧ (VG.Proof.MlDsa.X86_64.Sign.PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧
      (x₀.gpr .r15).setWidth 32 ≠ 0) t Q)
    (he : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (VG.Proof.MlDsa.X86_64.Sign.PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧
      x.mem = x₀.mem) ∧ (VG.Proof.MlDsa.X86_64.Sign.PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧
      (x₀.gpr .r15).setWidth 32 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q := by
  unfold ifOkElse
  refine RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => (VG.Proof.MlDsa.X86_64.Sign.PPostB D x x₁ [] ∧ (∀ r ∈ calleeSaved, x₁.gpr r = x.gpr r) ∧ x₁.mem = x.mem) ∧
      x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨WP.mono (VG.Proof.MlDsa.X86_64.Sign.test15_ok x D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
      WP.mono (VG.Proof.MlDsa.X86_64.Sign.test15_ok y D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
    (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      ((VG.Proof.MlDsa.X86_64.Sign.PPostB D x₀ x₁ [] ∧ (∀ r ∈ calleeSaved, x₁.gpr r = x₀.gpr r) ∧ x₁.mem = x₀.mem) ∧
        x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      ((VG.Proof.MlDsa.X86_64.Sign.PPostB D y₀ y₁ [] ∧ (∀ r ∈ calleeSaved, y₁.gpr r = y₀.gpr r) ∧ y₁.mem = y₀.mem) ∧
        y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, hq x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono he (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (VG.Impl.MlDsa.X86_64.Sign.seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [VG.Impl.MlDsa.X86_64.Sign.seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact VG.Proof.MlDsa.X86_64.Sign.seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (VG.Impl.MlDsa.X86_64.Sign.seqR f a n) (R (a + n))
  | 0, _, _ => VG.Proof.MlDsa.X86_64.Sign.nil_tr
  | n + 1, a, h => by
    rw [VG.Impl.MlDsa.X86_64.Sign.seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (VG.Proof.MlDsa.X86_64.Sign.seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks`. -/
section

/-!
# ML-DSA signing on x86-64: the blocks between the calls

What the function's own instructions do, in its layout: copies (`copy_okB`),
stores of a byte or of 8 bytes (`setB_okB`, `setQ_okB`), the AND of a result
into `r15` (`and15_ok`), the counters `κ` and `CNT` and the bytes of `κ + r`
for `ExpandMask` (`kapAdd_ok`, `cntDec_ok`, `setKappa_ok`), the sum of the 1s
of the hint (`onesAdd_ok`) and its check (`onesOk_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Spec.MlDsa (integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- What a block that writes only registers other than the callee-saved
ones, and memory within `W`, leaves. -/
theorem postB_of_keep {D : Nat} {rs : List Reg} {s s' : State} (k : Keep rs s s')
    (hcs : ∀ r ∈ calleeSaved, r ∉ rs) {W : List Region} (hf : Frame W s.mem s'.mem) :
    VG.Proof.MlDsa.X86_64.Sign.PostB D s s' W ∧ ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r :=
  ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (hcs r (VG.Proof.MlDsa.X86_64.Sign.bases_cs r hr)), k.gpr (hcs .rsp (by decide)),
    hf.mono fun r hr => List.mem_append_left _ hr⟩, fun r hr => k.gpr (hcs r hr)⟩

/-! ## Copies, 8 bytes at a time -/

open VG.Proof.MlKem.X86_64 (pa sx_ofNat sw_ofNat off_add contains_offset' wp_countdown)

/-- `l` bytes from byte `off` of a range. -/
theorem inRegions_off {rs : List Region} {a : Addr} {n off l : Nat} (h : InRegions rs a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8)
    (h1 : InRegions s.wr (s.gpr .rdi) 8) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rsi 0)), .store (VG.Impl.MlKem.X86_64.at_ .rdi 0) .rax,
      .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rsi) 64) ∧ s'.gpr .rdi = s.gpr .rdi + 8 ∧
        s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1]

/-- Byte `j` of a write of 8 bytes at `p + 8k`, of a read at `q + 8k`. -/
theorem copy_byte (m m' : Mem) (p q : Addr) {k j : Nat} (hj : j < 2 ^ 62) (hk : 8 * k + 8 < 2 ^ 62) :
    (m.writeW (p + BitVec.ofNat 64 (8 * k)) (m'.readW (q + BitVec.ofNat 64 (8 * k)) 64)) (p + BitVec.ofNat 64 j) =
      if 8 * k ≤ j ∧ j < 8 * k + 8 then m' (q + BitVec.ofNat 64 j) else m (p + BitVec.ofNat 64 j) := by
  split
  · rename_i h
    have e := writeW_byte m (p + BitVec.ofNat 64 (8 * k)) (m'.readW (q + BitVec.ofNat 64 (8 * k)) 64)
      (k := j - 8 * k) (by omega) (by decide)
    rw [off_add, Nat.add_sub_cancel' h.1, byte_readW _ _ (by omega), off_add, Nat.add_sub_cancel' h.1] at e
    exact e
  · rename_i h
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' _ (by omega) (by omega)]
    split <;> omega

theorem copy_ok (dst src : Ptr) (n : Nat) (hn0 : 0 < n ∧ n % 8 = 0) (hn : n < 2 ^ 31) (hd : dst.2 < 2 ^ 31)
    (hs : src.2 < 2 ^ 31) (hsr : src.1 ≠ .rdi) (s : State)
    (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s src) n) (hwr : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s dst) n)
    (hdj : Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s src, n⟩ ⟨VG.Proof.MlDsa.X86_64.Sign.pa s dst, n⟩) :
    WP isa (copy dst src n) s fun s' =>
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s dst) n = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s src) n ∧ Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s dst, n⟩] s.mem s'.mem ∧
        Keep [.rax, .rcx, .rsi, .rdi] s s' := by
  unfold copy lea
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Sign.pa s dst ∧
      s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Sign.pa s src ∧ s'.gpr .rcx = BitVec.ofNat 64 (n / 8))
    (by xrun [VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hd, VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hs, hsr, List.cons_append, List.nil_append,
      VG.Proof.MlDsa.X86_64.Sign.sw_ofNat (show n / 8 < 2 ^ 32 by omega)])
    (by rfl)) fun s1 ⟨⟨hm1, hdi1, hsi1, hcx1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n / 8) (by omega) (by omega) (fun k s' =>
      s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Sign.pa s dst + BitVec.ofNat 64 (8 * k) ∧ s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Sign.pa s src + BitVec.ofNat 64 (8 * k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < 8 * k, s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s dst + BitVec.ofNat 64 j) = s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s src + BitVec.ofNat 64 j)) ∧
      Keep [.rax, .rcx, .rsi, .rdi] s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hdi1]; simp, by rw [hsi1]; simp, k1.2.1, k1.2.2, by rw [hm1]; exact Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), k1.mono (by decide)⟩ hcx1)
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.copyBody_ok s' (by rw [hrd', hwr', hsi]; exact VG.Proof.MlDsa.X86_64.Sign.inRegions_off hrd (by omega) (by omega))
      (by rw [hwr', hdi]; exact VG.Proof.MlDsa.X86_64.Sign.inRegions_off hwr (by omega) (by omega))) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hdi', hdi, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl,
          by rw [hsi', hsi, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl,
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (VG.Proof.MlDsa.X86_64.Sign.contains_offset' (by omega) (by omega))
    · rw [hm, hdi, hsi, VG.Proof.MlDsa.X86_64.Sign.copy_byte _ _ _ _ (by omega) (by omega)]
      split
      · rename_i h
        exact hf.bytes (R := ⟨VG.Proof.MlDsa.X86_64.Sign.pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) (show j < n by omega)
      · exact hc j (by omega)
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (by have := List.mem_range.mp hi; omega)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
include L

/-! ## Copies -/

/-- What a copy of `n` bytes from `src` to `dst` needs of the layout. -/
def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs dst n && VG.Proof.MlDsa.X86_64.Sign.inB bs src n && VG.Proof.MlDsa.X86_64.Sign.sepB bs src n dst n && decide (0 < n ∧ n % 8 = 0) && decide (n < 2 ^ 31) &&
    decide (dst.2 < 2 ^ 31) && decide (src.2 < 2 ^ 31) && decide (src.1 ≠ .rdi)

omit L in
theorem copyChk_spec {bs wbs : List (Reg × Nat)} {dst src : Ptr} {n : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.copyChk bs wbs dst src n = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs dst n = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs src n = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs src n dst n = true ∧ (0 < n ∧ n % 8 = 0) ∧ n < 2 ^ 31 ∧
      dst.2 < 2 ^ 31 ∧ src.2 < 2 ^ 31 ∧ src.1 ≠ .rdi := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem copy_okB {dst src : Ptr} {n : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(dst, n)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s dst) n = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s src) n := by
  obtain ⟨w, i, d, h0, hn, od, os, sr⟩ := VG.Proof.MlDsa.X86_64.Sign.copyChk_spec hc
  exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_ok dst src n h0 hn od os sr s (L.iR i) (L.iW w) (L.disj d))
    fun s' ⟨hb, hf, k⟩ => ⟨(VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).1, (VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).2, hb⟩

/-! ## Stores -/

theorem setB_okB {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 256) (hc : VG.Proof.MlDsa.X86_64.Sign.inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(p, 1)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s p) (BitVec.ofNat 8 v) := by
  refine WP.mono (VG.Proof.MlKem.X86_64.setB_ok p v hr hv s (L.iW hc)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, 1⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).1, (VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).2, hm⟩

omit L in
theorem setQ_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 2 ^ 31) (s : State)
    (hw : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s p) 8) :
    WP isa (.block (setQ p v)) s fun s' => s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s p) (BitVec.ofNat 64 v) ∧ Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  unfold setQ
  xrun [hw, hr, VG.Proof.MlDsa.X86_64.Sign.sw_ofNat (show v < 2 ^ 32 by omega)]

theorem setQ_okB {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 2 ^ 31) (hc : VG.Proof.MlDsa.X86_64.Sign.inB wbs p 8 = true) :
    WP isa (.block (setQ p v)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(p, 8)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s p) (BitVec.ofNat 64 v) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setQ_ok p v hr hv s (L.iW hc)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).1, (VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).2, hm⟩

end

/-! ## Results in `r15` -/

/-- A result (1 or 0) as a 64-bit register. -/
abbrev bit (b : Prop) [Decidable b] : BitVec 64 := if b then 1 else 0

theorem and15_ok (s : State) :
    WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s fun s' =>
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
        s'.mem = s.mem ∧ Keep [.r15] s s' := by
  refine WP.mono (WP.keep [.r15] (Q := fun s' =>
    s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem)
    (by xrun) (by decide)) fun s' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x y : BitVec 64} (hx : x = VG.Proof.MlDsa.X86_64.Sign.bit a)
    (hy : y.setWidth 32 = if b then 1 else 0) :
    BitVec.setWidth 64 (x.setWidth 32 &&& y.setWidth 32) = VG.Proof.MlDsa.X86_64.Sign.bit (a ∧ b) := by
  subst hx
  rw [hy]
  by_cases ha : a <;> by_cases hb : b <;> simp [VG.Proof.MlDsa.X86_64.Sign.bit, ha, hb]

theorem bit_setWidth {a : Prop} [Decidable a] : (VG.Proof.MlDsa.X86_64.Sign.bit a).setWidth 32 = if a then 1 else 0 := by
  by_cases ha : a <;> simp [VG.Proof.MlDsa.X86_64.Sign.bit, ha]

/-- A block that writes `r15` alone, and flags, leaves `PostB` but for `r15`. -/
theorem postB15 {D : Nat} {s s' : State} (k : Keep [.r15] s s') (hm : s'.mem = s.mem) (W : List Region) :
    VG.Proof.MlDsa.X86_64.Sign.PostB D s s' W ∧ ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r :=
  ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
      simp only [VG.Proof.MlDsa.X86_64.Sign.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
      by rw [hm]; exact Frame.refl _ _⟩,
    fun r _ hne => k.gpr (by simpa using hne)⟩

/-! ## Counters -/

theorem ofNat64_add {a b : Nat} : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

/-- `[p] ← [p] + v`, through `rax`. -/
theorem addQ_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 2 ^ 31) (s : State) (hw : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s p) 8)
    (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s p) 8) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ p.1 p.2)), .alu .add .rax (.imm (BitVec.ofNat 32 v)),
      .store (VG.Impl.MlKem.X86_64.at_ p.1 p.2) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s p) (s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s p) 64 + BitVec.ofNat 64 v) ∧ Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  xrun [hw, hrd, hr, VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hv]

/-- `[p] ← [p] - 1`, through `rax`, and ZF set when it is 0. -/
theorem decQ_ok (p : Ptr) (hr : p.1 ≠ .rax) (s : State) (hw : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s p) 8)
    (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s p) 8) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ p.1 p.2)), .alu .sub .rax (.imm 1),
      .store (VG.Impl.MlKem.X86_64.at_ p.1 p.2) .rax]) s fun s' =>
      (s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s p) (s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s p) 64 - 1) ∧
        s'.zf = some (s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s p) 64 - 1 == 0)) ∧ Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  xrun [hw, hrd, hr]

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr`. -/
section

/-!
# ML-DSA signing on x86-64: blocks that leak only their pointers

A block of moves, arithmetic and stores whose memory operands are `[b + disp]`
with `b` among registers `rs` that it never writes leaks the same from two
states that agree on `rs` (`block_tr`). Unlike the taint analysis, which
evaluates the code, this holds for code with immediates and displacements that
are variables, such as the pieces of the function indexed by a polynomial or
an entry of `Â`; `blockOk` is checked by `rfl`.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64

/-- The base register of a memory operand without an index. -/
def mBase (m : MemOp) : Option (List Reg) := if m.index = none then some [m.base] else none

/-- The registers the address of an operand uses. -/
def srcBase : Src → Option (List Reg)
  | .mem m => VG.Proof.MlDsa.X86_64.Sign.mBase m
  | _ => some []

/-- The registers the address an instruction accesses uses, for the moves,
arithmetic, shifts and stores; `none` for any other instruction. -/
def memBase : Instr → Option (List Reg)
  | .mov _ src => VG.Proof.MlDsa.X86_64.Sign.srcBase src
  | .store m _ => VG.Proof.MlDsa.X86_64.Sign.mBase m
  | .alu _ _ src => VG.Proof.MlDsa.X86_64.Sign.srcBase src
  | .mov32 _ src => VG.Proof.MlDsa.X86_64.Sign.srcBase src
  | .store32 m _ => VG.Proof.MlDsa.X86_64.Sign.mBase m
  | .alu32 _ _ src => VG.Proof.MlDsa.X86_64.Sign.srcBase src
  | .shift .. => some []
  | .shift32 .. => some []
  | .movzx8 _ m => VG.Proof.MlDsa.X86_64.Sign.mBase m
  | .store8 m _ => VG.Proof.MlDsa.X86_64.Sign.mBase m
  | _ => none

/-- Every instruction's addresses use only `rs`, which none writes. -/
def blockOk (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (match VG.Proof.MlDsa.X86_64.Sign.memBase i with | some l => l.all (rs.contains ·) | none => false) &&
    rs.all fun r => !Taint.clobbers i r

theorem ea_agree {rs : List Reg} {m : MemOp} {l : List Reg} (h : VG.Proof.MlDsa.X86_64.Sign.mBase m = some l) (hl : ∀ r ∈ l, r ∈ rs)
    {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) : s.ea m = s'.ea m := by
  unfold VG.Proof.MlDsa.X86_64.Sign.mBase at h
  split at h
  · rename_i hi
    cases h
    simp only [State.ea, hi, hs m.base (hl _ (List.mem_singleton_self _))]
  · cases h

theorem srcAddrs_agree {rs : List Reg} {src : Src} {l : List Reg} (h : VG.Proof.MlDsa.X86_64.Sign.srcBase src = some l)
    (hl : ∀ r ∈ l, r ∈ rs) {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    srcAddrs s src = srcAddrs s' src := by
  cases src with
  | mem m => simp only [srcAddrs, VG.Proof.MlDsa.X86_64.Sign.ea_agree h hl hs]
  | _ => rfl

theorem addrs_agree {rs : List Reg} {i : Instr} {l : List Reg} (h : VG.Proof.MlDsa.X86_64.Sign.memBase i = some l) (hl : ∀ r ∈ l, r ∈ rs)
    {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) : isa.addrs i s = isa.addrs i s' := by
  cases i <;> simp only [VG.Proof.MlDsa.X86_64.Sign.memBase, reduceCtorEq] at h
  all_goals first
    | exact VG.Proof.MlDsa.X86_64.Sign.srcAddrs_agree h hl hs
    | (show [State.ea _ _] = [State.ea _ _]; rw [VG.Proof.MlDsa.X86_64.Sign.ea_agree h hl hs])
    | rfl

theorem blockOk_cons {rs : List Reg} {i : Instr} {is : List Instr} (h : VG.Proof.MlDsa.X86_64.Sign.blockOk rs (i :: is) = true) :
    (∃ l, VG.Proof.MlDsa.X86_64.Sign.memBase i = some l ∧ ∀ r ∈ l, r ∈ rs) ∧ (∀ r ∈ rs, Taint.clobbers i r = false) ∧
      VG.Proof.MlDsa.X86_64.Sign.blockOk rs is = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.blockOk, List.all_cons, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hm, hc⟩, hr⟩ := h
  refine ⟨?_, hc, by simpa [VG.Proof.MlDsa.X86_64.Sign.blockOk] using hr⟩
  revert hm
  cases VG.Proof.MlDsa.X86_64.Sign.memBase i with
  | some l => intro hm; simp only [List.all_eq_true, List.contains_iff_mem] at hm; exact ⟨l, rfl, hm⟩
  | none => intro hm; cases hm

theorem execBlock_tr {rs : List Reg} : ∀ {is : List Instr}, VG.Proof.MlDsa.X86_64.Sign.blockOk rs is = true →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, _, _, _, _, hs, e₁, e₂ => by
    obtain ⟨⟨l, hm, hl⟩, hc, h'⟩ := VG.Proof.MlDsa.X86_64.Sign.blockOk_cons h
    simp only [execBlock] at e₁ e₂
    split at e₁
    · cases e₁
    · rename_i u₁ x₁
      split at e₂
      · cases e₂
      · rename_i u₂ x₂
        obtain ⟨⟨a₁, b₁⟩, f₁, g₁⟩ := Option.map_eq_some_iff.mp e₁
        obtain ⟨⟨a₂, b₂⟩, f₂, g₂⟩ := Option.map_eq_some_iff.mp e₂
        simp only [Prod.mk.injEq] at g₁ g₂
        rw [← g₁.2, ← g₂.2, show addrs i s₁ = addrs i s₂ from VG.Proof.MlDsa.X86_64.Sign.addrs_agree hm hl hs,
          VG.Proof.MlDsa.X86_64.Sign.execBlock_tr h' (fun r hr => by rw [exec_gpr (hc r hr) x₁, exec_gpr (hc r hr) x₂, hs r hr]) f₁ f₂]

/-- A block that `blockOk` accepts leaks the same from states that agree on `rs`. -/
theorem block_tr {rs : List Reg} {is : List Instr} (h : VG.Proof.MlDsa.X86_64.Sign.blockOk rs is = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨VG.Proof.MlDsa.X86_64.Sign.execBlock_tr h (hP _ _ hp) e₁ e₂, trivial⟩

end VG.Proof.MlDsa.X86_64.Sign

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Impl.MlKem.X86_64 (at_)

/-! ## Copies -/

theorem execBlock_snoc : ∀ {is : List Instr} {i : Instr} {s s' : State} {t : List Leak},
    execBlock isa (is ++ [i]) s = some (s', t) →
      ∃ s₀ t₀, execBlock isa is s = some (s₀, t₀) ∧ isa.exec i s₀ = some s'
  | [], i, s, s', t, h => by
    simp only [List.nil_append, execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨s, [], rfl, h.1 ▸ e⟩
  | j :: is, i, s, s', t, h => by
    simp only [List.cons_append, execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨s₀, t₀, h0, h1⟩ := VG.Proof.MlDsa.X86_64.Sign.execBlock_snoc h2
      refine ⟨s₀, (isa.addrs j s).map Leak.addr ++ t₀, ?_, heq.1 ▸ h1⟩
      simp only [execBlock, e, h0, Option.map_some]

/-- The body of a copy's loop. -/
abbrev cbody : List Instr := [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax, .alu .add .rdi (.imm 8),
  .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]

theorem cbody_rcx {s s' : State} {t : List Leak} (h : execBlock isa VG.Proof.MlDsa.X86_64.Sign.cbody s = some (s', t)) :
    s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨s₀, t₀, h0, h1⟩ := VG.Proof.MlDsa.X86_64.Sign.execBlock_snoc (is := [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax,
    .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8)]) h
  have e := execBlock_gpr (r := .rcx) (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) h0
  simp only [isa, exec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at h1
  subst h1
  constructor <;> simp [State.setReg, arithFlags, State.setFlags, e]

theorem cbody_taint : ((taint.check (Taint.ofRegs [.rdi, .rsi, .rcx]) (.block VG.Proof.MlDsa.X86_64.Sign.cbody)
    (Taint.hintOf taint (Taint.ofRegs [.rdi, .rsi, .rcx]) (.block VG.Proof.MlDsa.X86_64.Sign.cbody))).map fun τ' =>
      (RegSet.ofList [Reg.rdi, .rsi, .rcx]).subset τ'.regs) = some true := by decide

/-- Two runs of a copy from the same addresses leak the same. -/
theorem copy_tr {dst src : Ptr} {n : Nat} (h0 : 0 < n ∧ n % 8 = 0) (hn : n < 2 ^ 31) (hd : dst.2 < 2 ^ 31)
    (hs : src.2 < 2 ^ 31) (hsr : src.1 ≠ .rdi) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr src.1 = y.gpr src.1) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  let I : Nat → State → State → Prop := fun m x y =>
    (∀ r ∈ [Reg.rdi, .rsi, .rcx], x.gpr r = y.gpr r) ∧ (x.gpr .rcx).toNat = m + 1
  have pro : ∀ s, WP isa (.block (lea .rdi dst ++ lea .rsi src ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 (n / 8)))])) s
      fun s' => s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Sign.pa s dst ∧ s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Sign.pa s src ∧ s'.gpr .rcx = BitVec.ofNat 64 (n / 8) := fun s => by
    unfold lea
    xrun [VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hd, VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hs, hsr, List.cons_append, List.nil_append,
      VG.Proof.MlDsa.X86_64.Sign.sw_ofNat (show n / 8 < 2 ^ 32 by omega)]
  unfold copy
  refine RelCT.seq (R := I (n / 8 - 1)) (VG.Proof.MlKem.X86_64.RelCT.postDep (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr (VG.Proof.MlDsa.X86_64.Sign.nomem_append (VG.Proof.MlDsa.X86_64.Sign.nomem_append (VG.Proof.MlDsa.X86_64.Sign.lea_nomem _ _)
    (VG.Proof.MlDsa.X86_64.Sign.lea_nomem _ _)) fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
    (fun x y _ => ⟨pro x, pro y⟩) fun x y x' y' hp ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ?_) ?_
  · refine RelCT.loop (M := isa) I (fun m => ?_) (n / 8 - 1)
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hr, hc⟩ e₁ e₂
    obtain ⟨ht, hr'⟩ := RelCT.taintRegs (P := fun x y => ∀ r ∈ [Reg.rdi, .rsi, .rcx], x.gpr r = y.gpr r)
      (fun _ _ h => Taint.agree_ofRegs h) [.rdi, .rsi, .rcx] VG.Proof.MlDsa.X86_64.Sign.cbody_taint _ _ _ _ _ _ hr e₁ e₂
    rw [Exec.block_iff] at e₁ e₂
    obtain ⟨c₁, z₁⟩ := VG.Proof.MlDsa.X86_64.Sign.cbody_rcx e₁
    obtain ⟨c₂, z₂⟩ := VG.Proof.MlDsa.X86_64.Sign.cbody_rcx e₂
    have ec : s₁.gpr .rcx = s₂.gpr .rcx := hr .rcx (by simp)
    have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
    refine ⟨ht, by rw [hev, hev, z₁, z₂, ec], fun _ => trivial, fun hcont => ?_⟩
    rw [hev, z₁] at hcont
    have hne : s₁.gpr .rcx - 1 ≠ 0 := by
      intro h0; rw [h0] at hcont; simp at hcont
    have h1 : (s₁.gpr .rcx - 1).toNat = m := by
      rw [BitVec.toNat_sub, hc]
      have : (1 : BitVec 64).toNat = 1 := rfl
      rw [this]; omega
    refine ⟨m - 1, ?_, hr', ?_⟩
    · have : m ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl))
      omega
    · have : m ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl))
      rw [c₁, h1]; omega
  · obtain ⟨e1, e2⟩ := hP x y hp
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a1, b1, VG.Proof.MlDsa.X86_64.Sign.pa, VG.Proof.MlDsa.X86_64.Sign.pa, e1]
      · rw [a2, b2, VG.Proof.MlDsa.X86_64.Sign.pa, VG.Proof.MlDsa.X86_64.Sign.pa, e2]
      · rw [a3, b3]
    · rw [a3, BitVec.toNat_ofNat]; omega

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inv`. -/
section

/-!
# ML-DSA signing on x86-64: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Parts of buffers -/

theorem inB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB bs (r, o) L = true)
    (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.X86_64.Sign.inB bs (r, o') l = true := by
  unfold VG.Proof.MlDsa.X86_64.Sign.inB at h ⊢
  split at h
  · rename_i n hn
    simp only [hn, decide_eq_true_eq] at h ⊢
    omega
  · cases h

theorem sepB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} {q : Ptr} {k : Nat}
    (h : VG.Proof.MlDsa.X86_64.Sign.sepB bs (r, o) L q k = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.X86_64.Sign.sepB bs (r, o') l q k = true := by
  unfold VG.Proof.MlDsa.X86_64.Sign.sepB at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hp, hq⟩, hs⟩ := h
  refine ⟨⟨VG.Proof.MlDsa.X86_64.Sign.inB_sub hp h2, hq⟩, ?_⟩
  rcases hs with hs | ⟨he, hs⟩
  · exact .inl hs
  · exact .inr ⟨he, by omega⟩

theorem keepB_sub {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {r : Reg} {o L o' l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.keepB bs ws (r, o) L = true)
    (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.X86_64.Sign.keepB bs ws (r, o') l = true := by
  unfold VG.Proof.MlDsa.X86_64.Sign.keepB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨h.1.1, VG.Proof.MlDsa.X86_64.Sign.inB_sub h.1.2 h2⟩, fun w hw => VG.Proof.MlDsa.X86_64.Sign.sepB_sub (h.2 w hw) h1 h2⟩

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (D : Nat) (σ s : State) : Prop where
  top : VG.Proof.MlDsa.X86_64.Sign.Top σ s
  lay : VG.Proof.MlDsa.X86_64.Sign.Lay D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) s
  sk : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (.rbp, 0)) p.skLen = VG.Proof.MlDsa.X86_64.Sign.skOf p σ
  mu : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (.r12, 0)) 64 = VG.Proof.MlDsa.X86_64.Sign.muOf σ
  rnd : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (.r13, 0)) 32 = VG.Proof.MlDsa.X86_64.Sign.rndOf σ

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.topChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (.rbp, 0) p.skLen && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (.r12, 0) 64 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (.r13, 0) 32

theorem St.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.X86_64.Sign.St p D σ s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.stChk p ws = true) : VG.Proof.MlDsa.X86_64.Sign.St p D σ s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.stChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p), (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : Poly) : Prop := PolyIs s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → Poly) : Prop := ∀ j < m, VG.Proof.MlDsa.X86_64.Sign.Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool := m == 0 || keepB bs ws (pS b) (1024 * m)

theorem famChk_one {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.famChk bs ws b m = true) (hj : j < m) :
    VG.Proof.MlDsa.X86_64.Sign.keepB bs ws (pS (b + j)) 1024 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine VG.Proof.MlDsa.X86_64.Sign.keepB_sub h ?_ ?_ <;> simp only [VG.Impl.MlDsa.X86_64.Sign.oP] <;> omega

theorem Fam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) {b m : Nat} {f : Nat → Poly}
    (hc : VG.Proof.MlDsa.X86_64.Sign.famChk (rbs ++ wbs) ws b m = true) (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b m f) : VG.Proof.MlDsa.X86_64.Sign.Fam s' b m f :=
  fun j hj => L.keepPoly hP (VG.Proof.MlDsa.X86_64.Sign.famChk_one hc hj) (h j hj)

theorem Pl.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) {j : Nat} {f : Poly}
    (hc : VG.Proof.MlDsa.X86_64.Sign.keepB (rbs ++ wbs) ws (pS j) 1024 = true) (h : VG.Proof.MlDsa.X86_64.Sign.Pl s j f) : VG.Proof.MlDsa.X86_64.Sign.Pl s' j f :=
  L.keepPoly hP hc h

theorem Fam.congr {s : State} {b m : Nat} {f g : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b m f) (e : ∀ j < m, f j = g j) :
    VG.Proof.MlDsa.X86_64.Sign.Fam s b m g := fun j hj => e j hj ▸ h j hj

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.split {s : State} {b m r : Nat} {f : Nat → Poly} (hr : r ≤ m) :
    VG.Proof.MlDsa.X86_64.Sign.Fam s b m f ↔ VG.Proof.MlDsa.X86_64.Sign.Fam s b r f ∧ VG.Proof.MlDsa.X86_64.Sign.Fam s (b + r) (m - r) fun j => f (r + j) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), fun j hj => by rw [Nat.add_assoc]; exact h (r + j) (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases e : j < r
    · exact h1 j e
    · have := h2 (j - r) (by omega)
      simp only [show b + r + (j - r) = b + j by omega, show r + (j - r) = j by omega] at this
      exact this

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Prims`. -/
section

/-!
# ML-DSA signing on x86-64: the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is verified against its shared contract (`Spec/MlDsa/Poly.lean`) for a
stack that fits in the `D` bytes the function gives its calls (`Callee`); and,
of the samplers whose result the function branches on, that the result is
public in their own runs (`RetPub`) and that they succeed only when the
algorithm finishes within `maxBounds`, the bounds the leakage of signing is
stated for.

For each call of an arithmetic primitive: what it does (`…At_ok`), and that
two runs in the same layout leak the same (`…At_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs need of the implementations `P` of the primitives, with
`D` bytes of stack for each call. -/
structure PrimsOk (P : Prims) (D : Nat) where
  ntt : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => nttContract X86_64.abi S) D P.ntt
  invNtt : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => nttInvContract X86_64.abi S) D P.invNtt
  mul : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => mulContract X86_64.abi S) D P.mul
  mulAdd : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => mulAddContract X86_64.abi S) D P.mulAdd
  add : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => addContract X86_64.abi S) D P.add
  sub : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => subContract X86_64.abi S) D P.sub
  rejNTT : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => rejNTTContract X86_64.abi S) D P.rejNTT
  expandMask : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => expandMaskContract X86_64.abi S) D P.expandMask
  ball : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => sampleInBallContract X86_64.abi S) D P.ball
  highBits : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => highBitsContract X86_64.abi S) D P.highBits
  lowBits : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => lowBitsContract X86_64.abi S) D P.lowBits
  normLt : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => normLtContract X86_64.abi S) D P.normLt
  makeHint : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => makeHintContract X86_64.abi S) D P.makeHint
  simpleBitPack : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => simpleBitPackContract X86_64.abi S) D P.simpleBitPack
  bitPack : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => bitPackContract X86_64.abi S) D P.bitPack
  bitUnpack : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => bitUnpackContract X86_64.abi S) D P.bitUnpack
  hintBitPack : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => hintBitPackContract X86_64.abi S) D P.hintBitPack
  rej4 : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => rejNTT4Contract X86_64.abi S) D P.rej4
  expandMask4 : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => expandMask4Contract X86_64.abi S) D P.expandMask4
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : VG.Proof.MlDsa.X86_64.Sign.RetPub (rejNTTContract X86_64.abi rejNTT.S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract X86_64.abi rejNTT.S).pre s → Exec isa P.rejNTT s t s' →
    (s'.gpr .rax).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .rdi) 34)).isSome
  /-- `vg_mldsa_rej_ntt_poly4`'s result depends only on its public data (its seeds). -/
  rej4Ret : VG.Proof.MlDsa.X86_64.Sign.RetPub (rejNTT4Contract X86_64.abi rej4.S) P.rej4
  /-- `vg_mldsa_rej_ntt_poly4` succeeds only if `RejNTTPoly` finishes within `maxBounds` on each seed. -/
  rej4Max : ∀ s t s', (rejNTT4Contract X86_64.abi rej4.S).pre s → Exec isa P.rej4 s t s' →
    (s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (s.gpr .rdi) k)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : VG.Proof.MlDsa.X86_64.Sign.RetPub (sampleInBallContract X86_64.abi ball.S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract X86_64.abi ball.S).pre s → Exec isa P.ball s t s' →
    (s'.gpr .rax).setWidth 32 = 1 →
    (sampleInBall ((s.gpr .rdx).setWidth 32).toNat maxBounds.ball (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).isSome
  /-- `D` leaves room for the calls of the sponge functions. -/
  hD : 24 ≤ D
  hD' : D < 2 ^ 32

/-! ## The arguments of a call -/

theorem sw32_ofNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem toNat64 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; omega

theorem ptr_ok {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h1 : p.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) (h2 : p.2 < 2 ^ 31) : (Arg.ptr p).ok = true := by
  simp [Arg.ok, h1, h2]

theorem imm_ok {v : Nat} (h : v < 2 ^ 32) : (Arg.imm v).ok = true := by
  simp [Arg.ok, h]

/-- The setting of a call from a state in a layout: the stack pointer and
memory as they were, and the layout. -/
structure At (D : Nat) (rbs wbs : List (Reg × Nat)) (s s1 : State) : Prop where
  L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s
  mem : s1.mem = s.mem
  rsp : s1.gpr .rsp = s.gpr .rsp

theorem At.of {D : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) (hm : s1.mem = s.mem)
    (k : Keep VG.Proof.MlDsa.X86_64.Sign.argRegs s s1) : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1 := ⟨L, hm, k.gpr (by decide)⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1)
include A

theorem At.ret {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) (hD : 8 ≤ D) :
    Region.Disjoint ⟨s1.gpr .rsp - 8, 8⟩ ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ := by
  rw [A.rsp]; exact VG.Proof.MlDsa.X86_64.Sign.ce_ret (A.L.stkD h) hD A.L.dsm

theorem At.stk {S : Nat} (hS : S + 8 ≤ D) {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) :
    (below (s1.gpr .rsp - 8) S).Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ := by
  rw [A.rsp]; exact VG.Proof.MlDsa.X86_64.Sign.ce_below (A.L.stkD h) hS A.L.dsm

theorem At.k1 {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) :
    (below (s1.gpr .rsp) D).Disjoint ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, l⟩ := by
  rw [A.rsp]; exact A.L.stkD h

theorem At.poly {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    polyAt s1.callEntry.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) = polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) := by
  rw [VG.Proof.MlDsa.X86_64.Sign.ce_polyAt s1 (A.k1 h) hD A.L.dsm, A.mem]

theorem At.natPoly {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    natPolyAt s1.callEntry.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) = natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) := by
  rw [VG.Proof.MlDsa.X86_64.Sign.ce_natPolyAt s1 (A.k1 h) hD A.L.dsm, A.mem]

theorem At.red {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    Reduced s1.callEntry.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) ↔ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) := by
  rw [VG.Proof.MlDsa.X86_64.Sign.ce_reduced s1 (A.k1 h) hD A.L.dsm, A.mem]

theorem At.bytes {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) (hD : 8 ≤ D) :
    bytesAt s1.callEntry.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) l = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) l := by
  rw [VG.Proof.MlDsa.X86_64.Sign.ce_bytesAt s1 (A.L.nwp h |> fun h' => by omega) (A.k1 h) hD A.L.dsm, A.mem]

theorem At.coeff {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) {i : Nat} (hi : i < 256) :
    coeffAt s1.callEntry.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) i = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) i := by
  rw [coeffAt_congr₂ (p := VG.Proof.MlDsa.X86_64.Sign.pa s p) (m := s.mem) (fun k hk => ?_) hi]
  rw [← A.mem]; exact VG.Proof.MlDsa.X86_64.Sign.ce_byte s1 (R := VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s p)) (A.k1 h) hD A.L.dsm (show 1024 ≤ 2 ^ 64 by decide) hk

theorem At.hint {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {k : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p (1024 * k) = true) (hD : 8 ≤ D) :
    hintAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) k = hintAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) k := by
  rw [hintAt_congr (m := s.mem) fun x hx => ?_]
  rw [← A.mem]
  exact VG.Proof.MlDsa.X86_64.Sign.ce_byte s1 (R := ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, 1024 * k⟩) (A.k1 h) hD A.L.dsm (show 1024 * k ≤ 2 ^ 64 by have := A.L.nwp h; omega) hx

theorem At.coeffs {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {len : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p (len * 4) = true) (hD : 8 ≤ D) :
    (List.range len).map (fun i => (coeffAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) i).toNat) =
      (List.range len).map (fun i => (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) i).toNat) := by
  rw [coeffs_congr (m := s.mem) fun x hx => ?_]
  rw [← A.mem]
  exact VG.Proof.MlDsa.X86_64.Sign.ce_byte s1 (R := ⟨VG.Proof.MlDsa.X86_64.Sign.pa s p, len * 4⟩) (A.k1 h) hD A.L.dsm (show len * 4 ≤ 2 ^ 64 by have := A.L.nwp h; omega)
    (show x < len * 4 by omega)

theorem At.coeff' {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) {i : Nat} (hi : i < 256) :
    coeffAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) i = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) i :=
  A.coeff h hD hi

theorem At.poly' {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    polyAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) = polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) :=
  A.poly h hD

theorem At.natPoly' {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    natPolyAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) = natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) :=
  A.natPoly h hD

theorem At.bytes' {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true) (hD : 8 ≤ D) :
    VG.Spec.Sha3.bytesAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) l = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p) l :=
  A.bytes h hD

theorem At.red' {p : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s p)) :
    Reduced (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s p) :=
  (A.red h hD).mpr hr

end

/-! ## `NTT` and `NTT⁻¹` in place -/

section
variable {P : Prims} {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call of an in-place transformation of `f` needs of the layout. -/
def ipChk (bs wbs : List (Reg × Nat)) (f : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs f 1024 && VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 1024 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs f 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 1024 && decide (f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (f.2 < 2 ^ 31)

theorem ipChk_spec {bs wbs : List (Reg × Nat)} {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} (h : VG.Proof.MlDsa.X86_64.Sign.ipChk bs wbs f = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs f 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 1024 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs f 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 1024 = true ∧ f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ f.2 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ipChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ipPre {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {f : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.ipChk (rbs ++ wbs) wbs f = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr f, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)] s s1)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) :
    (inPlaceContract X86_64.abi t S).pre (s1.callEntry.withRegions [] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS))]) := by
  obtain ⟨_, _, i1, i2, d12, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.ipChk_spec hc
  obtain ⟨h1, h2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS))]
  sig_pre [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [h1, h2, Arg.val]
  refine ⟨hwf, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, ?_⟩
  · refine Sig.conj_cons.mpr ⟨A.ret i2 hD, ?_⟩
    exact VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS))] (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨A.stk hS i1, A.stk hS i2⟩)
  · exact (A.red i1 hD).mpr hr

theorem ipAt_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => inPlaceContract X86_64.abi t S) D c)
    {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.ipChk (rbs ++ wbs) wbs f = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) :
    WP isa (callP n c [.ptr f, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)]) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(f, 1024), (VG.Impl.MlDsa.X86_64.Sign.sc oPS, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f))) := by
  obtain ⟨w1, w2, i1, _, _, b1, o1⟩ := VG.Proof.MlDsa.X86_64.Sign.ipChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok C.ver.1 C.nosp C.depth L.dsm (by simp [Arg.ok, b1, o1]; decide)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.ipPre C.hS (At.of L hm k) hc hA hr) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))
    (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨h1, _⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hA
  sig_post [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [h1, Arg.val, hm₂, ← State.callEntry_mem, A.poly i1 hD] at hq
  exact hq

theorem ipAt_tr {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => inPlaceContract X86_64.abi t S) D c)
    {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f))
      (callP n c [.ptr f, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)]) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, _, b1, o1⟩ := VG.Proof.MlDsa.X86_64.Sign.ipChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr C.ver.1 C.ver.2.1 (by simp [Arg.ok, b1, o1]; decide)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.ipPre C.hS (At.of R.lx hmx kx) hc hAx rx, VG.Proof.MlDsa.X86_64.Sign.ipPre C.hS (At.of R.ly hmy ky) hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2)),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2)),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hAy
  sig_pub [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## Products -/

/-- What a call of `vg_mldsa_multiply_ntt` or `vg_mldsa_multiply_add_ntt` on
`h`, `f`, `g` needs of the layout. -/
def mulChk (bs wbs : List (Reg × Nat)) (h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs h 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs h 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs g 1024 && VG.Proof.MlDsa.X86_64.Sign.sepB bs h 1024 f 1024 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs h 1024 g 1024 && decide (h.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (h.2 < 2 ^ 31) && decide (f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) &&
    decide (f.2 < 2 ^ 31) && decide (g.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (g.2 < 2 ^ 31)

theorem mulChk_spec {bs wbs : List (Reg × Nat)} {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk bs wbs h f g = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs h 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs h 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs g 1024 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs h 1024 f 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs h 1024 g 1024 = true ∧
      ([Arg.ptr h, .ptr f, .ptr g].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.mulChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [Arg.ok, h7, h8, h9, h10, h11, h12]⟩

theorem mulPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk (rbs ++ wbs) wbs h f g = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr h, .ptr f, .ptr g] s s1)
    (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    (mulContract X86_64.abi S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := VG.Proof.MlDsa.X86_64.Sign.mulChk_spec hc
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)]
  sig_pre [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, A.red' i2 hD rf, A.red' i3 hD rg⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem mulAddPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk (rbs ++ wbs) wbs h f g = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr h, .ptr f, .ptr g] s s1)
    (rh : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h)) (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    (mulAddContract X86_64.abi S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := VG.Proof.MlDsa.X86_64.Sign.mulChk_spec hc
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)]
  sig_pre [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, A.red' i1 hD rh, A.red' i2 hD rf, A.red' i3 hD rg⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem mulAt_ok {P : Prims} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => mulContract X86_64.abi S) D P.mul)
    {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk (rbs ++ wbs) wbs h f g = true)
    (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.Sign.mulAt P h f g) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(h, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.mulChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok C.ver.1 C.nosp C.depth L.dsm ok
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.mulPre C.hS (At.of L hm k) hc hA rf rg)
    (Covers.append_left (Covers.cons (L.cR i2) (L.cR i3)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  sig_post [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i2 hD, A.poly' i3 hD] at hq
  exact hq

theorem mulAddAt_ok {P : Prims} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => mulAddContract X86_64.abi S) D P.mulAdd)
    {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk (rbs ++ wbs) wbs h f g = true)
    (rh : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h)) (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(h, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h)
        (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.mulChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok C.ver.1 C.nosp C.depth L.dsm ok
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.mulAddPre C.hS (At.of L hm k) hc hA rh rf rg)
    (Covers.append_left (Covers.cons (L.cR i2) (L.cR i3)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  sig_post [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i1 hD, A.poly' i2 hD, A.poly' i3 hD] at hq
  exact hq

/-- Two runs in the same layout, with the arguments of a call in their registers. -/
theorem argsRel {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x1 y1 : State} (R : VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y)
    {as : List Arg} (hx : VG.Proof.MlDsa.X86_64.Sign.ArgsIn as x x1) (hy : VG.Proof.MlDsa.X86_64.Sign.ArgsIn as y y1)
    (hin : ∀ a ∈ as, match a with | .ptr p => ∃ l, VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) p l = true | .imm _ => True) :
    ∀ d ∈ argRegs6.zip as, x1.gpr d.1 = y1.gpr d.1 := by
  intro d hd
  rw [hx d hd, hy d hd]
  have := hin d.2 (List.of_mem_zip hd).2
  cases e : d.2 with
  | ptr p => rw [e] at this; obtain ⟨l, hl⟩ := this; simp only [Arg.val, R.pa hl]
  | imm v => rfl

theorem mulAt_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => mulContract X86_64.abi S) D P.mul)
    {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y g))) (VG.Impl.MlDsa.X86_64.Sign.mulAt P h f g) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.mulChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr C.ver.1 C.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.mulPre C.hS (At.of R.lx hmx kx) hc hAx rfx rgx, VG.Proof.MlDsa.X86_64.Sign.mulPre C.hS (At.of R.ly hmy ky) hc hAy rfy rgy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (Covers.cons (R.lx.cR i2) (R.lx.cR i3)) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (Covers.cons (R.ly.cR i2) (R.ly.cR i3)) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAy
  sig_pub [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem mulAddAt_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => mulAddContract X86_64.abi S) D P.mulAdd)
    {h f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧
      (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x h) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y h) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y g))) (mulAddAt P h f g)
      fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.mulChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr C.ver.1 C.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rhx, rfx, rgx⟩, ⟨rhy, rfy, rgy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.mulAddPre C.hS (At.of R.lx hmx kx) hc hAx rhx rfx rgx,
        VG.Proof.MlDsa.X86_64.Sign.mulAddPre C.hS (At.of R.ly hmy ky) hc hAy rhy rfy rgy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (Covers.cons (R.lx.cR i2) (R.lx.cR i3)) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (Covers.cons (R.ly.cR i2) (R.ly.cR i3)) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAy
  sig_pub [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsB`. -/
section

/-!
# ML-DSA signing on x86-64: calls of addition, subtraction and the samplers

As `Prims.lean`, for `vg_mldsa_add`, `vg_mldsa_sub`, `vg_mldsa_rej_ntt_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball`. The samplers'
results are public in two runs whose seeds agree (`rejCall_tr`,
`ballCall_tr`), and they succeed only if the algorithm finishes within
`maxBounds` (`rejCall_ok`, `ballCall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `k` with the fact `X` of each run added to its postcondition. -/
def withPost (k : Contract isa) (X : State → State → Prop) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ X s s' }

theorem hv_with {c : Prog isa} {k : Contract isa} {X : State → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hx : ∀ s t s', k.pre s → Exec isa c s t s' → X s s') :
    ∀ s, (VG.Proof.MlDsa.X86_64.Sign.withPost k X).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlDsa.X86_64.Sign.withPost k X).post s s' :=
  fun s hs => let ⟨t, s', e, a, p⟩ := hv s hs; ⟨t, s', e, a, p, hx s t s' hs e⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## Addition and subtraction -/

/-- The contract of `vg_mldsa_add` (`t = add`) or `vg_mldsa_sub` (`t = sub`). -/
abbrev accC (t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly) (S : Nat) : Contract isa :=
  accSig.contract X86_64.abi
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (t (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := S)

/-- What a call of `vg_mldsa_add` or `vg_mldsa_sub` on `f`, `g` needs of the layout. -/
def accChk (bs wbs : List (Reg × Nat)) (f g : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs f 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs g 1024 && VG.Proof.MlDsa.X86_64.Sign.sepB bs f 1024 g 1024 && decide (f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) &&
    decide (f.2 < 2 ^ 31) && decide (g.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (g.2 < 2 ^ 31)

theorem accChk_spec {bs wbs : List (Reg × Nat)} {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.accChk bs wbs f g = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs f 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs g 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs f 1024 g 1024 = true ∧
      ([Arg.ptr f, .ptr g].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.accChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, by simp [Arg.ok, h5, h6, h7, h8]⟩

theorem accPre {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1)
    {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr f, .ptr g] s s1)
    (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    (VG.Proof.MlDsa.X86_64.Sign.accC t S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.X86_64.Sign.accChk_spec hc
  obtain ⟨e1, e2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)]
  sig_pre [accSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, A.red' i1 hD rf,
    A.red' i2 hD rg⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s g)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem accAt_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => VG.Proof.MlDsa.X86_64.Sign.accC t S) D c)
    {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    WP isa (callP n c [.ptr f, .ptr g]) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(f, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g))) := by
  obtain ⟨w1, i1, i2, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.accChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok C.ver.1 C.nosp C.depth L.dsm ok
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.accPre C.hS (At.of L hm k) hc hA rf rg)
    (Covers.append_left (L.cR i2) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hA
  sig_post [accSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, hm₂, A.poly' i1 hD, A.poly' i2 hD] at hq
  exact hq

theorem accAt_tr {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => VG.Proof.MlDsa.X86_64.Sign.accC t S) D c)
    {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y g))) (callP n c [.ptr f, .ptr g]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.accChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr C.ver.1 C.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.accPre C.hS (At.of R.lx hmx kx) hc hAx rfx rgx, VG.Proof.MlDsa.X86_64.Sign.accPre C.hS (At.of R.ly hmy ky) hc hAy rfy rgy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i2) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i2) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hAy
  sig_pub [accSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem addAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.Sign.addAt P f g) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(f, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g))) :=
  VG.Proof.MlDsa.X86_64.Sign.accAt_ok (t := VG.Spec.MlDsa.add) hP.add L hc rf rg

theorem subAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.Sign.subAt P f g) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(f, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) (VG.Spec.MlDsa.sub (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s g))) :=
  VG.Proof.MlDsa.X86_64.Sign.accAt_ok (t := VG.Spec.MlDsa.sub) hP.sub L hc rf rg

theorem addAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y g))) (VG.Impl.MlDsa.X86_64.Sign.addAt P f g) fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Sign.accAt_tr (t := VG.Spec.MlDsa.add) hP.add hc

theorem subAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {f g : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y g))) (VG.Impl.MlDsa.X86_64.Sign.subAt P f g) fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Sign.accAt_tr (t := VG.Spec.MlDsa.sub) hP.sub hc

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
def rejChk (bs wbs : List (Reg × Nat)) (a : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs a 1024 && VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS) 34 && VG.Proof.MlDsa.X86_64.Sign.inB bs a 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS) 34 a 1024 && VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS) 34 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 && VG.Proof.MlDsa.X86_64.Sign.sepB bs a 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 &&
    decide (a.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (a.2 < 2 ^ 31)

theorem rejChk_spec {bs wbs : List (Reg × Nat)} {a : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.rejChk bs wbs a = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs a 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS) 34 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs a 1024 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS) 34 a 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS) 34 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs a 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ ([Arg.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS), .ptr a, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.rejChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  simp only [List.all_cons, List.all_nil, Arg.ok, h9, h10, decide_true, Bool.and_true]
  decide

theorem rejPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {a : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.rejChk (rbs ++ wbs) wbs a = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS), .ptr a, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)] s s1) :
    (rejNTTContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS), 34⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s a), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rejChk_spec hc
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS), 34⟩]
    [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s a), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩]
  sig_pre [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS), 34⟩, VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s a), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS), .ptr a, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)]) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(a, 1024), (VG.Impl.MlDsa.X86_64.Sign.sc oPS, 2048)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS)) 34)) ((s'.gpr .rax).setWidth 32)
        (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s a)) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS)) 34)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.rejChk_spec hc
  have hD : 8 ≤ D := by have := hP.rejNTT.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok (VG.Proof.MlDsa.X86_64.Sign.hv_with hP.rejNTT.ver.1 hP.rejMax) hP.rejNTT.nosp hP.rejNTT.depth L.dsm ok
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.rejPre hP.rejNTT.hS (At.of L hm k) hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, hm₂, er, A.bytes' i1 hD] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    e1, Arg.val, er, A.bytes i1 hD] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCall_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {a : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.rejChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x (VG.Impl.MlDsa.X86_64.Sign.sc oRS)) 34 = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y (VG.Impl.MlDsa.X86_64.Sign.sc oRS)) 34)
      (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS), .ptr a, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)])
      fun x y => (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.rejChk_spec hc
  have hD : 8 ≤ D := by have := hP.rejNTT.hS; omega
  refine VG.Proof.MlDsa.X86_64.Sign.callPRet_tr hP.rejNTT.ver.1 hP.rejRet ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.rejPre hP.rejNTT.hS (At.of R.lx hmx kx) hc hAx, VG.Proof.MlDsa.X86_64.Sign.rejPre hP.rejNTT.hS (At.of R.ly hmy ky) hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAy
  have Ax := At.of R.lx hmx kx
  have Ay := At.of R.ly hmy ky
  sig_pub [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, Ax.bytes' i1 hD, Ay.bytes' i1 hD, hb]
  simp only [Ax.rsp, Ay.rsp, R.rsp, R.pa i1, R.pa i2, R.pa i3, and_self]

/-! ## `RejNTTPoly` four times -/

/-- What the call of `vg_mldsa_rej_ntt_poly4` from the seeds at `RS4` to the four polynomials from `a`,
with the working space `w`, needs of the layout. -/
def rej4Chk (bs wbs : List (Reg × Nat)) (a w : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs a 4096 && VG.Proof.MlDsa.X86_64.Sign.inB wbs w 8192 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 && VG.Proof.MlDsa.X86_64.Sign.inB bs a 4096 && VG.Proof.MlDsa.X86_64.Sign.inB bs w 8192 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 a 4096 && VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 w 8192 && VG.Proof.MlDsa.X86_64.Sign.sepB bs a 4096 w 8192 &&
    decide (a.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (a.2 < 2 ^ 31) && decide (w.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (w.2 < 2 ^ 31)

theorem rej4Chk_spec {bs wbs : List (Reg × Nat)} {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.rej4Chk bs wbs a w = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs a 4096 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs w 8192 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs a 4096 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB bs w 8192 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 a 4096 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 w 8192 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs a 4096 w 8192 = true ∧ ([Arg.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), .ptr a, .ptr w].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.rej4Chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  simp only [List.all_cons, List.all_nil, Arg.ok, h9, h10, h11, h12, decide_true, Bool.and_true]
  decide

theorem rej4Pre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.rej4Chk (rbs ++ wbs) wbs a w = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), .ptr a, .ptr w] s s1) :
    (rejNTT4Contract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), 136⟩] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w, 8192⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rej4Chk_spec hc
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), 136⟩]
    [⟨VG.Proof.MlDsa.X86_64.Sign.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w, 8192⟩]
  sig_pre [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), 136⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w, 8192⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The seeds on entry to the call are those before it. -/
theorem At.seeds4 {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) (hi : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Sign.sc oRS4) 136 = true) (hD : 8 ≤ D)
    {k : Nat} (hk : k < 4) :
    seed4 (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) k = seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) k := by
  unfold seed4
  rw [← VG.Proof.MlKem.bytesAt_slice _ _ (show 34 * k + 34 ≤ 136 by omega),
    ← VG.Proof.MlKem.bytesAt_slice s.mem _ (show 34 * k + 34 ≤ 136 by omega), A.bytes' hi hD]

/-- The call of `vg_mldsa_rej_ntt_poly4`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds` on each seed. -/
theorem rej4Call_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hc : VG.Proof.MlDsa.X86_64.Sign.rej4Chk (rbs ++ wbs) wbs a w = true) :
    WP isa (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), .ptr a, .ptr w]) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(a, 4096), (w, 8192)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, Reduced s'.mem (poly4 (VG.Proof.MlDsa.X86_64.Sign.pa s a) k)) ∧
      (((s'.gpr .rax).setWidth 32 = 1 ∧ ∀ k < 4, ∃ b : Bounds,
          rejNTTPoly b.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) k) = some (polyAt s'.mem (poly4 (VG.Proof.MlDsa.X86_64.Sign.pa s a) k))) ∨
        ((s'.gpr .rax).setWidth 32 = 0 ∧ ∃ k < 4,
          rejNTTPoly minBounds.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) k) = none)) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4,
        (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) k)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.rej4Chk_spec hc
  have hD : 8 ≤ D := by have := hP.rej4.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok (VG.Proof.MlDsa.X86_64.Sign.hv_with hP.rej4.ver.1 hP.rej4Max) hP.rej4.nosp hP.rej4.depth L.dsm ok
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.rej4Pre hP.rej4.hS (At.of L hm k) hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, hm₂, er] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    e1, Arg.val, er] at hx
  obtain ⟨hr, ho⟩ := hq
  refine ⟨hr, ?_, fun h1 k hk => by rw [← A.seeds4 i1 hD hk]; exact hx h1 k hk⟩
  rcases ho with ⟨h1, hb⟩ | ⟨h0, k, hk, hn⟩
  · exact .inl ⟨h1, fun k hk => by rw [← A.seeds4 i1 hD hk]; exact hb k hk⟩
  · exact .inr ⟨h0, k, hk, by rw [← A.seeds4 i1 hD hk]; exact hn⟩

theorem rej4Call_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.rej4Chk (rbs ++ wbs) wbs a w = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧
        bytesAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) 136 = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y (VG.Impl.MlDsa.X86_64.Sign.sc oRS4)) 136)
      (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oRS4), .ptr a, .ptr w])
      fun x y => (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := VG.Proof.MlDsa.X86_64.Sign.rej4Chk_spec hc
  have hD : 8 ≤ D := by have := hP.rej4.hS; omega
  refine VG.Proof.MlDsa.X86_64.Sign.callPRet_tr hP.rej4.ver.1 hP.rej4Ret ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.rej4Pre hP.rej4.hS (At.of R.lx hmx kx) hc hAx, VG.Proof.MlDsa.X86_64.Sign.rej4Pre hP.rej4.hS (At.of R.ly hmy ky) hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAy
  have Ax := At.of R.lx hmx kx
  have Ay := At.of R.ly hmy ky
  sig_pub [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, Ax.bytes' i1 hD, Ay.bytes' i1 hD, hb]
  simp only [Ax.rsp, Ay.rsp, R.rsp, R.pa i1, R.pa i2, R.pa i3, and_self]

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
def maskChk (bs wbs : List (Reg × Nat)) (a : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs a 1024 && VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS) 66 && VG.Proof.MlDsa.X86_64.Sign.inB bs a 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS) 66 a 1024 && VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS) 66 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 && VG.Proof.MlDsa.X86_64.Sign.sepB bs a 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 &&
    decide (a.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (a.2 < 2 ^ 31)

theorem maskChk_spec {bs wbs : List (Reg × Nat)} {a : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.maskChk bs wbs a = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs a 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS) 66 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs a 1024 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS) 66 a 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS) 66 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs a 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ a.2 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.maskChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem maskPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {γ : Nat} {a : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.X86_64.Sign.maskChk (rbs ++ wbs) wbs a = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oMS), .imm γ, .ptr a, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)] s s1) :
    (expandMaskContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS), 66⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s a), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.X86_64.Sign.maskChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hγ' : γ < 2 ^ 32 := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS), 66⟩]
    [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s a), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩]
  sig_pre [expandMaskContract, expandMaskSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hγ']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3, hγ⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS), 66⟩, VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s a), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem maskAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {γ : Nat} {a : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.X86_64.Sign.maskChk (rbs ++ wbs) wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(a, 1024), (VG.Impl.MlDsa.X86_64.Sign.sc oPS, 2048)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s a) (toRq (bitUnpack (H (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := VG.Proof.MlDsa.X86_64.Sign.maskChk_spec hc
  have hD : 8 ≤ D := by have := hP.expandMask.hS; omega
  have hγ' : γ < 2 ^ 32 := by omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.expandMask.ver.1 hP.expandMask.nosp hP.expandMask.depth L.dsm
    (by simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true, decide_eq_true hγ']; decide)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.maskPre hP.expandMask.hS (At.of L hm k) hγ hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, _⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  sig_post [expandMaskContract, expandMaskSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.bytes' i1 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hγ'] at hq
  exact hq

theorem maskAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {γ : Nat} {a : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : VG.Proof.MlDsa.X86_64.Sign.maskChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (maskAt P γ a) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := VG.Proof.MlDsa.X86_64.Sign.maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.expandMask.ver.1 hP.expandMask.ver.2.1
    (by simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true, decide_eq_true hγ']; decide)
    fun x y x1 y1 R ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.maskPre hP.expandMask.hS (At.of R.lx hmx kx) hγ hc hAx,
        VG.Proof.MlDsa.X86_64.Sign.maskPre hP.expandMask.hS (At.of R.ly hmy ky) hγ hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAy
  sig_pub [expandMaskContract, expandMaskSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `ExpandMask` four times -/

/-- What the call of `vg_mldsa_expand_mask_poly4` from the seeds at `MS4` to the four polynomials from `a`,
with the working space `w`, needs of the layout. -/
def mask4Chk (bs wbs : List (Reg × Nat)) (a w : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs a 4096 && VG.Proof.MlDsa.X86_64.Sign.inB wbs w 8192 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 && VG.Proof.MlDsa.X86_64.Sign.inB bs a 4096 && VG.Proof.MlDsa.X86_64.Sign.inB bs w 8192 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 a 4096 && VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 w 8192 && VG.Proof.MlDsa.X86_64.Sign.sepB bs a 4096 w 8192 &&
    decide (a.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (a.2 < 2 ^ 31) && decide (w.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (w.2 < 2 ^ 31)

theorem mask4Chk_spec {bs wbs : List (Reg × Nat)} {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.mask4Chk bs wbs a w = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs a 4096 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs w 8192 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs a 4096 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB bs w 8192 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 a 4096 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 w 8192 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs a 4096 w 8192 = true ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ a.2 < 2 ^ 31 ∧ w.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ w.2 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.mask4Chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem mask4Pre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {γ : Nat} {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.X86_64.Sign.mask4Chk (rbs ++ wbs) wbs a w = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oMS4), .imm γ, .ptr a, .ptr w] s s1) :
    (expandMask4Contract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS4), 264⟩] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w, 8192⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.X86_64.Sign.mask4Chk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hγ' : γ < 2 ^ 32 := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS4), 264⟩]
    [⟨VG.Proof.MlDsa.X86_64.Sign.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w, 8192⟩]
  sig_pre [expandMask4Contract, expandMask4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hγ']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3, hγ⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS4), 264⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s w, 8192⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The seeds on entry to the call are those before it. -/
theorem At.seeds66 {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) (hi : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Sign.sc oMS4) 264 = true) (hD : 8 ≤ D)
    {k : Nat} (hk : k < 4) :
    seed66 (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS4)) k = seed66 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS4)) k := by
  unfold seed66
  rw [← VG.Proof.MlKem.bytesAt_slice _ _ (show 66 * k + 66 ≤ 264 by omega),
    ← VG.Proof.MlKem.bytesAt_slice s.mem _ (show 66 * k + 66 ≤ 264 by omega), A.bytes' hi hD]

/-- The call of `vg_mldsa_expand_mask_poly4`. -/
theorem mask4Call_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {γ : Nat} {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.X86_64.Sign.mask4Chk (rbs ++ wbs) wbs a w = true) :
    WP isa (mask4At P γ a w) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(a, 4096), (w, 8192)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ ∀ k < 4,
      PolyIs s'.mem (poly4 (VG.Proof.MlDsa.X86_64.Sign.pa s a) k) (toRq (bitUnpack
        (H (seed66 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oMS4)) k) (32 * (1 + bitlen (γ - 1)))) (γ - 1) γ)) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.mask4Chk_spec hc
  have hD : 8 ≤ D := by have := hP.expandMask4.hS; omega
  have hγ' : γ < 2 ^ 32 := by omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.expandMask4.ver.1 hP.expandMask4.nosp hP.expandMask4.depth L.dsm
    (by simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
      decide_eq_true hγ']; decide)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.mask4Pre hP.expandMask4.hS (At.of L hm k) hγ hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, _⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  sig_post [expandMask4Contract, expandMask4Sig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hγ'] at hq
  exact fun k hk => by rw [← A.seeds66 i1 hD hk]; exact hq k hk

theorem mask4Call_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {γ : Nat} {a w : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : VG.Proof.MlDsa.X86_64.Sign.mask4Chk (rbs ++ wbs) wbs a w = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (mask4At P γ a w) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.mask4Chk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.expandMask4.ver.1 hP.expandMask4.ver.2.1
    (by simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
      decide_eq_true hγ']; decide)
    fun x y x1 y1 R ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.mask4Pre hP.expandMask4.hS (At.of R.lx hmx kx) hγ hc hAx,
        VG.Proof.MlDsa.X86_64.Sign.mask4Pre hP.expandMask4.hS (At.of R.ly hmy ky) hγ hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAy
  sig_pub [expandMask4Contract, expandMask4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
def ballChk (bs wbs : List (Reg × Nat)) (len : Nat) (c : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs c 1024 && VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oCT) len && VG.Proof.MlDsa.X86_64.Sign.inB bs c 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oCT) len c 1024 && VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oCT) len (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 && VG.Proof.MlDsa.X86_64.Sign.sepB bs c 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 &&
    decide (c.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (c.2 < 2 ^ 31)

theorem ballChk_spec {bs wbs : List (Reg × Nat)} {len : Nat} {c : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.ballChk bs wbs len c = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs c 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB wbs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oCT) len = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs c 1024 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB bs (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oCT) len c 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs (VG.Impl.MlDsa.X86_64.Sign.sc oCT) len (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs c 1024 (VG.Impl.MlDsa.X86_64.Sign.sc oPS) 2048 = true ∧ c.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ c.2 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ballChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem ballArgs_ok {len tau : Nat} {c : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hp : (len, tau) ∈ ballParams) (b1 : c.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases)
    (o1 : c.2 < 2 ^ 31) : [Arg.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oCT), .imm len, .imm tau, .ptr c, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)].all Arg.ok = true := by
  have : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true, decide_eq_true this.1,
    decide_eq_true this.2]
  decide

theorem ballPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {len tau : Nat} {c : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.X86_64.Sign.ballChk (rbs ++ wbs) wbs len c = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr (VG.Impl.MlDsa.X86_64.Sign.sc oCT), .imm len, .imm tau, .ptr c, .ptr (VG.Impl.MlDsa.X86_64.Sign.sc oPS)] s s1) :
    (sampleInBallContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oCT), len⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s c), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.X86_64.Sign.ballChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  have hD : 8 ≤ D := by omega
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oCT), len⟩]
    [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s c), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩]
  sig_pre [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hl.2, VG.Proof.MlDsa.X86_64.Sign.toNat64 hl.1]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3, hp⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oCT), len⟩, VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s c), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oPS), 2048⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {len tau : Nat} {c : VG.Impl.MlDsa.X86_64.Sign.Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.X86_64.Sign.ballChk (rbs ++ wbs) wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(c, 1024), (VG.Impl.MlDsa.X86_64.Sign.sc oPS, 2048)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oCT)) len)).map toRq)
        ((s'.gpr .rax).setWidth 32) (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s c)) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.sc oCT)) len)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := VG.Proof.MlDsa.X86_64.Sign.ballChk_spec hc
  have hD : 8 ≤ D := by have := hP.ball.hS; omega
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok (VG.Proof.MlDsa.X86_64.Sign.hv_with hP.ball.ver.1 hP.ballMax) hP.ball.nosp hP.ball.depth L.dsm (VG.Proof.MlDsa.X86_64.Sign.ballArgs_ok hp b1 o1)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.ballPre hP.ball.hS (At.of L hm k) hp hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, _⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, er, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hl.2, VG.Proof.MlDsa.X86_64.Sign.toNat64 hl.1, A.bytes' i1 hD] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    e1, e2, e3, Arg.val, er, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hl.2, VG.Proof.MlDsa.X86_64.Sign.toNat64 hl.1, A.bytes i1 hD] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {len tau : Nat} {c : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : VG.Proof.MlDsa.X86_64.Sign.ballChk (rbs ++ wbs) wbs len c = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x (VG.Impl.MlDsa.X86_64.Sign.sc oCT)) len = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y (VG.Impl.MlDsa.X86_64.Sign.sc oCT)) len)
      (ballAt P len tau c) fun x y => (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := VG.Proof.MlDsa.X86_64.Sign.ballChk_spec hc
  have hD : 8 ≤ D := by have := hP.ball.hS; omega
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  refine VG.Proof.MlDsa.X86_64.Sign.callPRet_tr hP.ball.ver.1 hP.ballRet (VG.Proof.MlDsa.X86_64.Sign.ballArgs_ok hp b1 o1)
    fun x y x1 y1 ⟨R, hb⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.ballPre hP.ball.hS (At.of R.lx hmx kx) hp hc hAx, VG.Proof.MlDsa.X86_64.Sign.ballPre hP.ball.hS (At.of R.ly hmy ky) hp hc hAy,
        ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAy
  have Ax := At.of R.lx hmx kx
  have Ay := At.of R.ly hmy ky
  sig_pub [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, VG.Proof.MlDsa.X86_64.Sign.toNat64 hl.1, Ax.bytes' i1 hD,
    Ay.bytes' i1 hD, hb]
  simp only [Ax.rsp, Ay.rsp, R.rsp, R.pa i1, R.pa i2, R.pa i3, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA`. -/
section

/-!
# ML-DSA signing on x86-64: `ExpandA`

`ρ` to `RS`, then entry `e = ℓi + j` of `Â` by `vg_mldsa_rej_ntt_poly` from
the seed `ρ ‖ j ‖ i`, with `r15` the AND of the results (`IA`): if it is 1,
every entry so far is `RejNTTPoly`'s within `maxBounds`; if it is 0, one
entry's `RejNTTPoly` does not finish within `minBounds` (`sampleE_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slot of `Â[0, 0]`; entry `e = ℓi + j` is in slot `aBase + e`. -/
abbrev aBase : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (VG.Proof.MlDsa.X86_64.Sign.skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : Poly := aF maxBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : VG.Impl.MlDsa.X86_64.Sign.aP p (e / p.ℓ) (e % p.ℓ) = pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ) = pS (5 + 4 * p.k + 3 * p.ℓ + e)
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

theorem Fam.snoc {s : State} {b m : Nat} {f : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b m f) (h' : VG.Proof.MlDsa.X86_64.Sign.Pl s (b + m) (f m)) :
    VG.Proof.MlDsa.X86_64.Sign.Fam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  st : VG.Proof.MlDsa.X86_64.Sign.St p D σ s
  rs : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS)) 32 = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ
  r01 : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1
  ok : s.gpr .r15 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.seedE p σ e')).isSome) ∧
    VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.aBase p) e (VG.Proof.MlDsa.X86_64.Sign.aVal p σ)
  bad : s.gpr .r15 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.seedE p σ e') = none

/-! ## The seed -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem seed34 {m : Mem} {a : Addr} {ρ : List Byte} (hρ : bytesAt m a 32 = ρ) {j i : Nat}
    (hj : bytesAt m (a + BitVec.ofNat 64 32) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (a + BitVec.ofNat 64 33) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m a 34 = aSeed ρ i j := by
  rw [VG.Proof.MlKem.bytesAt_add m a 33 1, VG.Proof.MlKem.bytesAt_add m a 32 1, hρ, hj, hi, aSeed,
    VG.Proof.MlDsa.X86_64.Sign.integerToBytes_one, VG.Proof.MlDsa.X86_64.Sign.integerToBytes_one]

theorem pa_sc_add (s : State) (a b : Nat) : VG.Proof.MlDsa.X86_64.Sign.pa s (sc a) + BitVec.ofNat 64 b = VG.Proof.MlDsa.X86_64.Sign.pa s (sc (a + b)) :=
  VG.Proof.MlKem.X86_64.off_add _ _ _

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

/-! ## An entry -/

/-- What entry `e` needs of the layout. -/
def eChk (p : Params) (e : Nat) : Bool :=
  let a := pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)
  let w1 : List (Ptr × Nat) := [(sc (oRS + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS + 33), 1)]
  let w3 : List (Ptr × Nat) := [(a, 1024), (sc oPS, 2048)]
  VG.Proof.MlDsa.X86_64.Sign.stChk p w1 && VG.Proof.MlDsa.X86_64.Sign.stChk p w2 && VG.Proof.MlDsa.X86_64.Sign.stChk p w3 && VG.Proof.MlDsa.X86_64.Sign.stChk p [] && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS + 32)) 1 &&
    VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS + 33)) 1 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (sc oRS) 32 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc oRS) 32 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (sc oRS) 32 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc (oRS + 32)) 1 && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (VG.Proof.MlDsa.X86_64.Sign.aBase p) e &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (VG.Proof.MlDsa.X86_64.Sign.aBase p) e && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (VG.Proof.MlDsa.X86_64.Sign.aBase p) e && VG.Proof.MlDsa.X86_64.Sign.rejChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) a &&
    decide (e % p.ℓ < 256) && decide (e / p.ℓ < 256)

theorem eChk_spec {p : Params} {e : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) :
    VG.Proof.MlDsa.X86_64.Sign.stChk p [(sc (oRS + 32), 1)] = true ∧ VG.Proof.MlDsa.X86_64.Sign.stChk p [(sc (oRS + 33), 1)] = true ∧
      VG.Proof.MlDsa.X86_64.Sign.stChk p [(pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e), 1024), (sc oPS, 2048)] = true ∧ VG.Proof.MlDsa.X86_64.Sign.stChk p [] = true ∧
      VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS + 32)) 1 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS + 33)) 1 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS + 32), 1)] (sc oRS) 32 = true ∧ VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS + 33), 1)] (sc oRS) 32 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e), 1024), (sc oPS, 2048)] (sc oRS) 32 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS + 33), 1)] (sc (oRS + 32)) 1 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS + 32), 1)] (VG.Proof.MlDsa.X86_64.Sign.aBase p) e = true ∧ VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS + 33), 1)] (VG.Proof.MlDsa.X86_64.Sign.aBase p) e = true ∧
      VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e), 1024), (sc oPS, 2048)] (VG.Proof.MlDsa.X86_64.Sign.aBase p) e = true ∧
      VG.Proof.MlDsa.X86_64.Sign.rejChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) = true ∧ e % p.ℓ < 256 ∧ e / p.ℓ < 256 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.eChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD VG.Spec.MlDsa.zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem outcome01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α} (h : Outcome f r out) :
    r = 1 ∨ r = 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem Fam.of_eq {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr .rbx = s.gpr .rbx) {b m : Nat}
    {f : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b m f) : VG.Proof.MlDsa.X86_64.Sign.Fam s' b m f := fun j hj => by
  simp only [VG.Proof.MlDsa.X86_64.Sign.Pl, VG.Proof.MlDsa.X86_64.Sign.pa, hm, hb]; exact h j hj

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

theorem blkE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s) : WP isa (.block (VG.Proof.MlDsa.X86_64.Sign.blkE p e)) s fun s' =>
      (VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' (sc oRS)) 34 = VG.Proof.MlDsa.X86_64.Sign.seedE p σ e) ∧ s'.gpr .r15 = s.gpr .r15 := by
  obtain ⟨c1, c2, _, _, w1, w2, k1, k2, _, k12, f1, f2, _, _, hj, hi⟩ := VG.Proof.MlDsa.X86_64.Sign.eChk_spec he
  have L := h.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setB_okB L (by decide) hj w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have S1 := h.st.step hP1 c1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setB_okB S1.lay (by decide) hi w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have S2 := S1.step hP2 c2
  have e15 : s2.gpr .r15 = s.gpr .r15 := by rw [hcs2 _ (by decide), hcs1 _ (by decide)]
  have hrs : bytesAt s2.mem (VG.Proof.MlDsa.X86_64.Sign.pa s2 (sc oRS)) 32 = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ :=
    (S1.lay.keepBytes hP2 k2).trans ((L.keepBytes hP1 k1).trans h.rs)
  refine ⟨⟨⟨S2, hrs, e15 ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (e15 ▸ h0)⟩, VG.Proof.MlDsa.X86_64.Sign.seed34 hrs ?_ ?_⟩, e15⟩
  · obtain ⟨ok, fam⟩ := h.ok (e15 ▸ h1)
    exact ⟨ok, Fam.keep S1.lay hP2 f2 (Fam.keep L hP1 f1 fam)⟩
  · rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, S1.lay.keepBytes hP2 k12, hm1, hP1.pa (by decide)]; exact VG.Proof.MlDsa.X86_64.Sign.bytes1_write _ _ _
  · rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, hm2, hP2.pa (by decide)]; exact VG.Proof.MlDsa.X86_64.Sign.bytes1_write _ _ _

/-- What the call of entry `e` leaves. -/
def CallE (D : Nat) (a : Ptr) (x : List Byte) (s s' : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s a)) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT x) ((s'.gpr .rax).setWidth 32) (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s a)) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT x).isSome)

/-- Entry `e`'s call is done. -/
def JE (p : Params) (D : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s₀ ∧ VG.Proof.MlDsa.X86_64.Sign.CallE D (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) (VG.Proof.MlDsa.X86_64.Sign.seedE p σ e) s₀ s

theorem callE_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s) (hs : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS)) 34 = VG.Proof.MlDsa.X86_64.Sign.seedE p σ e) :
    WP isa (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)), .ptr (sc oPS)]) s
      (VG.Proof.MlDsa.X86_64.Sign.JE p D e σ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.eChk_spec he
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ => ⟨s, h, hP3, hcs3, hred, ?_, ?_⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem andE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.JE p D e σ s) : WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s (VG.Proof.MlDsa.X86_64.Sign.IA p D σ (e + 1)) := by
  obtain ⟨_, _, c3, c0, _, _, _, _, k3, _, _, _, f3, _, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.eChk_spec he
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := h
  have S3 := h.st.step hP3 c3
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.and15_ok s) fun s4 ⟨h15, hm4, k4⟩ => ?_
  have hP4 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s4 [] := (VG.Proof.MlDsa.X86_64.Sign.postB15 k4 hm4 _).1
  rw [hcs3 _ (by decide)] at h15
  have hr := VG.Proof.MlDsa.X86_64.Sign.outcome01 hout
  have hb4 : s4.gpr .rbx = s₀.gpr .rbx := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  refine ⟨S3.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rw [hm4, hP4.pa (by decide), h.st.lay.keepBytes hP3 k3, h.rs]
  · rw [h15]
    rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .r15 = 1 ∧ (s.gpr .rax).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := h.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, Fam.snoc ?_ ?_⟩
    · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · exact Fam.of_eq hm4 (hP4.bs _ (by decide)) (Fam.keep h.st.lay hP3 f3 fam)
    · show PolyIs s4.mem (VG.Proof.MlDsa.X86_64.Sign.pa s4 (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e))) (VG.Proof.MlDsa.X86_64.Sign.aVal p σ e)
      rw [hm4, show VG.Proof.MlDsa.X86_64.Sign.pa s4 (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) = VG.Proof.MlDsa.X86_64.Sign.pa s₀ (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) by simp only [VG.Proof.MlDsa.X86_64.Sign.pa, hb4]]
      exact ⟨hred hs.2, VG.Proof.MlDsa.X86_64.Sign.rej_val hout hs.2 hm⟩
  · rw [h15] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega, hn⟩

theorem sampleE_eq (P : Prims) (p : Params) (e : Nat) : sampleE P p e = .seq (.block (VG.Proof.MlDsa.X86_64.Sign.blkE p e))
    (.seq (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)), .ptr (sc oPS)])
      (.block [.alu32 .and .r15 (.reg .rax)])) := by
  unfold sampleE rejAt; rw [VG.Proof.MlDsa.X86_64.Sign.aP_eq]

theorem sampleE_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s) : WP isa (sampleE P p e) s (VG.Proof.MlDsa.X86_64.Sign.IA p D σ (e + 1)) := by
  rw [VG.Proof.MlDsa.X86_64.Sign.sampleE_eq]
  exact WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.blkE_ok he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.callE_ok hP he h1 hs1) fun s2 h2 => VG.Proof.MlDsa.X86_64.Sign.andE_ok he h2))

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA4`. -/
section

/-!
# ML-DSA signing on x86-64: `ExpandA`, four entries at a time

`ρ` to `RS` and to each of the four seeds at `RS4` (`IA4`); then, for each
group of four entries `4g, …, 4g + 3`, their indices to the seeds (`GS`,
`slot_ok`) and one call of `vg_mldsa_rej_ntt_poly4`, ANDed into `r15`
(`call4_ok`); then the last `kℓ mod 4` entries one at a time (`sampleE_ok`).
Each step keeps `IA` (`expandA_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `ExpandA` after `e` entries, with `ρ` in each seed of `RS4`. -/
structure IA4 (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  ia : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s
  rs4 : ∀ k < 4, bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oRS4 + 34 * k))) 32 = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ

/-- … and the seeds of entries `e, …, e + j - 1` in the first `j` seeds. -/
structure GS (p : Params) (D : Nat) (σ : State) (e j : Nat) (s : State) : Prop where
  ia4 : VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ e s
  done : ∀ k < j, bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oRS4 + 34 * k))) 34 = VG.Proof.MlDsa.X86_64.Sign.seedE p σ (e + k)

/-! ## Pieces that keep `IA` -/

theorem IA.step {p : Params} {D : Nat} {σ : State} {e : Nat} {s s' : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hst : VG.Proof.MlDsa.X86_64.Sign.stChk p ws = true) (hk : VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oRS) 32 = true)
    (hf : VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.aBase p) e = true) (e15 : s'.gpr .r15 = s.gpr .r15) : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s' := by
  refine ⟨h.st.step hP hst, (h.st.lay.keepBytes hP hk).trans h.rs, by rw [e15]; exact h.r01, fun h1 => ?_,
    fun h0 => h.bad (by rw [← e15]; exact h0)⟩
  obtain ⟨ok, fam⟩ := h.ok (by rw [← e15]; exact h1)
  exact ⟨ok, Fam.keep h.st.lay hP hf fam⟩

/-- The seeds of `RS4` apart from `ws`. -/
def rs4Chk (p : Params) (ws : List (Ptr × Nat)) (n : Nat) : Bool :=
  (List.range 4).all fun k => VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc (oRS4 + 34 * k)) n

theorem rs4Chk_spec {p : Params} {ws : List (Ptr × Nat)} {n : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.rs4Chk p ws n = true) {k : Nat}
    (hk : k < 4) : VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc (oRS4 + 34 * k)) n = true :=
  List.all_eq_true.mp h k (List.mem_range.mpr hk)

theorem IA4.step {p : Params} {D : Nat} {σ : State} {e : Nat} {s s' : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ e s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hst : VG.Proof.MlDsa.X86_64.Sign.stChk p ws = true) (hk : VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oRS) 32 = true)
    (hf : VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.aBase p) e = true) (h4 : VG.Proof.MlDsa.X86_64.Sign.rs4Chk p ws 32 = true) (e15 : s'.gpr .r15 = s.gpr .r15) :
    VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ e s' :=
  ⟨h.ia.step hP hst hk hf e15, fun k hk => (h.ia.st.lay.keepBytes hP (VG.Proof.MlDsa.X86_64.Sign.rs4Chk_spec h4 hk)).trans (h.rs4 k hk)⟩

/-! ## The seeds of a group -/

/-- What seed `j` of entry `e + j` needs of the layout. -/
def slotChk (p : Params) (e j : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(sc (oRS4 + 34 * j + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS4 + 34 * j + 33), 1)]
  VG.Proof.MlDsa.X86_64.Sign.stChk p w1 && VG.Proof.MlDsa.X86_64.Sign.stChk p w2 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS4 + 34 * j + 32)) 1 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS4 + 34 * j + 33)) 1 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (sc oRS) 32 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc oRS) 32 && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (VG.Proof.MlDsa.X86_64.Sign.aBase p) e &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (VG.Proof.MlDsa.X86_64.Sign.aBase p) e && VG.Proof.MlDsa.X86_64.Sign.rs4Chk p w1 32 && VG.Proof.MlDsa.X86_64.Sign.rs4Chk p w2 32 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc (oRS4 + 34 * j + 32)) 1 &&
    (List.range j).all (fun k => VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (sc (oRS4 + 34 * k)) 34 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc (oRS4 + 34 * k)) 34) &&
    decide ((e + j) % p.ℓ < 256) && decide ((e + j) / p.ℓ < 256)

theorem slot_ok {p : Params} {D : Nat} {σ : State} {e j : Nat} (hj4 : j < 4) (hc : VG.Proof.MlDsa.X86_64.Sign.slotChk p e j = true) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.GS p D σ e j s) : WP isa (.block (setSR p e j)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.GS p D σ e (j + 1) s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.slotChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, w1⟩, w2⟩, k1⟩, k2⟩, f1⟩, f2⟩, r1⟩, r2⟩, k12⟩, kd⟩, hj⟩, hi⟩ := hc
  have L := h.ia4.ia.st.lay
  unfold setSR
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setB_okB L (show Reg.rbx ≠ .rax by decide) hj w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have e1 : s1.gpr .r15 = s.gpr .r15 := hcs1 _ (by decide)
  have I1 := h.ia4.step hP1 c1 k1 f1 r1 e1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setB_okB I1.ia.st.lay (show Reg.rbx ≠ .rax by decide) hi w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have e2 : s2.gpr .r15 = s1.gpr .r15 := hcs2 _ (by decide)
  have I2 := I1.step hP2 c2 k2 f2 r2 e2
  refine ⟨⟨I2, fun k hk => ?_⟩, e2.trans e1⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · have kk := List.all_eq_true.mp kd k (List.mem_range.mpr hk')
    simp only [Bool.and_eq_true] at kk
    rw [I1.ia.st.lay.keepBytes hP2 kk.2, L.keepBytes hP1 kk.1]
    exact h.done k hk'
  · refine VG.Proof.MlDsa.X86_64.Sign.seed34 (I2.rs4 k (by omega)) ?_ ?_
    · rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, I1.ia.st.lay.keepBytes hP2 k12, hm1, hP1.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Sign.bases by decide)]; exact VG.Proof.MlDsa.X86_64.Sign.bytes1_write _ _ _
    · rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, hm2, hP2.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Sign.bases by decide)]; exact VG.Proof.MlDsa.X86_64.Sign.bytes1_write _ _ _

/-! ## The call -/

theorem pa_poly4 (s : State) (i k : Nat) : poly4 (VG.Proof.MlDsa.X86_64.Sign.pa s (pS i)) k = VG.Proof.MlDsa.X86_64.Sign.pa s (pS (i + k)) := by
  unfold poly4
  rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, show VG.Impl.MlDsa.X86_64.Sign.oP i + 1024 * k = VG.Impl.MlDsa.X86_64.Sign.oP (i + k) by simp only [VG.Impl.MlDsa.X86_64.Sign.oP]; omega]

theorem seed4_eq {p : Params} {D : Nat} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.GS p D σ e 4 s) {k : Nat}
    (hk : k < 4) : seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS4)) k = VG.Proof.MlDsa.X86_64.Sign.seedE p σ (e + k) := by
  unfold seed4
  rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc_add]; exact h.done k hk

/-- What the call of a group needs of the layout. -/
def callChk (p : Params) (e : Nat) : Bool :=
  let w3 : List (Ptr × Nat) := [(pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e), 4096), (r4P p, 8192)]
  VG.Proof.MlDsa.X86_64.Sign.stChk p w3 && VG.Proof.MlDsa.X86_64.Sign.stChk p [] && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (sc oRS) 32 && VG.Proof.MlDsa.X86_64.Sign.rs4Chk p w3 32 && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (VG.Proof.MlDsa.X86_64.Sign.aBase p) e &&
    VG.Proof.MlDsa.X86_64.Sign.rej4Chk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) (r4P p)

/-- What the call of group `e` leaves. -/
abbrev R4Post (D : Nat) (a w : Ptr) (s s' : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(a, 4096), (w, 8192)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, Reduced s'.mem (poly4 (VG.Proof.MlDsa.X86_64.Sign.pa s a) k)) ∧
    (((s'.gpr .rax).setWidth 32 = 1 ∧ ∀ k < 4, ∃ b : Bounds,
        rejNTTPoly b.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS4)) k) = some (polyAt s'.mem (poly4 (VG.Proof.MlDsa.X86_64.Sign.pa s a) k))) ∨
      ((s'.gpr .rax).setWidth 32 = 0 ∧ ∃ k < 4,
        rejNTTPoly minBounds.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS4)) k) = none)) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4,
      (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS4)) k)).isSome)

/-- The call of group `e` is done. -/
def J4 (p : Params) (D e : Nat) (σ s : State) : Prop :=
  ∃ s₀, VG.Proof.MlDsa.X86_64.Sign.GS p D σ e 4 s₀ ∧ VG.Proof.MlDsa.X86_64.Sign.R4Post D (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) (r4P p) s₀ s

theorem callG_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.callChk p e = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.GS p D σ e 4 s) :
    WP isa (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (sc oRS4), .ptr (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)), .ptr (r4P p)]) s
      fun s' => VG.Proof.MlDsa.X86_64.Sign.J4 p D e σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.callChk, Bool.and_eq_true] at hc
  exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.rej4Call_ok hP h.ia4.ia.st.lay hc.2) fun s' h' => ⟨⟨s, h, h'⟩, h'.2.1 _ (by decide)⟩

theorem and4_ok {p : Params} {D : Nat} {σ : State} {e : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.callChk p e = true) {s : State}
    (hJ : VG.Proof.MlDsa.X86_64.Sign.J4 p D e σ s) : WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s (VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (e + 4)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.callChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c3, c0⟩, k3⟩, r3⟩, f3⟩, _⟩ := hc
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := hJ
  have L := h.ia4.ia.st.lay
  have I1 := h.ia4.step hP3 c3 k3 f3 r3 (hcs3 _ (by decide))
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.and15_ok s) fun s4 ⟨h15, hm4, k4⟩ => ?_
  have hP4 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s4 [] := (VG.Proof.MlDsa.X86_64.Sign.postB15 k4 hm4 _).1
  rw [hcs3 _ (by decide)] at h15
  have hr : (s.gpr .rax).setWidth 32 = 1 ∨ (s.gpr .rax).setWidth 32 = 0 := by
    rcases hout with ⟨h1, _⟩ | ⟨h0, _⟩
    exacts [.inl h1, .inr h0]
  have hb4 : s4.gpr .rbx = s₀.gpr .rbx := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  have epa : ∀ q : Ptr, q.1 = .rbx → VG.Proof.MlDsa.X86_64.Sign.pa s4 q = VG.Proof.MlDsa.X86_64.Sign.pa s₀ q := fun q hq => by simp only [VG.Proof.MlDsa.X86_64.Sign.pa, hq, hb4]
  have hia := h.ia4.ia
  refine ⟨⟨I1.ia.st.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩, fun k hk => ?_⟩
  · rw [hm4, epa _ rfl, ← hP3.pa (by decide), I1.ia.rs]
  · rw [h15]
    rcases hia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .r15 = 1 ∧ (s.gpr .rax).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases hia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := hia.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, fun j hj => ?_⟩
    · by_cases he'' : e' < e
      · exact ok1 e' he''
      · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ e' = e + k := ⟨e' - e, by omega, by omega⟩
        rw [← VG.Proof.MlDsa.X86_64.Sign.seed4_eq h hk]; exact hm k hk
    · by_cases hj' : j < e
      · exact Fam.of_eq hm4 (hP4.bs _ (by decide)) (Fam.keep L hP3 f3 fam) j hj'
      · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ j = e + k := ⟨j - e, by omega, by omega⟩
        show PolyIs s4.mem (VG.Proof.MlDsa.X86_64.Sign.pa s4 (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + (e + k)))) (VG.Proof.MlDsa.X86_64.Sign.aVal p σ (e + k))
        rw [hm4, epa _ rfl, ← Nat.add_assoc, ← VG.Proof.MlDsa.X86_64.Sign.pa_poly4]
        rcases hout with ⟨_, hb⟩ | ⟨h0, _⟩
        · refine ⟨hred hs.2 k hk, ?_⟩
          have := VG.Proof.MlDsa.X86_64.Sign.rej_val (x := seed4 s₀.mem (VG.Proof.MlDsa.X86_64.Sign.pa s₀ (sc oRS4)) k) (.inl ⟨hs.2, hb k hk⟩) hs.2 (hm k hk)
          rw [this, VG.Proof.MlDsa.X86_64.Sign.seed4_eq h hk]; rfl
        · rw [hs.2] at h0; cases h0
  · rw [h15] at h0
    rcases hia.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := hia.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, k, hk, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e + k, by omega, by rw [← VG.Proof.MlDsa.X86_64.Sign.seed4_eq h hk]; exact hn⟩
  · rw [hm4, epa _ rfl, ← hP3.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Sign.bases by decide)]; exact I1.rs4 k hk

theorem call4_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.callChk p e = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.GS p D σ e 4 s) :
    WP isa (rej4At P (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) (r4P p)) s (VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (e + 4)) := by
  unfold rej4At
  exact WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.callG_ok hP hc h) fun _ h' => VG.Proof.MlDsa.X86_64.Sign.and4_ok hc h'.1)

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, VG.Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl,
    VG.Proof.MlKem.bytesAt_add, show 68 = 34 + 34 from rfl, VG.Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds of a group, from `ρ`. -/
theorem GS.seeds {p : Params} {D : Nat} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.GS p D σ e 4 s) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS4)) 136 = aSeed (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      aSeed (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ aSeed (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      aSeed (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS4) + BitVec.ofNat 64 (34 * k)) 34 = VG.Proof.MlDsa.X86_64.Sign.seedE p σ (e + k) :=
    fun k hk => VG.Proof.MlDsa.X86_64.Sign.seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, BitVec.add_zero] at b0
  rw [VG.Proof.MlDsa.X86_64.Sign.bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-- What a group needs of the layout. -/
def g4Chk (p : Params) (e : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.slotChk p e 0 && VG.Proof.MlDsa.X86_64.Sign.slotChk p e 1 && VG.Proof.MlDsa.X86_64.Sign.slotChk p e 2 && VG.Proof.MlDsa.X86_64.Sign.slotChk p e 3 && VG.Proof.MlDsa.X86_64.Sign.callChk p e

theorem sample4_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.g4Chk p (4 * g) = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (4 * g) s) :
    WP isa (sample4 P p g) s (VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (4 * g + 4)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.g4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, cc⟩ := hc
  unfold sample4
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.slot_ok (by decide) s0 (j := 0) ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x0 h0 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.slot_ok (by decide) s1 h0.1) fun x1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.slot_ok (by decide) s2 h1.1) fun x2 h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.slot_ok (by decide) s3 h2.1) fun x3 h3 => ?_)
  exact VG.Proof.MlDsa.X86_64.Sign.call4_ok hP cc h3.1

/-! ## The matrix -/

/-- `ρ` to `sc o`. -/
theorem copyRho_ok {p : Params} {D : Nat} {σ : State} {o : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc o) (.rbp, 0) 32 = true) (hst : VG.Proof.MlDsa.X86_64.Sign.stChk p [(sc o, 32)] = true) (hsk : 32 ≤ p.skLen)
    {s : State} (hs : VG.Proof.MlDsa.X86_64.Sign.St p D σ s) :
    WP isa (copy (sc o) (.rbp, 0) 32) s fun s' => VG.Proof.MlDsa.X86_64.Sign.St p D σ s' ∧ VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(sc o, 32)] ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' (sc o)) 32 = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ ∧ s'.gpr .r15 = s.gpr .r15 :=
  WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB hs.lay hc) fun _ ⟨hP1, hcs1, hb⟩ => ⟨hs.step hP1 hst, hP1,
    by rw [hP1.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Sign.bases by decide), hb, VG.Proof.MlDsa.X86_64.Sign.rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk], hcs1 _ (by decide)⟩

/-- After `ρ` to `RS` and to the first `j` seeds of `RS4`. -/
structure ICopy (p : Params) (D : Nat) (σ : State) (j : Nat) (s : State) : Prop where
  st : VG.Proof.MlDsa.X86_64.Sign.St p D σ s
  rs : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS)) 32 = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ
  rs4 : ∀ k < j, bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oRS4 + 34 * k))) 32 = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ
  r15 : s.gpr .r15 = 1

/-- What the copy of `ρ` to seed `j` of `RS4` needs of the layout. -/
def cpChk (p : Params) (j : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oRS4 + 34 * j)) (.rbp, 0) 32 && VG.Proof.MlDsa.X86_64.Sign.stChk p [(sc (oRS4 + 34 * j), 32)] &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS4 + 34 * j), 32)] (sc oRS) 32 &&
    (List.range j).all fun k => VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc (oRS4 + 34 * j), 32)] (sc (oRS4 + 34 * k)) 32

theorem cpR4_ok {p : Params} {D : Nat} {σ : State} {j : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.cpChk p j = true) (hsk : 32 ≤ p.skLen) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ j s) : WP isa (cpR4 j) s (VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ (j + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.cpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hcp, hst⟩, k0⟩, kk⟩ := hc
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.copyRho_ok hcp hst hsk h.st) fun s1 ⟨S1, hP1, hb, e15⟩ =>
    ⟨S1, (h.st.lay.keepBytes hP1 k0).trans h.rs, fun k hk => ?_, e15.trans h.r15⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · exact (h.st.lay.keepBytes hP1 (List.all_eq_true.mp kk k (List.mem_range.mpr hk'))).trans (h.rs4 k hk')
  · exact hb

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (VG.Proof.MlDsa.X86_64.Sign.eChk p) && VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oRS) (.rbp, 0) 32 &&
    VG.Proof.MlDsa.X86_64.Sign.stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen) && (List.range 4).all (VG.Proof.MlDsa.X86_64.Sign.cpChk p) &&
    (List.range (p.k * p.ℓ / 4)).all fun g => VG.Proof.MlDsa.X86_64.Sign.g4Chk p (4 * g)

theorem aChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ICopy.ia4 {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ 4 s) : VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ 0 s :=
  ⟨⟨h.st, h.rs, .inr h.r15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans h.r15) (by decide)⟩, h.rs4⟩

theorem expandA_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.aChk p = true) {σ s : State}
    (hs : VG.Proof.MlDsa.X86_64.Sign.St p D σ s) (h15 : s.gpr .r15 = 1) : WP isa (Impl.MlDsa.X86_64.Sign.expandA P p) s (VG.Proof.MlDsa.X86_64.Sign.IA p D σ (p.k * p.ℓ)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩, hc4⟩, hg⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.copyRho_ok hcp hst hsk hs) fun s1 ⟨S1, _, hb, e15⟩ => ?_)
  have I0 : VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ 0 s1 := ⟨S1, hb, fun _ h => absurd h (Nat.not_lt_zero _), e15.trans h15⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (f := cpR4) (I := VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ) 4 0
    (fun k _ hk s h => VG.Proof.MlDsa.X86_64.Sign.cpR4_ok (hc4 k (by omega)) hsk h) s1 I0) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (f := sample4 P p) (I := fun g => VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (4 * g)) (p.k * p.ℓ / 4) 0
    (fun g _ hg' s h => VG.Proof.MlDsa.X86_64.Sign.sample4_ok hP (hg g (by omega)) h) s2 h2.ia4) fun s3 h3 => ?_)
  have := VG.Proof.MlDsa.X86_64.Sign.seqR_ok (f := sampleE P p) (I := VG.Proof.MlDsa.X86_64.Sign.IA p D σ) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    (fun k h1 hk s h => VG.Proof.MlDsa.X86_64.Sign.sampleE_ok hP (he k (by omega)) h) s3 (by rw [Nat.zero_add] at h3; exact h3.ia)
  rwa [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega] at this

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsC`. -/
section

/-!
# ML-DSA signing on x86-64: calls of rounding, norms, hints and packing

As `Prims.lean`, for `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint`, `vg_mldsa_simple_bit_pack`,
`vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_hint_bit_pack`.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call with a polynomial `f` read and a buffer `out` of `l` bytes
written needs of the layout. -/
def rwChk (bs wbs : List (Reg × Nat)) (f : VG.Impl.MlDsa.X86_64.Sign.Ptr) (lf : Nat) (out : VG.Impl.MlDsa.X86_64.Sign.Ptr) (l : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs out l && VG.Proof.MlDsa.X86_64.Sign.inB bs f lf && VG.Proof.MlDsa.X86_64.Sign.inB bs out l && VG.Proof.MlDsa.X86_64.Sign.sepB bs f lf out l && decide (f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) &&
    decide (f.2 < 2 ^ 31) && decide (out.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (out.2 < 2 ^ 31)

theorem rwChk_spec {bs wbs : List (Reg × Nat)} {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {lf l : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk bs wbs f lf out l = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs out l = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs f lf = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs out l = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs f lf out l = true ∧
      f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ f.2 < 2 ^ 31 ∧ out.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ out.2 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.rwChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## `HighBits` and `LowBits` -/

theorem gamma2_lt {γ : Nat} (h : γ ∈ gamma2s) : γ < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

theorem bitsArgs_ok {bs : List (Reg × Nat)} {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk bs wbs r 1024 out 1024 = true) :
    [Arg.ptr r, .imm γ, .ptr out].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true (VG.Proof.MlDsa.X86_64.Sign.gamma2_lt hγ)]

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q`. -/
abbrev bitsC (Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract X86_64.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

theorem bitsPre {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State}
    (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr r, .imm γ, .ptr out] s s1)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) :
    (VG.Proof.MlDsa.X86_64.Sign.bitsC Q S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s out)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s out)]
  sig_pre [bitsSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat (VG.Proof.MlDsa.X86_64.Sign.gamma2_lt hγ)]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hγ, A.red' i1 hD hr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s r), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s out)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bitsAt_ok {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => VG.Proof.MlDsa.X86_64.Sign.bitsC Q S) D c) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) :
    WP isa (callP n c [.ptr r, .imm γ, .ptr out]) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ Q γ (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s out) := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok C.ver.1 C.nosp C.depth L.dsm (VG.Proof.MlDsa.X86_64.Sign.bitsArgs_ok hγ hc)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.bitsPre C.hS (At.of L hm k) hγ hc hA hr)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hA
  sig_post [bitsSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i1 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat (VG.Proof.MlDsa.X86_64.Sign.gamma2_lt hγ)] at hq
  exact hq

theorem bitsAt_tr {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.X86_64.Sign.Callee (fun S => VG.Proof.MlDsa.X86_64.Sign.bitsC Q S) D c) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y r))
      (callP n c [.ptr r, .imm γ, .ptr out]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr C.ver.1 C.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.bitsArgs_ok hγ hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.bitsPre C.hS (At.of R.lx hmx kx) hγ hc hAx rx, VG.Proof.MlDsa.X86_64.Sign.bitsPre C.hS (At.of R.ly hmy ky) hγ hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn3 hAy
  sig_pub [bitsSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem highBitsAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      NatPolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s out) ((polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)).map fun c => (highBits γ c).toNat) :=
  VG.Proof.MlDsa.X86_64.Sign.bitsAt_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits L hγ hc hr

theorem highBitsAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Sign.bitsAt_tr (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits hγ hc

theorem lowBitsAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s out) ((polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)).map fun c => ofInt (lowBits γ c)) :=
  VG.Proof.MlDsa.X86_64.Sign.bitsAt_ok (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits L hγ hc hr

theorem lowBitsAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {r out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y r))
      (lowBitsAt P r γ out) fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Sign.bitsAt_tr (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits hγ hc

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
def normChk (bs : List (Reg × Nat)) (f : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB bs f 1024 && decide (f.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (f.2 < 2 ^ 31)

theorem normPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {B : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.normChk (rbs ++ wbs) f = true) (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr f, .imm B] s s1)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) :
    (normLtContract X86_64.abi S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] []) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨i1, _⟩, _⟩ := hc
  obtain ⟨e1, e2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 32]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] []
  sig_pre [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, Arg.val]
  refine ⟨hwf, trivial, ?_, A.L.nwp i1, A.red' i1 hD hr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i1 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  exact A.stk hS i1

theorem normArgs_ok {bs : List (Reg × Nat)} {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.X86_64.Sign.normChk bs f = true) :
    [Arg.ptr f, .imm B].all Arg.ok = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [List.all_cons, List.all_nil, Arg.ok, hc.1.2, hc.2, decide_true, Bool.and_true, decide_eq_true hB]

theorem normCall_ok {nm : String} {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.X86_64.Sign.normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) :
    WP isa (callP nm P.normLt [.ptr f, .imm B]) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (s'.gpr .rax).setWidth 32 = if normRq [polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)] < B then 1 else 0 := by
  have i1 : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) f 1024 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Sign.normChk, Bool.and_eq_true] at hc; exact hc.1.1
  have hD : 8 ≤ D := by have := hP.normLt.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.normLt.ver.1 hP.normLt.nosp hP.normLt.depth L.dsm (VG.Proof.MlDsa.X86_64.Sign.normArgs_ok hB hc)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.normPre hP.normLt.hS (At.of L hm k) hc hA hr)
    (Covers.append_left (L.cR i1) Covers.nil) Covers.nil)
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, er, A.poly' i1 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hB] at hq
  exact hq

theorem normCall_tr {nm : String} {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : VG.Proof.MlDsa.X86_64.Sign.normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f))
      (callP nm P.normLt [.ptr f, .imm B]) fun _ _ => True := by
  have i1 : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) f 1024 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Sign.normChk, Bool.and_eq_true] at hc; exact hc.1.1
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.normLt.ver.1 hP.normLt.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.normArgs_ok hB hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.normPre hP.normLt.hS (At.of R.lx hmx kx) hc hAx rx,
        VG.Proof.MlDsa.X86_64.Sign.normPre hP.normLt.hS (At.of R.ly hmy ky) hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) Covers.nil, Covers.nil,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) Covers.nil, Covers.nil,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn2 hAy
  sig_pub [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp,
    and_self]

/-! ## `MakeHint` -/

/-- What a call of `vg_mldsa_make_hint` on `z`, `r` to `h` needs of the layout. -/
def hintChk (bs wbs : List (Reg × Nat)) (z r h : VG.Impl.MlDsa.X86_64.Sign.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB wbs h 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs z 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs r 1024 && VG.Proof.MlDsa.X86_64.Sign.inB bs h 1024 && VG.Proof.MlDsa.X86_64.Sign.sepB bs z 1024 h 1024 &&
    VG.Proof.MlDsa.X86_64.Sign.sepB bs r 1024 h 1024 && decide (z.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (z.2 < 2 ^ 31) && decide (r.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) &&
    decide (r.2 < 2 ^ 31) && decide (h.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases) && decide (h.2 < 2 ^ 31)

theorem hintChk_spec {bs wbs : List (Reg × Nat)} {z r h : VG.Impl.MlDsa.X86_64.Sign.Ptr} (hc : VG.Proof.MlDsa.X86_64.Sign.hintChk bs wbs z r h = true) :
    VG.Proof.MlDsa.X86_64.Sign.inB wbs h 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs z 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs r 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB bs h 1024 = true ∧
      VG.Proof.MlDsa.X86_64.Sign.sepB bs z 1024 h 1024 = true ∧ VG.Proof.MlDsa.X86_64.Sign.sepB bs r 1024 h 1024 = true ∧ z.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ z.2 < 2 ^ 31 ∧
      r.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ r.2 < 2 ^ 31 ∧ h.1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases ∧ h.2 < 2 ^ 31 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem hintArgs_ok {bs : List (Reg × Nat)} {z r h : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.hintChk bs wbs z r h = true) :
    [Arg.ptr z, .ptr r, .imm γ, .ptr h].all Arg.ok = true := by
  obtain ⟨_, _, _, _, _, _, b1, o1, b2, o2, b3, o3⟩ := VG.Proof.MlDsa.X86_64.Sign.hintChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, b3, o3, decide_true, Bool.and_true,
    decide_eq_true (VG.Proof.MlDsa.X86_64.Sign.gamma2_lt hγ)]

theorem hintPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {z r h : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.hintChk (rbs ++ wbs) wbs z r h = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr z, .ptr r, .imm γ, .ptr h] s s1) (rz : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s z))
    (rr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) :
    (makeHintContract X86_64.abi S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d13, d23, _⟩ := VG.Proof.MlDsa.X86_64.Sign.hintChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s r)]
    [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)]
  sig_pre [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat (VG.Proof.MlDsa.X86_64.Sign.gamma2_lt hγ)]
  refine ⟨hwf, trivial, trivial, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, hγ, A.red' i1 hD rz, A.red' i2 hD rr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s r), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s h)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem hintCall_ok {nm : String} {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {z r h : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.X86_64.Sign.hintChk (rbs ++ wbs) wbs z r h = true) (rz : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s z))
    (rr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r)) :
    WP isa (callP nm P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(h, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      HintIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h) 1 [Vector.zipWith (makeHint γ) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r))] ∧
      ((s'.gpr .rax).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint γ) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s r))] := by
  obtain ⟨w1, i1, i2, i3, _⟩ := VG.Proof.MlDsa.X86_64.Sign.hintChk_spec hc
  have hD : 8 ≤ D := by have := hP.makeHint.hS; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.makeHint.ver.1 hP.makeHint.nosp hP.makeHint.depth L.dsm (VG.Proof.MlDsa.X86_64.Sign.hintArgs_ok hγ hc)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.hintPre hP.makeHint.hS (At.of L hm k) hγ hc hA rz rr)
    (Covers.append_left (Covers.cons (L.cR i1) (L.cR i2)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, er, A.poly' i1 hD, A.poly' i2 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat (VG.Proof.MlDsa.X86_64.Sign.gamma2_lt hγ)] at hq
  exact hq

theorem hintCall_tr {nm : String} {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {z r h : VG.Impl.MlDsa.X86_64.Sign.Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Sign.hintChk (rbs ++ wbs) wbs z r h = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x z) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x r)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y z) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y r)))
      (callP nm P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _⟩ := VG.Proof.MlDsa.X86_64.Sign.hintChk_spec hc
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.makeHint.ver.1 hP.makeHint.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.hintArgs_ok hγ hc)
    fun x y x1 y1 ⟨R, ⟨rzx, rrx⟩, ⟨rzy, rry⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.hintPre hP.makeHint.hS (At.of R.lx hmx kx) hγ hc hAx rzx rrx,
        VG.Proof.MlDsa.X86_64.Sign.hintPre hP.makeHint.hS (At.of R.ly hmy ky) hγ hc hAy rzy rry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (Covers.cons (R.lx.cR i1) (R.lx.cR i2)) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (Covers.cons (R.ly.cR i1) (R.ly.cR i2)) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAy
  sig_pub [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsD`. -/
section

/-!
# ML-DSA signing on x86-64: calls of the packing primitives

As `Prims.lean`, for `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`,
`vg_mldsa_bit_unpack` and `vg_mldsa_hint_bit_pack` (which may leak the hint:
two runs leak the same when their hints agree, `hbpAt_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `SimpleBitPack` -/

theorem sbpArgs_ok {bs : List (Reg × Nat)} {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {b len : Nat} (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk bs wbs f 1024 out len = true) : [Arg.ptr f, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true hb, decide_eq_true hl]

theorem sbpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr f, .imm b, .ptr out, .imm len] s s1)
    (hle : ∀ i < 256, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) i).toNat ≤ b) :
    (simpleBitPackContract X86_64.abi S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s out, len⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s out, len⟩]
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hb'.1, VG.Proof.MlDsa.X86_64.Sign.toNat64 hb'.2]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hb, hl,
    fun i hi => by rw [A.coeff' i1 hD hi]; exact hle i hi⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s out, len⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem sbpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s out) len = simpleBitPack (natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) b := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.simpleBitPack.hS; omega
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.simpleBitPack.ver.1 hP.simpleBitPack.nosp hP.simpleBitPack.depth L.dsm
    (VG.Proof.MlDsa.X86_64.Sign.sbpArgs_ok hb'.1 hb'.2 hc) (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.sbpPre hP.simpleBitPack.hS (At.of L hm k) hb hl hc hA hle)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hA
  sig_post [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, A.natPoly' i1 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hb'.1, VG.Proof.MlDsa.X86_64.Sign.toNat64 hb'.2] at hq
  exact hq

theorem sbpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.simpleBitPack.ver.1 hP.simpleBitPack.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.sbpArgs_ok hb'.1 hb'.2 hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.sbpPre hP.simpleBitPack.hS (At.of R.lx hmx kx) hb hl hc hAx rx,
        VG.Proof.MlDsa.X86_64.Sign.sbpPre hP.simpleBitPack.hS (At.of R.ly hmy ky) hb hl hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn4 hAy
  sig_pub [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `BitPack` -/

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpArgs_ok {bs : List (Reg × Nat)} {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk bs wbs f 1024 out len = true) : [Arg.ptr f, .imm a, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true ha, decide_eq_true hb, decide_eq_true hl]

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
def InRange (m : Mem) (p : Addr) (a b : Nat) : Prop :=
  ∀ i < 256, -(a : Int) ≤ modPm (coeffAt m p i).toNat q ∧ modPm (coeffAt m p i).toNat q ≤ b

theorem bpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr f, .imm a, .imm b, .ptr out, .imm len] s s1) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f))
    (hrg : VG.Proof.MlDsa.X86_64.Sign.InRange s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) a b) :
    (bitPackContract X86_64.abi S).pre (s1.callEntry.withRegions [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s out, len⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  have hD : 8 ≤ D := by omega
  obtain ⟨ha', hb', hl'⟩ := VG.Proof.MlDsa.X86_64.Sign.bitPackParams_lt hp
  rw [← hl] at hl'
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 32, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s out, len⟩]
  sig_pre [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat ha', VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hb', VG.Proof.MlDsa.X86_64.Sign.toNat64 hl']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, hl, A.red' i1 hD hr,
    fun i hi => by rw [A.coeff' i1 hD hi]; exact hrg i hi⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f), ⟨VG.Proof.MlDsa.X86_64.Sign.pa s out, len⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) (hrg : VG.Proof.MlDsa.X86_64.Sign.InRange s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s out) len = bitPack ((polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)).map fun c => modPm c.val q) a b := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.bitPack.hS; omega
  obtain ⟨ha', hb', hl'⟩ := VG.Proof.MlDsa.X86_64.Sign.bitPackParams_lt hp
  rw [← hl] at hl'
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.bitPack.ver.1 hP.bitPack.nosp hP.bitPack.depth L.dsm (VG.Proof.MlDsa.X86_64.Sign.bpArgs_ok ha' hb' hl' hc)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.bpPre hP.bitPack.hS (At.of L hm k) hp hl hc hA hr hrg)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  sig_post [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, e5, Arg.val, hm₂, A.poly' i1 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat ha', VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hb', VG.Proof.MlDsa.X86_64.Sign.toNat64 hl'] at hq
  exact hq

theorem bpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {f out : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ VG.Proof.MlDsa.X86_64.Sign.InRange x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) a b) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) ∧ VG.Proof.MlDsa.X86_64.Sign.InRange y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl'⟩ := VG.Proof.MlDsa.X86_64.Sign.bitPackParams_lt hp
  rw [← hl] at hl'
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.bitPack.ver.1 hP.bitPack.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.bpArgs_ok ha' hb' hl' hc)
    fun x y x1 y1 ⟨R, ⟨rx, gx⟩, ⟨ry, gy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.bpPre hP.bitPack.hS (At.of R.lx hmx kx) hp hl hc hAx rx gx,
        VG.Proof.MlDsa.X86_64.Sign.bpPre hP.bitPack.hS (At.of R.ly hmy ky) hp hl hc hAy ry gy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAy
  sig_pub [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `BitUnpack` -/

theorem bupArgs_ok {bs : List (Reg × Nat)} {v f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk bs wbs v len f 1024 = true) : [Arg.ptr v, .imm len, .imm a, .imm b, .ptr f].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true ha, decide_eq_true hb, decide_eq_true hl]

theorem bupPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {v f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs v len f 1024 = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr v, .imm len, .imm a, .imm b, .ptr f] s s1) :
    (bitUnpackContract X86_64.abi S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s v, len⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  have hD : 8 ≤ D := by omega
  obtain ⟨ha', hb', hl'⟩ := VG.Proof.MlDsa.X86_64.Sign.bitPackParams_lt hp
  rw [← hl] at hl'
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 32, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s v, len⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)]
  sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat ha', VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hb', VG.Proof.MlDsa.X86_64.Sign.toNat64 hl']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, hl⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s v, len⟩, VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.X86_64.Sign.pa s f)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bupAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {v f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(f, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f) (toRq (bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s v) len) a b)) := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.bitUnpack.hS; omega
  obtain ⟨ha', hb', hl'⟩ := VG.Proof.MlDsa.X86_64.Sign.bitPackParams_lt hp
  rw [← hl] at hl'
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.bitUnpack.ver.1 hP.bitUnpack.nosp hP.bitUnpack.depth L.dsm (VG.Proof.MlDsa.X86_64.Sign.bupArgs_ok ha' hb' hl' hc)
    (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.bupPre hP.bitUnpack.hS (At.of L hm k) hp hl hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  sig_post [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, e5, Arg.val, hm₂, A.bytes' i1 hD, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat ha', VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat hb', VG.Proof.MlDsa.X86_64.Sign.toNat64 hl'] at hq
  exact hq

theorem bupAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {v f : VG.Impl.MlDsa.X86_64.Sign.Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl'⟩ := VG.Proof.MlDsa.X86_64.Sign.bitPackParams_lt hp
  rw [← hl] at hl'
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.bitUnpack.ver.1 hP.bitUnpack.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.bupArgs_ok ha' hb' hl' hc)
    fun x y x1 y1 R ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.bupPre hP.bitUnpack.hS (At.of R.lx hmx kx) hp hl hc hAx,
        VG.Proof.MlDsa.X86_64.Sign.bupPre hP.bitUnpack.hS (At.of R.ly hmy ky) hp hl hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAy
  sig_pub [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `HintBitPack` -/

theorem hbpArgs_ok {bs : List (Reg × Nat)} {h y : VG.Impl.MlDsa.X86_64.Sign.Ptr} {hlen ω len : Nat} (h1 : hlen < 2 ^ 32) (h2 : ω < 2 ^ 32) (h3 : len < 2 ^ 32)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk bs wbs h (hlen * 4) y len = true) :
    [Arg.ptr h, .imm hlen, .imm ω, .ptr y, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true h1, decide_eq_true h2, decide_eq_true h3]

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : VG.Proof.MlDsa.X86_64.Sign.At D rbs wbs s s1) {h y : VG.Impl.MlDsa.X86_64.Sign.Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hA : VG.Proof.MlDsa.X86_64.Sign.ArgsIn [.ptr h, .imm (256 * k), .imm ω, .ptr y, .imm (ω + k)] s s1)
    (hones : hintOnes (hintAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h) k) ≤ ω) :
    (hintBitPackContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Sign.pa s h, 256 * k * 4⟩] [⟨VG.Proof.MlDsa.X86_64.Sign.pa s y, ω + k⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  have hD : 8 ≤ D := by omega
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.X86_64.Sign.hintParams_lt hp
  have hwf := VG.Proof.MlDsa.X86_64.Sign.ce_wfS (ws := [64, 64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨VG.Proof.MlDsa.X86_64.Sign.pa s h, 256 * k * 4⟩]
    [⟨VG.Proof.MlDsa.X86_64.Sign.pa s y, ω + k⟩]
  have ek : ω + k - ω = k := by omega
  have i1' : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  sig_pre [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat h1, VG.Proof.MlDsa.X86_64.Sign.toNat64 h2, VG.Proof.MlDsa.X86_64.Sign.toNat64 h3, ek]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, by omega, trivial,
    by rw [A.hint i1' hD]; exact hones⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, VG.Proof.MlDsa.X86_64.Sign.conj_stk [⟨VG.Proof.MlDsa.X86_64.Sign.pa s h, 256 * k * 4⟩, ⟨VG.Proof.MlDsa.X86_64.Sign.pa s y, ω + k⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem hbpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {h y : VG.Impl.MlDsa.X86_64.Sign.Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(y, ω + k)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s y) (ω + k) = hintBitPack ω k (hintAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s h) k) := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.hintBitPack.hS; omega
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.X86_64.Sign.hintParams_lt hp
  have ek : ω + k - ω = k := by omega
  have i1' : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.callP_ok hP.hintBitPack.ver.1 hP.hintBitPack.nosp hP.hintBitPack.depth L.dsm
    (VG.Proof.MlDsa.X86_64.Sign.hbpArgs_ok h3 h1 h2 hc) (fun s1 hA hm k => VG.Proof.MlDsa.X86_64.Sign.hbpPre hP.hintBitPack.hS (At.of L hm k) hp hc hA hones)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k', s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k'
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hA
  sig_post [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e3, e4, e5, Arg.val, hm₂, VG.Proof.MlDsa.X86_64.Sign.sw32_ofNat h1, VG.Proof.MlDsa.X86_64.Sign.toNat64 h2, ek, A.hint i1' hD] at hq
  exact hq

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {h y : VG.Impl.MlDsa.X86_64.Sign.Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : VG.Proof.MlDsa.X86_64.Sign.rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => VG.Proof.MlDsa.X86_64.Sign.LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (VG.Proof.MlDsa.X86_64.Sign.pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (VG.Proof.MlDsa.X86_64.Sign.pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.hintBitPack.hS; omega
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.X86_64.Sign.hintParams_lt hp
  refine VG.Proof.MlDsa.X86_64.Sign.callP_tr hP.hintBitPack.ver.1 hP.hintBitPack.ver.2.1 (VG.Proof.MlDsa.X86_64.Sign.hbpArgs_ok h3 h1 h2 hc)
    fun x z x1 z1 ⟨R, ox, oz, hl⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAz, hmz⟩, kz⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Sign.hbpPre hP.hintBitPack.hS (At.of R.lx hmx kx) hp hc hAx ox,
        VG.Proof.MlDsa.X86_64.Sign.hbpPre hP.hintBitPack.hS (At.of R.ly hmz kz) hp hc hAz oz, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [kz.2.1, kz.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [kz.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmz kz).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAx
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := VG.Proof.MlDsa.X86_64.Sign.argsIn5 hAz
  have Ax := At.of R.lx hmx kx
  have Az := At.of R.ly hmz kz
  sig_pub [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hz1, hz2, hz3, hz4, hz5, Arg.val, VG.Proof.MlDsa.X86_64.Sign.toNat64 h3, Ax.coeffs (len := 256 * k) i1 hD,
    Az.coeffs (len := 256 * k) i1 hD, hl]
  simp only [Ax.rsp, Az.rsp, R.rsp, R.pa i1, R.pa i2, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseD`. -/
section

/-!
# ML-DSA signing on x86-64: the private key and `ρ″`

Once `Â` is sampled (`IM`), `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`dec_ok`), in their slots (`ID`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` at `MS` (`decode_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1Base : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2Base : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0Base : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]` of the function entered in `σ`. -/
abbrev S1v (σ : State) (r : Nat) : Poly := s1F p (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : Poly := s2F p (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : Poly := t0F p (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := H (((VG.Proof.MlDsa.X86_64.Sign.skOf p σ).drop 32).take 32 ++ VG.Proof.MlDsa.X86_64.Sign.rndOf σ ++ VG.Proof.MlDsa.X86_64.Sign.muOf σ) 64

end

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (D : Nat) (σ s : State) : Prop where
  st : VG.Proof.MlDsa.X86_64.Sign.St p D σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.seedE p σ e)).isSome
  A : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.aBase p) (p.k * p.ℓ) (VG.Proof.MlDsa.X86_64.Sign.aVal p σ)

def imChk (p : Params) (ws : List (Ptr × Nat)) : Bool := VG.Proof.MlDsa.X86_64.Sign.stChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.aBase p) (p.k * p.ℓ)

theorem IM.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.X86_64.Sign.IM p D σ s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.imChk p ws = true) : VG.Proof.MlDsa.X86_64.Sign.IM p D σ s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.imChk, Bool.and_eq_true] at hc
  exact ⟨h.st.step hP hc.1, h.ok, Fam.keep h.st.lay hP hc.2 h.A⟩

theorem IA.im {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA p D σ (p.k * p.ℓ) s) (h1 : s.gpr .r15 = 1) :
    VG.Proof.MlDsa.X86_64.Sign.IM p D σ s := ⟨h.st, (h.ok h1).1, (h.ok h1).2⟩

/-! ## The private key -/

/-- `Â`, the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (D : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  im : VG.Proof.MlDsa.X86_64.Sign.IM p D σ s
  s1 : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.s1Base p) a (VG.Proof.MlDsa.X86_64.Sign.S1v p σ)
  s2 : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.s2Base p) b (VG.Proof.MlDsa.X86_64.Sign.S2v p σ)
  t0 : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.t0Base p) c (VG.Proof.MlDsa.X86_64.Sign.T0v p σ)

def idChk (p : Params) (ws : List (Ptr × Nat)) (a b c : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.imChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.s1Base p) a && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.s2Base p) b && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.t0Base p) c

theorem ID.step {p : Params} {D : Nat} {σ s s' : State} {a b c : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.ID p D σ a b c s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.idChk p ws a b c = true) : VG.Proof.MlDsa.X86_64.Sign.ID p D σ a b c s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.idChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.im.st.lay
  exact ⟨h.im.step hP h1, Fam.keep L hP h2 h.s1, Fam.keep L hP h3 h.s2, Fam.keep L hP h4 h.t0⟩

theorem pS_bases (j : Nat) : (pS j).1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := List.mem_cons_self ..

theorem sc_bases (o : Nat) : (sc o).1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := List.mem_cons_self ..

theorem pa_add (s : State) (r : Reg) (a b : Nat) : VG.Proof.MlDsa.X86_64.Sign.pa s (r, a) + BitVec.ofNat 64 b = VG.Proof.MlDsa.X86_64.Sign.pa s (r, a + b) :=
  VG.Proof.MlKem.X86_64.off_add _ _ _

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sign.St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (.rbp, o)) len = ((VG.Proof.MlDsa.X86_64.Sign.skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, VG.Proof.MlDsa.X86_64.Sign.pa_add, Nat.zero_add]

/-- What decoding a polynomial of `len` bytes at `src` to slot `j` needs of the layout. -/
def decChk (p : Params) (a b c : Nat) (src : Ptr) (len j : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.rwChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) src len (pS j) 1024 && VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (pS j) &&
    VG.Proof.MlDsa.X86_64.Sign.idChk p [(pS j, 1024)] a b c && VG.Proof.MlDsa.X86_64.Sign.idChk p [(pS j, 1024), (sc oPS, 1024)] a b c

theorem dec_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {a b c : Nat} {src : Ptr}
    {len x y j : Nat} (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y))
    (hc : VG.Proof.MlDsa.X86_64.Sign.decChk p a b c src len j = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ID p D σ a b c s) :
    WP isa (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sign.ID p D σ a b c s' ∧ VG.Proof.MlDsa.X86_64.Sign.Pl s' j (ntt (toRq (bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s src) len) x y))) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.bupAt_ok hP h.im.st.lay hp hl h1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 h3
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := ntt) hP.ntt I1.im.st.lay h2 (by rw [hP1.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases j)]; exact hq1.1))
    fun s2 ⟨hP2, _, hq2⟩ => ⟨I1.step hP2 h4, ?_⟩
  show PolyIs s2.mem (VG.Proof.MlDsa.X86_64.Sign.pa s2 (pS j)) _
  rw [hP2.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases j), hP1.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases j), ← hq1.2]
  rw [hP1.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases j)] at hq2
  exact hq2

/-- What `decode` needs of the layout. -/
def dChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun r => VG.Proof.MlDsa.X86_64.Sign.decChk p r 0 0 (.rbp, skS1 p r) (sLen p) (VG.Proof.MlDsa.X86_64.Sign.s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => VG.Proof.MlDsa.X86_64.Sign.decChk p p.ℓ i 0 (.rbp, skS2 p i) (sLen p) (VG.Proof.MlDsa.X86_64.Sign.s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => VG.Proof.MlDsa.X86_64.Sign.decChk p p.ℓ p.k i (.rbp, skT0 p i) 416 (VG.Proof.MlDsa.X86_64.Sign.t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    VG.Proof.MlDsa.X86_64.Sign.shakeChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64 &&
    VG.Proof.MlDsa.X86_64.Sign.idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Decoded: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″` at `MS`. -/
structure IK (p : Params) (D : Nat) (σ s : State) : Prop where
  d : VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oMS)) 64 = VG.Proof.MlDsa.X86_64.Sign.rppOf p σ

theorem dChk_spec {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.dChk p = true) :
    (∀ r < p.ℓ, VG.Proof.MlDsa.X86_64.Sign.decChk p r 0 0 (.rbp, skS1 p r) (sLen p) (VG.Proof.MlDsa.X86_64.Sign.s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, VG.Proof.MlDsa.X86_64.Sign.decChk p p.ℓ i 0 (.rbp, skS2 p i) (sLen p) (VG.Proof.MlDsa.X86_64.Sign.s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, VG.Proof.MlDsa.X86_64.Sign.decChk p p.ℓ p.k i (.rbp, skT0 p i) 416 (VG.Proof.MlDsa.X86_64.Sign.t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    VG.Proof.MlDsa.X86_64.Sign.shakeChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64 = true ∧
    VG.Proof.MlDsa.X86_64.Sign.idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k = true ∧ VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oMS) 64 = true ∧
    (p.η, p.η) ∈ bitPackParams ∧ 64 ≤ p.skLen := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.dChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hη⟩, hsk⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, hη, hsk⟩

theorem sLen_eq (p : Params) : sLen p = 32 * bitlen (p.η + p.η) := by rw [← Nat.two_mul]

section
variable {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.dChk p = true) {σ : State}
include hP hc

theorem decS1_ok {r : Nat} (hr : r < p.ℓ) {s : State} (hs : VG.Proof.MlDsa.X86_64.Sign.ID p D σ r 0 0 s) :
    WP isa (decS1 P p r) s (VG.Proof.MlDsa.X86_64.Sign.ID p D σ (r + 1) 0 0) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc).1 r hr
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.dec_ok hP (VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc).2.2.2.2.2.2.1 (VG.Proof.MlDsa.X86_64.Sign.sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, Fam.snoc I'.s1 ?_, I'.s2, I'.t0⟩
  rw [VG.Proof.MlDsa.X86_64.Sign.sk_slice hs.im.st ck] at hq
  exact hq

theorem decS2_ok {i : Nat} (hi : i < p.k) {s : State} (hs : VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ i 0 s) :
    WP isa (decS2 P p i) s (VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ (i + 1) 0) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc).2.1 i hi
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.dec_ok hP (VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc).2.2.2.2.2.2.1 (VG.Proof.MlDsa.X86_64.Sign.sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, I'.s1, Fam.snoc I'.s2 ?_, I'.t0⟩
  rw [VG.Proof.MlDsa.X86_64.Sign.sk_slice hs.im.st ck] at hq
  exact hq

theorem decT0_ok {i : Nat} (hi : i < p.k) {s : State} (hs : VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k i s) :
    WP isa (decT0 P p i) s (VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k (i + 1)) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc).2.2.1 i hi
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.dec_ok hP (by decide) (by decide) c hs) fun s' ⟨I', hq⟩ => ⟨I'.im, I'.s1, I'.s2,
    Fam.snoc I'.t0 ?_⟩
  have e : skT0 p i = 128 + lenS p * p.ℓ + lenS p * p.k + 32 * 13 * i := by
    unfold skT0 lenS sLen; rw [Nat.mul_add]; omega
  rw [VG.Proof.MlDsa.X86_64.Sign.sk_slice hs.im.st ck, e] at hq
  exact hq

theorem rpp_ok {s : State} (hs : VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k p.k s) :
    WP isa (shakeAt [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64) s (VG.Proof.MlDsa.X86_64.Sign.IK p D σ) := by
  obtain ⟨_, _, _, h4, h5, _, _, hsk⟩ := VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.shake_ok (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hP.hD h4 hs.im.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs.step hP4 h5, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [VG.Proof.MlDsa.X86_64.Sign.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [VG.Proof.MlDsa.X86_64.Sign.sk_slice hs.im.st (o := 32) (len := 32) (by omega), hs.im.st.rnd, hs.im.st.mu, ← List.append_assoc]

theorem decode_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IM p D σ s) : WP isa (decode P p) s (VG.Proof.MlDsa.X86_64.Sign.IK p D σ) := by
  unfold decode
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.X86_64.Sign.ID p D σ r 0 0) p.ℓ 0
    (fun r _ hr s hs => VG.Proof.MlDsa.X86_64.Sign.decS1_ok hP hc (by omega) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ i 0) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.X86_64.Sign.decS2_ok hP hc (by omega) hs) s1
    ⟨hs1.im, hs1.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.X86_64.Sign.decT0_ok hP hc (by omega) hs) s2
    ⟨hs2.im, hs2.s1, hs2.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  exact VG.Proof.MlDsa.X86_64.Sign.rpp_ok hP hc hs3

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseC`. -/
section

/-!
# ML-DSA signing on x86-64: the commitment of an iteration

At the head of iteration `t` of the loop (`IL`): what decoding left, `κ = ℓt`
at `KAP`, `814 - t` at `CNT`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`
(`maskR_ok`), `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])` (`rowW_ok`),
`w1Encode(HighBits(w[i]))` at `W1` (`w1R_ok`), and `c̃ = H(μ ‖ w1Encode(w₁),
λ/4)` at `CT` (`commit_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : Poly := aF maxBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) i j

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : Poly := toRq (yF p (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : Poly := yhF p (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : Poly := wF p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) maxBounds 0 t

end

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.X86_64.Sign.aVal p σ (p.ℓ * i + j) = VG.Proof.MlDsa.X86_64.Sign.Am p σ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.X86_64.Sign.aVal, e1, e2]

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s
  kap : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * t)
  cnt : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  t_lt : t < 814
  rej : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t

/-- A piece that writes `ws` keeps what decoding left (but `KAP` and `CNT`). -/
def ikChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.idChk p ws p.ℓ p.k p.k && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oMS) 64

/-- A piece that writes `ws` keeps `IL`. -/
def ilChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ikChk p ws && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oKAP) 8 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oCNT) 8

theorem IK.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.ikChk p ws = true) : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ikChk, Bool.and_eq_true] at hc
  exact ⟨h.d.step hP hc.1, (h.d.im.st.lay.keepBytes hP hc.2).trans h.rpp⟩

theorem IL.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.ilChk p ws = true) : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ilChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP h1, (L.keepW hP h2).trans h.kap, (L.keepW hP h3).trans h.cnt, h.t_lt, h.rej⟩

theorem IL.st {p : Params} {D : Nat} {σ s : State} {t : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) : VG.Proof.MlDsa.X86_64.Sign.St p D σ s := h.k.d.im.st

/-! ## `κ + r` -/

theorem setKap_ok (o r : Nat) (hr : r < 2 ^ 31) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 8) (h2 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc o)) 1)
    (h3 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (o + 1))) 1) :
    WP isa (.block (setKap o r)) s fun s' =>
      s'.mem = (s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc o))
        ((s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 64 + BitVec.ofNat 64 r).setWidth 8)).writeW
        (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (o + 1))) (((s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 64 + BitVec.ofNat 64 r) >>> 8).setWidth 8) ∧
        Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  unfold setKap
  xrun [h1, h2, h3, VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hr]

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 64 x).setWidth 8, (BitVec.ofNat 64 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [VG.Proof.MlDsa.X86_64.Sign.integerToBytes_two]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega

theorem add_one_ne (a : Addr) : a ≠ a + 1 := by
  intro h
  have := congrArg BitVec.toNat h
  have ha := a.isLt
  rw [BitVec.toNat_add] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  omega

theorem bytes2_write (m : Mem) (a : Addr) (v w : Byte) :
    bytesAt ((m.writeW a v).writeW (a + 1) w) a 2 = [v, w] := by
  show [((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 0),
    ((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 1)] = _
  have e0 : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
  have e1 : a + BitVec.ofNat 64 1 = a + 1 := rfl
  rw [e0, e1, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlKem.writeW8_apply, ifn (VG.Proof.MlDsa.X86_64.Sign.add_one_ne a), ifp rfl,
    VG.Proof.MlKem.writeW8_apply, ifp rfl]

/-- `κ + r` to `scratch + o`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKap_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {r x : Nat}
    {o : Nat} (hr : r < 2 ^ 31) (hx : x + r < 2 ^ 16) (h1 : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : VG.Proof.MlDsa.X86_64.Sign.inB wbs (sc o) 2 = true) (hk : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKap o r)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(sc o, 2)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc o)) 2 = integerToBytes (x + r) 2 := by
  have e65 : VG.Proof.MlDsa.X86_64.Sign.pa s (sc (o + 1)) = VG.Proof.MlDsa.X86_64.Sign.pa s (sc o) + 1 := (VG.Proof.MlDsa.X86_64.Sign.pa_sc_add s o 1).symm
  have w2 := L.iW h2
  have c0 : (⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc o), 2⟩ : Region).Contains (VG.Proof.MlDsa.X86_64.Sign.pa s (sc o)) 1 := by
    have := VG.Proof.MlDsa.X86_64.Sign.contains_offset' (base := VG.Proof.MlDsa.X86_64.Sign.pa s (sc o)) (off := 0) (len := 1) (n := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc o), 2⟩ : Region).Contains (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (o + 1))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.X86_64.Sign.contains_offset' (off := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc o)) 1 := by
    have := VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (o + 1))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setKap_ok o r hr s (L.iR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc o), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨(VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).1, (VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf).2, ?_⟩
  rw [hm, e65, VG.Proof.MlDsa.X86_64.Sign.bytes2_write, hk, VG.Proof.MlDsa.X86_64.Sign.ofNat64_add, VG.Proof.MlDsa.X86_64.Sign.kappa_bytes hx]

/-- `κ + r` to `MS + 64`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKappa_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {r x : Nat}
    (hr : r < 2 ^ 31) (hx : x + r < 2 ^ 16) (h1 : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : VG.Proof.MlDsa.X86_64.Sign.inB wbs (sc (oMS + 64)) 2 = true) (hk : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKappa r)) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(sc (oMS + 64), 2)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64))) 2 = integerToBytes (x + r) 2 :=
  VG.Proof.MlDsa.X86_64.Sign.setKap_okB L hr hx h1 h2 hk

/-! ## `y` and `ŷ` -/

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure ICm (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) r (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yhBase p) r (VG.Proof.MlDsa.X86_64.Sign.YHv p σ (p.ℓ * t))

def icmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ilChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p) r && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yhBase p) r

theorem ICm.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.icmChk p ws r = true) : VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t r s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.icmChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `y[r]` and `ŷ[r]` need of the layout. -/
def mChk (p : Params) (r : Nat) : Bool :=
  let y := pS (VG.Proof.MlDsa.X86_64.Sign.yBase p + r)
  let yh := pS (VG.Proof.MlDsa.X86_64.Sign.yhBase p + r)
  let w1 : List (Ptr × Nat) := [(sc (oMS + 64), 2)]
  let w2 : List (Ptr × Nat) := [(y, 1024), (sc oPS, 2048)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  VG.Proof.MlDsa.X86_64.Sign.icmChk p w1 r && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oKAP) 8 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oMS + 64)) 2 && VG.Proof.MlDsa.X86_64.Sign.maskChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) y &&
    VG.Proof.MlDsa.X86_64.Sign.icmChk p w2 r && VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) yh y 1024 && VG.Proof.MlDsa.X86_64.Sign.icmChk p w3 r && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (VG.Proof.MlDsa.X86_64.Sign.yBase p) (r + 1) &&
    VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) yh && VG.Proof.MlDsa.X86_64.Sign.icmChk p w4 r && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w4 (VG.Proof.MlDsa.X86_64.Sign.yBase p) (r + 1) &&
    decide (p.ℓ * 813 + r < 2 ^ 16) && decide (r < 2 ^ 31) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem maskR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.mChk p r = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t r s) : WP isa (maskR P p r) s (VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (r + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, k1⟩, w1⟩, cm⟩, c2⟩, cc⟩, c3⟩, f3⟩, ci⟩, c4⟩, f4⟩, hx⟩, hr⟩, hγ⟩ := hc
  have ht := h.l.t_lt
  unfold maskR
  have hx' : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.step hP1 c1
  have hms : bytesAt s1.mem (VG.Proof.MlDsa.X86_64.Sign.pa s1 (sc oMS)) 66 = VG.Proof.MlDsa.X86_64.Sign.rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, I1.l.k.rpp, VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, hP1.pa (by decide), hb1]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.maskAt_ok hP I1.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_)
  rw [hms] at hq2
  have I2 := I1.step hP2 c2
  have hy2 : VG.Proof.MlDsa.X86_64.Sign.Fam s2 (VG.Proof.MlDsa.X86_64.Sign.yBase p) (r + 1) (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t)) :=
    Fam.snoc I2.y (by
      show PolyIs s2.mem (VG.Proof.MlDsa.X86_64.Sign.pa s2 (pS (VG.Proof.MlDsa.X86_64.Sign.yBase p + r))) _
      rw [hP2.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq2)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB I2.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := I2.step hP3 c3
  have hyh3 : VG.Proof.MlDsa.X86_64.Sign.Pl s3 (VG.Proof.MlDsa.X86_64.Sign.yhBase p + r) (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]
    exact polyIs_of_bytes hb3 (hy2 r (by omega))
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, Fam.keep I3.l.st.lay hP4 f4 (Fam.keep I2.l.st.lay hP3 f3 hy2), Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _), hyh3.2] at *
  exact hq4

/-! ## `y` and `ŷ`, four at a time -/

/-- Iteration `t`, with the first `ry` polynomials of `y` and the first `r` of `ŷ`. -/
structure ICy (p : Params) (D : Nat) (σ : State) (t ry r : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) ry (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yhBase p) r (VG.Proof.MlDsa.X86_64.Sign.YHv p σ (p.ℓ * t))

def icyChk (p : Params) (ws : List (Ptr × Nat)) (ry r : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ilChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p) ry && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yhBase p) r

theorem ICy.step {p : Params} {D : Nat} {σ s s' : State} {t ry r : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t ry r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.icyChk p ws ry r = true) : VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t ry r s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.icyChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `ŷ[r]` needs of the layout, with `ry` polynomials of `y`. -/
def yhChk (p : Params) (ry r : Nat) : Bool :=
  let y := pS (VG.Proof.MlDsa.X86_64.Sign.yBase p + r)
  let yh := pS (VG.Proof.MlDsa.X86_64.Sign.yhBase p + r)
  VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) yh y 1024 && VG.Proof.MlDsa.X86_64.Sign.icyChk p [(yh, 1024)] ry r && VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) yh &&
    VG.Proof.MlDsa.X86_64.Sign.icyChk p [(yh, 1024), (sc oPS, 1024)] ry r

theorem yhR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t ry r : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.yhChk p ry r = true) (hr : r < ry) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t ry r s) :
    WP isa (yhR P p r) s (VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t ry (r + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.yhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨cc, c3⟩, ci⟩, c4⟩ := hc
  unfold yhR
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB h.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := h.step hP3 c3
  have hyh3 : VG.Proof.MlDsa.X86_64.Sign.Pl s3 (VG.Proof.MlDsa.X86_64.Sign.yhBase p + r) (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]
    exact polyIs_of_bytes hb3 (h.y r hr)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, I4.y, Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _), hyh3.2] at *
  exact hq4

/-- Iteration `t`, with the first `4g` polynomials of `y` and `ŷ`, and the first `k` seeds of `MS4`. -/
structure SD (p : Params) (D : Nat) (σ : State) (t g k : Nat) (s : State) : Prop where
  m : VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * g) s
  sd : ∀ j < k, bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS4 + 66 * j))) 66 =
    VG.Proof.MlDsa.X86_64.Sign.rppOf p σ ++ integerToBytes (p.ℓ * t + (4 * g + j)) 2

/-- What seed `k` of `MS4` needs of the layout. -/
def ms4Chk (p : Params) (g k : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(sc (oMS4 + 66 * k), 64)]
  let w2 : List (Ptr × Nat) := [(sc (oMS4 + 66 * k + 64), 2)]
  VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oMS4 + 66 * k)) (sc oMS) 64 && VG.Proof.MlDsa.X86_64.Sign.icmChk p w1 (4 * g) && VG.Proof.MlDsa.X86_64.Sign.icmChk p w2 (4 * g) &&
    VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oKAP) 8 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc (oMS4 + 66 * k + 64)) 2 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc (oMS4 + 66 * k)) 64 &&
    (List.range k).all (fun j => VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (sc (oMS4 + 66 * j)) 66 &&
      VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc (oMS4 + 66 * j)) 66) &&
    decide (p.ℓ * 813 + (4 * g + k) < 2 ^ 16) && decide (4 * g + k < 2 ^ 31)

theorem ms4_ok {p : Params} {D : Nat} {σ : State} {t g k : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.ms4Chk p g k = true) {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.SD p D σ t g k s) : WP isa (cpM4 g k) s (VG.Proof.MlDsa.X86_64.Sign.SD p D σ t g (k + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ms4Chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cc, c1⟩, c2⟩, k1⟩, w2⟩, k12⟩, kd⟩, hx⟩, hr⟩ := hc
  have ht := h.m.l.t_lt
  have hx' : p.ℓ * t + (4 * g + k) < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega); omega
  unfold cpM4
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB h.m.l.st.lay cc) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.m.step hP1 c1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setKap_okB I1.l.st.lay hr hx' k1 w2 I1.l.kap) fun s2 ⟨hP2, _, hb2⟩ => ?_
  have I2 := I1.step hP2 c2
  refine ⟨I2, fun j hj => ?_⟩
  rcases (by omega : j < k ∨ j = k) with hj' | rfl
  · have kk := List.all_eq_true.mp kd j (List.mem_range.mpr hj')
    simp only [Bool.and_eq_true] at kk
    rw [I1.l.st.lay.keepBytes hP2 kk.2, h.m.l.st.lay.keepBytes hP1 kk.1]
    exact h.sd j hj'
  · rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, I1.l.st.lay.keepBytes hP2 k12, hP1.pa (VG.Proof.MlDsa.X86_64.Sign.sc_bases _), hb1,
      h.m.l.k.rpp, hP2.pa (VG.Proof.MlDsa.X86_64.Sign.sc_bases _), hb2]

/-- What `y[4g], …, y[4g + 3]` and their `ŷ` need of the layout. -/
def m4Chk (p : Params) (g : Nat) : Bool :=
  (List.range 4).all (VG.Proof.MlDsa.X86_64.Sign.ms4Chk p g) && VG.Proof.MlDsa.X86_64.Sign.mask4Chk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (yP p (4 * g)) (r4P p) &&
    VG.Proof.MlDsa.X86_64.Sign.icmChk p [(yP p (4 * g), 4096), (r4P p, 8192)] (4 * g) &&
    (List.range 4).all (fun r => VG.Proof.MlDsa.X86_64.Sign.yhChk p (4 * g + 4) (4 * g + r)) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem m4Chk_spec {p : Params} {g : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.m4Chk p g = true) :
    (∀ k < 4, VG.Proof.MlDsa.X86_64.Sign.ms4Chk p g k = true) ∧ VG.Proof.MlDsa.X86_64.Sign.mask4Chk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (yP p (4 * g)) (r4P p) = true ∧
      VG.Proof.MlDsa.X86_64.Sign.icmChk p [(yP p (4 * g), 4096), (r4P p, 8192)] (4 * g) = true ∧
      (∀ r, 4 * g ≤ r → r < 4 * g + 4 → VG.Proof.MlDsa.X86_64.Sign.yhChk p (4 * g + 4) r = true) ∧ (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.m4Chk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hcp, cm⟩, c2⟩, hyh⟩, hγ⟩ := hc
  refine ⟨hcp, cm, c2, fun r h1 h2 => ?_, hγ⟩
  have := hyh (r - 4 * g) (by omega)
  rwa [show 4 * g + (r - 4 * g) = r by omega] at this

/-- The call of `vg_mldsa_expand_mask_poly4`, from the four seeds of `MS4`. -/
theorem m4call_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t g : Nat}
    (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) (cm : VG.Proof.MlDsa.X86_64.Sign.mask4Chk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (yP p (4 * g)) (r4P p) = true)
    (c2 : VG.Proof.MlDsa.X86_64.Sign.icmChk p [(yP p (4 * g), 4096), (r4P p, 8192)] (4 * g) = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.SD p D σ t g 4 s) :
    WP isa (mask4At P p.γ₁ (yP p (4 * g)) (r4P p)) s (VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t (4 * g + 4) (4 * g)) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.mask4Call_ok hP h.m.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_
  have I2 := h.m.step hP2 c2
  refine ⟨I2.l, fun j hj => ?_, I2.yh⟩
  rcases (by omega : j < 4 * g ∨ 4 * g ≤ j) with hj' | hj'
  · exact I2.y j hj'
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ j = 4 * g + k := ⟨j - 4 * g, by omega, by omega⟩
    have hq := hq2 k hk
    rw [seed66, VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, h.sd k hk] at hq
    show PolyIs s2.mem (VG.Proof.MlDsa.X86_64.Sign.pa s2 (pS (VG.Proof.MlDsa.X86_64.Sign.yBase p + (4 * g + k)))) _
    rw [hP2.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _), ← Nat.add_assoc, ← VG.Proof.MlDsa.X86_64.Sign.pa_poly4]
    exact hq

theorem mask4_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t g : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.m4Chk p g = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * g) s) :
    WP isa (mask4 P p g) s (VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * (g + 1))) := by
  obtain ⟨hcp, cm, c2, hyh, hγ⟩ := VG.Proof.MlDsa.X86_64.Sign.m4Chk_spec hc
  unfold mask4
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun k => VG.Proof.MlDsa.X86_64.Sign.SD p D σ t g k) 4 0
    (fun k _ hk s hs => VG.Proof.MlDsa.X86_64.Sign.ms4_ok (hcp k (by omega)) hs) s ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.m4call_ok hP hγ cm c2 hs1) fun s2 hs2 => ?_)
  exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t (4 * g + 4) r) 4 (4 * g)
    (fun r h1 hr s hs => VG.Proof.MlDsa.X86_64.Sign.yhR_ok hP (hyh r h1 hr) (by omega) hs) s2 hs2)
    fun s3 hs3 => ⟨hs3.l, hs3.y, hs3.yh⟩

/-! ## `w` -/

/-- Iteration `t`, with `y`, `ŷ`, and the first `i` polynomials of `w`. -/
structure ICw (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yhBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.YHv p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p) i (VG.Proof.MlDsa.X86_64.Sign.Wv p σ (p.ℓ * t))

def icwChk (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.icmChk p ws p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.wBase p) i

theorem ICw.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.icwChk p ws i = true) : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.icwChk, Bool.and_eq_true] at hc
  have I : VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t p.ℓ s' := (ICm.mk h.l h.y h.yh).step hP hc.1
  exact ⟨I.l, I.y, I.yh, Fam.keep h.l.st.lay hP hc.2 h.w⟩

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (σ : State) (κ i m : Nat) : Poly :=
  ((List.range m).map fun j => multiplyNTT (VG.Proof.MlDsa.X86_64.Sign.Am p σ i j) (VG.Proof.MlDsa.X86_64.Sign.YHv p σ κ j)).foldl add VG.Spec.MlDsa.zero

theorem add_zero_left (x : Poly) : add VG.Spec.MlDsa.zero x = x := by
  apply Vector.ext
  intro j hj
  simp [add, VG.Spec.MlDsa.zero]

theorem wAcc_one (p : Params) (σ : State) (κ i : Nat) :
    VG.Proof.MlDsa.X86_64.Sign.wAcc p σ κ i 1 = multiplyNTT (VG.Proof.MlDsa.X86_64.Sign.Am p σ i 0) (VG.Proof.MlDsa.X86_64.Sign.YHv p σ κ 0) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, VG.Proof.MlDsa.X86_64.Sign.add_zero_left]

theorem wAcc_succ (p : Params) (σ : State) (κ i m : Nat) :
    VG.Proof.MlDsa.X86_64.Sign.wAcc p σ κ i (m + 1) = add (VG.Proof.MlDsa.X86_64.Sign.wAcc p σ κ i m) (multiplyNTT (VG.Proof.MlDsa.X86_64.Sign.Am p σ i m) (VG.Proof.MlDsa.X86_64.Sign.YHv p σ κ m)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem aP_ij (p : Params) (i j : Nat) : VG.Impl.MlDsa.X86_64.Sign.aP p i j = pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + (p.ℓ * i + j)) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j) = _
  rw [Nat.add_assoc (5 + 4 * p.k + 3 * p.ℓ)]

/-- What `w[i]` needs of the layout. -/
def wChk (p : Params) (i : Nat) : Bool :=
  let w := pS (VG.Proof.MlDsa.X86_64.Sign.wBase p + i)
  (List.range p.ℓ).all (fun j => VG.Proof.MlDsa.X86_64.Sign.mulChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) w (VG.Impl.MlDsa.X86_64.Sign.aP p i j) (yhP p j)) && VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) w &&
    VG.Proof.MlDsa.X86_64.Sign.icwChk p [(w, 1024)] i && VG.Proof.MlDsa.X86_64.Sign.icwChk p [(w, 1024), (sc oPS, 1024)] i && decide (0 < p.ℓ)

theorem rowW_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.wChk p i = true) (hi : i < p.k) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) :
    WP isa (rowW P p i) s (VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, c2⟩, hl⟩ := hc
  have hA : ∀ {s : State} (I : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.aP p i j)) (VG.Proof.MlDsa.X86_64.Sign.Am p σ i j) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [VG.Proof.MlDsa.X86_64.Sign.aVal_ij hj] at this
      rw [VG.Proof.MlDsa.X86_64.Sign.aP_ij]; exact this
  have hY : ∀ {s : State} (I : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yhP p j)) (VG.Proof.MlDsa.X86_64.Sign.YHv p σ (p.ℓ * t) j) :=
    fun I j hj => I.yh j hj
  unfold rowW
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul h.l.st.lay (cm 0 hl) (hA h 0 hl).1 (hY h 0 hl).1)
    fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 c1
  rw [(hA h 0 hl).2, (hY h 0 hl).2, ← VG.Proof.MlDsa.X86_64.Sign.wAcc_one] at hq1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun j s => VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s ∧ VG.Proof.MlDsa.X86_64.Sign.Pl s (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.wAcc p σ (p.ℓ * t) i j))
    (p.ℓ - 1) 1 (fun j hj1 hj s ⟨I, hw⟩ => ?_) s1 ⟨I1, by show PolyIs _ _ _; rw [hP1.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq1⟩)
    fun s2 ⟨I2, hw2⟩ => ?_)
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAddAt_ok hP.mulAdd I.l.st.lay (cm j (by omega)) hw.1 (hA I j (by omega)).1
      (hY I j (by omega)).1) fun s' ⟨hP', _, hq'⟩ => ⟨I.step hP' c1, ?_⟩
    rw [hw.2, (hA I j (by omega)).2, (hY I j (by omega)).2, ← VG.Proof.MlDsa.X86_64.Sign.wAcc_succ] at hq'
    show PolyIs _ _ _
    rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq'
  rw [show 1 + (p.ℓ - 1) = p.ℓ by omega] at hw2
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt I2.l.st.lay ci hw2.1) fun s3 ⟨hP3, _, hq3⟩ => ?_
  have I3 := I2.step hP3 c2
  refine ⟨I3.l, I3.y, I3.yh, Fam.snoc I3.w ?_⟩
  show PolyIs _ _ _
  rw [hP3.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]
  rw [hw2.2] at hq3
  exact hq3

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (σ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => simpleBitPack (w1F p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `ŷ`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure ICh (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t p.k s
  w1 : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oW1)) (w1Len p * i) = VG.Proof.MlDsa.X86_64.Sign.w1Enc p σ (p.ℓ * t) i

/-- What `w1Encode(w₁[i])` needs of the layout. -/
def hChk (p : Params) (i : Nat) : Bool :=
  let w := pS (VG.Proof.MlDsa.X86_64.Sign.wBase p + i)
  let o := sc (oW1 + w1Len p * i)
  VG.Proof.MlDsa.X86_64.Sign.rwChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) w 1024 t1P 1024 && VG.Proof.MlDsa.X86_64.Sign.rwChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t1P 1024 o (w1Len p) &&
    VG.Proof.MlDsa.X86_64.Sign.icwChk p [(t1P, 1024)] p.k && VG.Proof.MlDsa.X86_64.Sign.icwChk p [(o, w1Len p)] p.k && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(t1P, 1024)] (sc oW1) (w1Len p * i) &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(o, w1Len p)] (sc oW1) (w1Len p * i) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (p.γ₂ ∈ gamma2s)

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

theorem w1R_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.hChk p i = true) (hi : i < p.k) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t i s) :
    WP isa (w1R P p i) s (VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, k1⟩, k2⟩, e1⟩, e2⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.highBitsAt_ok hP h.c.l.st.lay hγ c1 (h.c.w i hi).1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.c.step hP1 k1
  rw [(h.c.w i hi).2] at hq1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.sbpAt_ok hP I1.l.st.lay hb rfl c2 fun j hj => ?_) fun s2 ⟨hP2, _, hq2⟩ => ?_
  · rw [hP1.pa (by decide), VG.Proof.MlDsa.X86_64.Sign.natPolyIs_coeff hq1 hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _
  have I2 := I1.step hP2 k2
  refine ⟨I2, ?_⟩
  have b1 : bytesAt s2.mem (VG.Proof.MlDsa.X86_64.Sign.pa s2 (sc oW1)) (w1Len p * i) = VG.Proof.MlDsa.X86_64.Sign.w1Enc p σ (p.ℓ * t) i := by
    rw [I1.l.st.lay.keepBytes hP2 e2, h.c.l.st.lay.keepBytes hP1 e1, h.w1]
  have b2 : bytesAt s2.mem (VG.Proof.MlDsa.X86_64.Sign.pa s2 (sc (oW1 + w1Len p * i))) (w1Len p) =
      simpleBitPack (w1F p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) (p.ℓ * t) i) (w1Max p) := by
    rw [hP2.pa (VG.Proof.MlDsa.X86_64.Sign.sc_bases _), hq2, hP1.pa (by decide), show natPolyAt s1.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t1P) = _ from hq1]
    rfl
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, VG.Proof.MlDsa.X86_64.Sign.pa_sc_add, b1, b2, VG.Proof.MlDsa.X86_64.Sign.w1Enc, VG.Proof.MlDsa.X86_64.Sign.w1Enc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton]

/-- The commitment of iteration `t`: `y`, `ŷ`, `w`, and `c̃` at `CT`. -/
structure IC (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  (List.range (p.ℓ / 4)).all (VG.Proof.MlDsa.X86_64.Sign.m4Chk p) && (List.range p.ℓ).all (VG.Proof.MlDsa.X86_64.Sign.mChk p) && (List.range p.k).all (VG.Proof.MlDsa.X86_64.Sign.wChk p) && (List.range p.k).all (VG.Proof.MlDsa.X86_64.Sign.hChk p) &&
    VG.Proof.MlDsa.X86_64.Sign.shakeChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) [((.r12, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p) &&
    VG.Proof.MlDsa.X86_64.Sign.icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem commit_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) : WP isa (commit P p) s (VG.Proof.MlDsa.X86_64.Sign.IC p D σ t) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hm4, hm⟩, hw⟩, hh⟩, hs⟩, hk⟩ := hc
  unfold commit
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun g => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * g)) (p.ℓ / 4) 0
    (fun g _ hg s hs => VG.Proof.MlDsa.X86_64.Sign.mask4_ok hP (hm4 g (by omega)) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s0 hs0 => ?_)
  rw [Nat.zero_add] at hs0
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t r) (p.ℓ % 4) (4 * (p.ℓ / 4))
    (fun r _ hr s hs => VG.Proof.MlDsa.X86_64.Sign.maskR_ok hP (hm r (by omega)) hs) s0 hs0) fun s1 hs1 => ?_)
  rw [Nat.div_add_mod] at hs1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.X86_64.Sign.rowW_ok hP (hw i (by omega)) (by omega) hs) s1
    ⟨hs1.l, hs1.y, hs1.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.X86_64.Sign.w1R_ok hP (hh i (by omega)) (by omega) hs) s2
    ⟨hs2, by simp [VG.Proof.MlDsa.X86_64.Sign.w1Enc]; rfl⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.shake_ok (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hP.hD hs hs3.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs3.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [VG.Proof.MlDsa.X86_64.Sign.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, hs3.w1, hs3.c.l.st.mu]
  simp only [VG.Proof.MlDsa.X86_64.Sign.CTv, ctF, w1Encode, List.flatMap_map]

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseK`. -/
section

/-!
# ML-DSA signing on x86-64: the checks of an iteration

`c = SampleInBall(c̃)` at `ĉ` (`ball_ok`), and, if it succeeded, `ĉ = NTT(c)`
and each check of the iteration, their results ANDed into `r15`: the norm of
each `z[r]` (`zR_ok`), of each `r₀[i]` (`r0R_ok`) and of each `ct₀[i]`, with
each hint `h[i]` and the number of its 1s summed at `ONES` (`hR_ok`), and that
sum against `ω` (`onesOk_ok`); so `r15` is 1 exactly when the iteration passes
(`checks_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `c = SampleInBall(c̃)` of the iteration with counter `κ`, within `maxBounds`. -/
abbrev cV (σ : State) (κ : Nat) : IPoly :=
  (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)).getD (Vector.replicate n 0)

/-- `z[r]`, `r₀[i]`, `ct₀[i]`, `w[i] - cs₂[i]`, `w[i] - cs₂[i] + ct₀[i]` and `h[i]`. -/
abbrev Zv (σ : State) (κ r : Nat) : Poly := zF p (VG.Proof.MlDsa.X86_64.Sign.S1v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) r
abbrev R0v (σ : State) (κ i : Nat) : Poly := r0F p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) i
abbrev CT0v (σ : State) (κ i : Nat) : Poly := ct0F (VG.Proof.MlDsa.X86_64.Sign.T0v p σ) (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) i
abbrev W'v (σ : State) (κ i : Nat) : Poly := w'F p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) i
abbrev W''v (σ : State) (κ i : Nat) : Poly := w''F p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.T0v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) i
abbrev Hv (σ : State) (κ i : Nat) : Vector Bool n := hF p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.T0v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) i

/-- Whether the iteration with counter `κ` passes, once `SampleInBall` succeeded. -/
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S1v p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.T0v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ)

end

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)
  r01 : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1
  ok : (s.gpr .rax).setWidth 32 = 1 → VG.Proof.MlDsa.X86_64.Sign.Pl s 0 (toRq (VG.Proof.MlDsa.X86_64.Sign.cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .rax).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)) = none

def bChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ballChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (cLen p) cP && VG.Proof.MlDsa.X86_64.Sign.icwChk p [(cP, 1024), (sc oPS, 2048)] p.k &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(cP, 1024), (sc oPS, 2048)] (sc oCT) (cLen p) && decide ((cLen p, p.τ) ∈ ballParams)

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem ball_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.bChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IC p D σ t s) : WP isa (ballAt P (cLen p) p.τ cP) s (VG.Proof.MlDsa.X86_64.Sign.IB p D σ t) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.bChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, hbp⟩ := hc
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ballCall_ok hP h.c.l.st.lay hbp c1) fun s' ⟨hP1, _, hred, hout, hmax⟩ => ?_
  rw [h.ct] at hout hmax
  refine ⟨h.c.step hP1 c2, by rw [h.c.l.st.lay.keepBytes hP1 c3, h.ct], ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · refine ⟨?_, hmax h1⟩
    show PolyIs _ _ _
    rw [hP1.pa (by decide)]
    exact ⟨hred h1, VG.Proof.MlDsa.X86_64.Sign.ball_val hout h1 (hmax h1)⟩
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

/-! ## Norms, into `r15` -/

theorem normAt_okB {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.X86_64.Sign.normChk (rbs ++ wbs) f = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) {a : Prop} [Decidable a] (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Sign.bit a) :
    WP isa (normAt P f B) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [] ∧ (∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r15 = VG.Proof.MlDsa.X86_64.Sign.bit (a ∧ normRq [polyAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)] < B) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.normCall_ok hP L hB hc hr) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.and15_ok s1) fun s2 ⟨h15', hm2, k2⟩ => ?_
  obtain ⟨hP2, hcs2⟩ := VG.Proof.MlDsa.X86_64.Sign.postB15 (D := D) k2 hm2 (([] : List (Ptr × Nat)).map (VG.Proof.MlDsa.X86_64.Sign.toR s1))
  refine ⟨PPostB.trans hP1 hP2 (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil), fun r hr hne => (hcs2 r hr hne).trans (hcs1 r hr), ?_⟩
  rw [h15', VG.Proof.MlDsa.X86_64.Sign.bit_and (hcs1 _ (by decide) |>.trans h15) hq1]

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : VG.Proof.MlDsa.X86_64.Sign.bit a = VG.Proof.MlDsa.X86_64.Sign.bit b := by
  by_cases ha : a
  · rw [show VG.Proof.MlDsa.X86_64.Sign.bit a = 1 from ifp ha _ _, show VG.Proof.MlDsa.X86_64.Sign.bit b = 1 from ifp (h.mp ha) _ _]
  · rw [show VG.Proof.MlDsa.X86_64.Sign.bit a = 0 from ifn ha _ _, show VG.Proof.MlDsa.X86_64.Sign.bit b = 0 from ifn (fun hb => ha (h.mpr hb)) _ _]

theorem bit01 {a : Prop} [Decidable a] : VG.Proof.MlDsa.X86_64.Sign.bit a = 0 ∨ VG.Proof.MlDsa.X86_64.Sign.bit a = 1 := by
  by_cases ha : a
  · exact .inr (ifp ha _ _)
  · exact .inl (ifn ha _ _)

theorem bit_one {a : Prop} [Decidable a] : VG.Proof.MlDsa.X86_64.Sign.bit a = 1 ↔ a := by
  by_cases ha : a
  · exact ⟨fun _ => ha, fun _ => ifp ha _ _⟩
  · exact ⟨fun h => absurd (h.symm.trans (ifn ha 1 0)) (by decide), fun h => absurd h ha⟩

theorem bit_zero {a : Prop} [Decidable a] : VG.Proof.MlDsa.X86_64.Sign.bit a = 0 ↔ ¬ a := by
  by_cases ha : a
  · exact ⟨fun h => absurd (h.symm.trans (ifp ha 1 0)) (by decide), fun h => absurd ha h⟩
  · exact ⟨fun _ => ha, fun _ => ifn ha _ _⟩

theorem forall_lt_succ {P : Nat → Prop} {r : Nat} : ((∀ j < r, P j) ∧ P r) ↔ ∀ j < r + 1, P j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega), h r (by omega)⟩⟩

theorem Fam.head {s : State} {b m : Nat} {f : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b (m + 1) f) : VG.Proof.MlDsa.X86_64.Sign.Pl s b (f 0) := h 0 (by omega)

theorem Fam.tail {s : State} {b m : Nat} {f : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b (m + 1) f) :
    VG.Proof.MlDsa.X86_64.Sign.Fam s (b + 1) m fun j => f (j + 1) := fun j hj => by
  have := h (j + 1) (by omega)
  show VG.Proof.MlDsa.X86_64.Sign.Pl s (b + 1 + j) _
  rw [show b + 1 + j = b + (j + 1) by omega]
  exact this

theorem Fam.shift {s : State} {b m r : Nat} {f : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s (b + r) (m - r) fun j => f (r + j))
    (hr : r < m) : VG.Proof.MlDsa.X86_64.Sign.Fam s (b + (r + 1)) (m - (r + 1)) fun j => f (r + 1 + j) := fun j hj => by
  have := h (j + 1) (by omega)
  show VG.Proof.MlDsa.X86_64.Sign.Pl s (b + (r + 1) + j) (f (r + 1 + j))
  rw [show b + (r + 1) + j = b + r + (j + 1) by omega, show r + 1 + j = r + (j + 1) by omega]
  exact this

theorem Fam.zero {s : State} {b m : Nat} {f : Nat → Poly} (h : VG.Proof.MlDsa.X86_64.Sign.Fam s b m f) :
    VG.Proof.MlDsa.X86_64.Sign.Fam s (b + 0) (m - 0) fun j => f (0 + j) := fun j hj => by
  show VG.Proof.MlDsa.X86_64.Sign.Pl s (b + 0 + j) (f (0 + j))
  rw [Nat.add_zero, Nat.zero_add]
  exact h j hj

/-! ## The checks' state -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded: `ĉ = NTT(c)`. -/
structure KB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s
  ct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)
  c : VG.Proof.MlDsa.X86_64.Sign.Pl s 0 (chF (VG.Proof.MlDsa.X86_64.Sign.cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome

def kbChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ilChk p ws && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oCT) (cLen p) && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws cP 1024

theorem KB.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.kbChk p ws = true) : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.kbChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP h1, (L.keepBytes hP h2).trans h.ct, L.keepPoly hP h3 h.c, h.some⟩

/-! ## `z` -/

/-- The checks of `z[j]` for `j < r`, with `ONES = 0` (but `r15`). -/
structure IZb (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) r (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t))
  y : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p + r) (p.ℓ - r) fun j => VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t) (r + j)
  w : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k (VG.Proof.MlDsa.X86_64.Sign.Wv p σ (p.ℓ * t))
  ones : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 64 = 0

/-- The checks of `z[j]` for `j < r`, their results in `r15`. -/
def IZ (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sign.IZb p D σ t r s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Sign.bit (∀ j < r, normRq [VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

def zfam (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.kbChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p) r && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oONES) 8

theorem IZb.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.IZb p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.zfam p ws r = true)
    (hy : VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p + r) (p.ℓ - r) = true) : VG.Proof.MlDsa.X86_64.Sign.IZb p D σ t r s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.zfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP hy h.y, Fam.keep L hP h3 h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `z[r]` needs of the layout. -/
def zChk (p : Params) (r : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(yP p r, 1024)]
  VG.Proof.MlDsa.X86_64.Sign.mulChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t1P cP (s1P p r) && VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t1P && VG.Proof.MlDsa.X86_64.Sign.accChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (yP p r) t1P &&
    VG.Proof.MlDsa.X86_64.Sign.normChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (yP p r) && VG.Proof.MlDsa.X86_64.Sign.zfam p w1 r && VG.Proof.MlDsa.X86_64.Sign.zfam p w2 r && VG.Proof.MlDsa.X86_64.Sign.zfam p w3 r && VG.Proof.MlDsa.X86_64.Sign.zfam p [] (r + 1) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (VG.Proof.MlDsa.X86_64.Sign.yBase p + r) (p.ℓ - r) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (VG.Proof.MlDsa.X86_64.Sign.yBase p + r) (p.ℓ - r) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (VG.Proof.MlDsa.X86_64.Sign.yBase p + (r + 1)) (p.ℓ - (r + 1)) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.yBase p + (r + 1)) (p.ℓ - (r + 1)) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (VG.Proof.MlDsa.X86_64.Sign.yBase p) r && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (s1P p r) 1024 && decide (p.γ₁ - p.β < 2 ^ 32) &&
    decide (r < p.ℓ)

theorem zR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.zChk p r = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t r s) : WP isa (zR P p r) s (VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t (r + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, y1⟩, y2⟩, y3⟩, y4⟩, f3⟩, e1⟩, hB⟩, hr⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs1 := h.b.l.k.d.s1 r hr
  unfold zR
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L cm h.b.c.1 hs1.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs1.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hy2 : VG.Proof.MlDsa.X86_64.Sign.Pl s2 (VG.Proof.MlDsa.X86_64.Sign.yBase p + r) (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t) r) := I2.y 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.addAt_ok hP I2.b.l.st.lay ca hy2.1 (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1))
    fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hy2.2, hP2.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1), hP1.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [VG.Proof.MlDsa.X86_64.Sign.zfam, Bool.and_eq_true] at z3 z4
  have hz3 : VG.Proof.MlDsa.X86_64.Sign.Pl s3 (VG.Proof.MlDsa.X86_64.Sign.yBase p + r) (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]
    exact hq3
  have J3 : VG.Proof.MlDsa.X86_64.Sign.IZb p D σ t (r + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.snoc (Fam.keep L2 hP3 f3 I2.z) hz3,
    Fam.keep L2 hP3 y3 (I2.y.shift hr),
    Fam.keep L2 hP3 z3.1.2 I2.w, (L2.keepW hP3 z3.2).trans I2.ones⟩
  have e15 : s3.gpr .r15 = s.gpr .r15 := by
    rw [hcs3 _ (by decide), hcs2 _ (by decide), hcs1 _ (by decide)]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.normAt_okB hP J3.b.l.st.lay hB cn hz3.1 (e15.trans h15)) fun s4 ⟨hP4, _, h4⟩ => ?_
  have L3 := J3.b.l.st.lay
  refine ⟨⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z, Fam.keep L3 hP4 y4 J3.y,
    Fam.keep L3 hP4 z4.1.2 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩, ?_⟩
  rw [h4, hz3.2]
  exact VG.Proof.MlDsa.X86_64.Sign.bit_congr VG.Proof.MlDsa.X86_64.Sign.forall_lt_succ

/-! ## `r₀` -/

/-- The checks of `r₀[j]` for `j < i` (`w[j]` is `w[j] - cs₂[j]`), with `z` checked and `ONES = 0`. -/
structure IRb (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t))
  w' : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p) i (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (p.k - i) fun j => VG.Proof.MlDsa.X86_64.Sign.Wv p σ (p.ℓ * t) (i + j)
  ones : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 64 = 0

/-- `z` passed. -/
abbrev ZOk (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ j] < p.γ₁ - p.β

def IR (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t i s ∧
    s.gpr .r15 = VG.Proof.MlDsa.X86_64.Sign.bit (VG.Proof.MlDsa.X86_64.Sign.ZOk p σ (p.ℓ * t) ∧ ∀ j < i, normRq [VG.Proof.MlDsa.X86_64.Sign.R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

def rfam (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.kbChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.wBase p) i && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oONES) 8

theorem IRb.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.rfam p ws i = true)
    (hw : VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (p.k - i) = true) : VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t i s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.rfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w', Fam.keep L hP hw h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `r₀[i]` needs of the layout. -/
def rChk (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w4 : List (Ptr × Nat) := [(t2P, 1024)]
  VG.Proof.MlDsa.X86_64.Sign.mulChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t1P cP (s2P p i) && VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t1P && VG.Proof.MlDsa.X86_64.Sign.accChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (wP p i) t1P &&
    VG.Proof.MlDsa.X86_64.Sign.rwChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (wP p i) 1024 t2P 1024 && VG.Proof.MlDsa.X86_64.Sign.normChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) t2P && VG.Proof.MlDsa.X86_64.Sign.rfam p w1 i && VG.Proof.MlDsa.X86_64.Sign.rfam p w2 i &&
    VG.Proof.MlDsa.X86_64.Sign.rfam p w3 i && VG.Proof.MlDsa.X86_64.Sign.rfam p w4 (i + 1) && VG.Proof.MlDsa.X86_64.Sign.rfam p [] (i + 1) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (p.k - i) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (p.k - i) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w3 (VG.Proof.MlDsa.X86_64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w4 (VG.Proof.MlDsa.X86_64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w4 (wP p i) 1024 &&
    decide (p.γ₂ - p.β < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k)

theorem r0R_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.rChk p i = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IR p D σ t i s) : WP isa (r0R P p i) s (VG.Proof.MlDsa.X86_64.Sign.IR p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, y1⟩, y2⟩, y3⟩, y4⟩, y5⟩, k4⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs2 := h.b.l.k.d.s2 i hi
  unfold r0R
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L cm h.b.c.1 hs2.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs2.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hw2 : VG.Proof.MlDsa.X86_64.Sign.Pl s2 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.Wv p σ (p.ℓ * t) i) := I2.w 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.subAt_ok hP I2.b.l.st.lay ca hw2.1
    (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1)) fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hw2.2, hP2.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1), hP1.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [VG.Proof.MlDsa.X86_64.Sign.rfam, Bool.and_eq_true] at z3 z4 z5
  have hw3 : VG.Proof.MlDsa.X86_64.Sign.Pl s3 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]
    exact hq3
  have J3 : VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t (i + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.keep L2 hP3 z3.1.1.2 I2.z,
    Fam.snoc (Fam.keep L2 hP3 z3.1.2 I2.w') hw3, Fam.keep L2 hP3 y3 (I2.w.shift hi), (L2.keepW hP3 z3.2).trans I2.ones⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.lowBitsAt_ok hP J3.b.l.st.lay hγ cl hw3.1) fun s4 ⟨hP4, hcs4, hq4⟩ => ?_)
  rw [hw3.2] at hq4
  have L3 := J3.b.l.st.lay
  have J4 : VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t (i + 1) s4 := ⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z,
    Fam.keep L3 hP4 z4.1.2 J3.w', Fam.keep L3 hP4 y4 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩
  have e15 : s4.gpr .r15 = s.gpr .r15 := by
    rw [hcs4 _ (by decide), hcs3 _ (by decide), hcs2 _ (by decide), hcs1 _ (by decide)]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.normAt_okB hP J4.b.l.st.lay hB cn (by rw [hP4.pa (by decide)]; exact hq4.1) (e15.trans h15))
    fun s5 ⟨hP5, _, h5⟩ => ?_
  have L4 := J4.b.l.st.lay
  refine ⟨⟨J4.b.step hP5 z5.1.1.1, Fam.keep L4 hP5 z5.1.1.2 J4.z, Fam.keep L4 hP5 z5.1.2 J4.w',
    Fam.keep L4 hP5 y5 J4.w, (L4.keepW hP5 z5.2).trans J4.ones⟩, ?_⟩
  rw [h5, hP4.pa (by decide), hq4.2]
  exact VG.Proof.MlDsa.X86_64.Sign.bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
    fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## Hints and their 1s -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega

theorem sub_add_neg (a b : Poly) : VG.Spec.MlDsa.sub a (add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.MlDsa.sub, add, neg, Vector.getElem_zipWith, Vector.getElem_map, VG.Proof.MlDsa.X86_64.Sign.zq_sub_add]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : List (Vector Bool n)}
    (hb : ∀ k < 1024, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) (H : HintIs m a 1 h) :
    HintIs m' a 1 h :=
  ⟨H.1, fun i hi j hj => by
    have hn : n = 256 := rfl
    rw [coeffAt_congr₂ hb (show 256 * i + j < 256 by omega)]; exact H.2 i hi j hj⟩

/-- The hints of the first `m` slots from `b`. -/
def HFam (s : State) (b m : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < m, HintIs s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (pS (b + j))) 1 [f j]

theorem HFam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) {b m : Nat} {f : Nat → Vector Bool n}
    (hc : VG.Proof.MlDsa.X86_64.Sign.famChk (rbs ++ wbs) ws b m = true) (h : VG.Proof.MlDsa.X86_64.Sign.HFam s b m f) : VG.Proof.MlDsa.X86_64.Sign.HFam s' b m f := fun j hj => by
  have hk := VG.Proof.MlDsa.X86_64.Sign.famChk_one hc hj
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Sign.keepB_cs hk)]
  exact VG.Proof.MlDsa.X86_64.Sign.hintIs_congr (VG.Proof.MlKem.bytes_frame hP.frame (L.fdisj hk) (by decide)) (h j hj)

theorem HFam.snoc {s : State} {b m : Nat} {f : Nat → Vector Bool n} (h : VG.Proof.MlDsa.X86_64.Sign.HFam s b m f)
    (h' : HintIs s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (pS (b + m))) 1 [f m]) : VG.Proof.MlDsa.X86_64.Sign.HFam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The sum of the 1s of the first `i` hints. -/
abbrev onesSum (f : Nat → Vector Bool n) (i : Nat) : Nat := ((List.range i).map fun j => hintOnes [f j]).sum

theorem onesSum_le (f : Nat → Vector Bool n) : ∀ i, VG.Proof.MlDsa.X86_64.Sign.onesSum f i ≤ 256 * i
  | 0 => by simp [VG.Proof.MlDsa.X86_64.Sign.onesSum]
  | i + 1 => by
    simp only [VG.Proof.MlDsa.X86_64.Sign.onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have := VG.Proof.MlDsa.X86_64.Sign.onesSum_le f i; have := VG.Proof.MlDsa.X86_64.Sign.hintOnes_le (f i)
    simp only [VG.Proof.MlDsa.X86_64.Sign.onesSum] at *
    omega

theorem onesSum_succ (f : Nat → Vector Bool n) (i : Nat) : VG.Proof.MlDsa.X86_64.Sign.onesSum f (i + 1) = VG.Proof.MlDsa.X86_64.Sign.onesSum f i + hintOnes [f i] := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The block after `vg_mldsa_make_hint`: its result added to `ONES`. -/
abbrev onesAdd : List Instr :=
  [.mov32 .rcx (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oONES)), .alu32 .add .rcx (.reg .rax),
    .store (VG.Impl.MlKem.X86_64.at_ .rbx oONES) .rcx]

theorem onesAdd_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 4)
    (h2 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 8) :
    WP isa (.block VG.Proof.MlDsa.X86_64.Sign.onesAdd) s fun s' => s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES))
      (BitVec.setWidth 64 (s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 32 + (s.gpr .rax).setWidth 32)) ∧ Keep [.rcx] s s' := by
  refine WP.keep [.rcx] ?_ (by rfl)
  xrun [h1, h2]

/-! ## `ct₀` and the hint -/

/-- `r₀` passed. -/
abbrev R0Ok (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [VG.Proof.MlDsa.X86_64.Sign.R0v p σ κ j] < p.γ₂ - p.β

/-- The checks of `ct₀[j]` for `j < a`, where `w[j]` is `w[j] - cs₂[j] + ct₀[j]`, and the hints `h[j]` for
`j < c`, their 1s summed at `ONES`. -/
structure IHb (p : Params) (D : Nat) (σ : State) (t a c : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t))
  w'' : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p) a (VG.Proof.MlDsa.X86_64.Sign.W''v p σ (p.ℓ * t))
  w' : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p + a) (p.k - a) fun j => VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) (a + j)
  h : VG.Proof.MlDsa.X86_64.Sign.HFam s 5 c (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t))
  ones : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 64 = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sign.onesSum (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t)) c)

def IH (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sign.IHb p D σ t i i s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Sign.bit ((VG.Proof.MlDsa.X86_64.Sign.ZOk p σ (p.ℓ * t) ∧ VG.Proof.MlDsa.X86_64.Sign.R0Ok p σ (p.ℓ * t)) ∧
    ∀ j < i, normRq [VG.Proof.MlDsa.X86_64.Sign.CT0v p σ (p.ℓ * t) j] < p.γ₂)

def hfam (p : Params) (ws : List (Ptr × Nat)) (a c : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.kbChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.wBase p) a &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.wBase p + a) (p.k - a) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws 5 c

theorem IHb.step {p : Params} {D : Nat} {σ s s' : State} {t a c : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.IHb p D σ t a c s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.hfam p ws a c = true)
    (ho : VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (sc oONES) 8 = true) : VG.Proof.MlDsa.X86_64.Sign.IHb p D σ t a c s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.hfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w'', Fam.keep L hP h4 h.w',
    HFam.keep L hP h5 h.h, (L.keepW hP ho).trans h.ones⟩

theorem ones32 {m : Mem} {a : Addr} {x : Nat} (h : m.readW a 64 = BitVec.ofNat 64 x) :
    m.readW a 32 = BitVec.ofNat 32 x := by
  have e := readW_extract m a (w := 64) (k := 0) (n := 4) (by omega)
  rw [BitVec.add_zero, h] at e
  rw [← e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  omega

/-- What `h[i]` needs of the layout. -/
def hChk2 (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t3P, 1024)]
  let w2 : List (Ptr × Nat) := [(t3P, 1024), (sc oPS, 1024)]
  let w4 : List (Ptr × Nat) := [(t4P, 1024)]
  let w5 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w7 : List (Ptr × Nat) := [(hP i, 1024)]
  let w8 : List (Ptr × Nat) := [(sc oONES, 8)]
  VG.Proof.MlDsa.X86_64.Sign.mulChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t3P cP (t0P p i) && VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t3P && VG.Proof.MlDsa.X86_64.Sign.normChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) t3P &&
    VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t4P (wP p i) 1024 && VG.Proof.MlDsa.X86_64.Sign.accChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (wP p i) t3P &&
    VG.Proof.MlDsa.X86_64.Sign.accChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t4P (wP p i) && VG.Proof.MlDsa.X86_64.Sign.hintChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) t4P (wP p i) (hP i) &&
    VG.Proof.MlDsa.X86_64.Sign.hfam p w1 i i && VG.Proof.MlDsa.X86_64.Sign.hfam p w2 i i && VG.Proof.MlDsa.X86_64.Sign.hfam p [] i i && VG.Proof.MlDsa.X86_64.Sign.hfam p w4 i i &&
    (VG.Proof.MlDsa.X86_64.Sign.kbChk p w5 && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w5 (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w5 5 i) &&
    VG.Proof.MlDsa.X86_64.Sign.hfam p w4 (i + 1) i && VG.Proof.MlDsa.X86_64.Sign.hfam p w7 (i + 1) i && VG.Proof.MlDsa.X86_64.Sign.hfam p w8 (i + 1) (i + 1) &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w5 (VG.Proof.MlDsa.X86_64.Sign.wBase p) i && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) w5 (VG.Proof.MlDsa.X86_64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (sc oONES) 8 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w2 (sc oONES) 8 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (sc oONES) 8 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w4 (sc oONES) 8 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w5 (sc oONES) 8 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w7 (sc oONES) 8 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] t3P 1024 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w4 t3P 1024 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w5 t4P 1024 && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) w1 (t0P p i) 1024 &&
    VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oONES) 4 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oONES) 8 &&
    decide (p.γ₂ < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k) && decide (256 * p.k < 2 ^ 32)

theorem pa_sc {s s' : State} (h : s'.gpr .rbx = s.gpr .rbx) (o : Nat) : VG.Proof.MlDsa.X86_64.Sign.pa s' (sc o) = VG.Proof.MlDsa.X86_64.Sign.pa s (sc o) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, h]

theorem hR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Sign.hChk2 p i = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IH p D σ t i s) : WP isa (hR P p i) s (VG.Proof.MlDsa.X86_64.Sign.IH p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, f5a⟩, f5b⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o7⟩, t3⟩, t4⟩, u5⟩, v1⟩, i1⟩, i2⟩, hγ'⟩, hγ⟩, hi⟩, hk⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have ht0 := h.b.l.k.d.t0 i hi
  unfold hR
  -- `ĉ t̂₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L cm h.b.c.1 ht0.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, ht0.2] at hq1
  have I1 := h.step hP1 g1 o1
  have b1 : s1.gpr .rbx = s.gpr .rbx := hP1.bs _ (by decide)
  -- `ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci (by rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc b1]; exact hq1.1))
    fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc b1, hq1.2] at hq2
  have I2 := I1.step hP2 g2 o2
  have b2 : s2.gpr .rbx = s.gpr .rbx := (hP2.bs _ (by decide)).trans b1
  have q2 : VG.Proof.MlDsa.X86_64.Sign.Pl s2 3 (VG.Proof.MlDsa.X86_64.Sign.CT0v p σ (p.ℓ * t) i) := by show PolyIs _ _ _; rw [VG.Proof.MlDsa.X86_64.Sign.pa_sc b2]; exact hq2
  -- its norm
  have e2 : s2.gpr .r15 = s.gpr .r15 := by rw [hcs2 _ (by decide), hcs1 _ (by decide)]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.normAt_okB hP I2.b.l.st.lay hγ' cn q2.1 (e2.trans h15)) fun s3 ⟨hP3, hcs3, h3⟩ => ?_)
  rw [q2.2] at h3
  have I3 := I2.step hP3 g3 o3
  have q3 : VG.Proof.MlDsa.X86_64.Sign.Pl s3 3 (VG.Proof.MlDsa.X86_64.Sign.CT0v p σ (p.ℓ * t) i) := I2.b.l.st.lay.keepPoly hP3 t3 q2
  -- `T4 ← w[i] - cs₂[i]`
  have hw3 : VG.Proof.MlDsa.X86_64.Sign.Pl s3 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) i) := I3.w' 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB I3.b.l.st.lay cc) fun s4 ⟨hP4, hcs4, hb4⟩ => ?_)
  have I4 := I3.step hP4 g4 o4
  have q4 : VG.Proof.MlDsa.X86_64.Sign.Pl s4 3 (VG.Proof.MlDsa.X86_64.Sign.CT0v p σ (p.ℓ * t) i) := I3.b.l.st.lay.keepPoly hP4 t4 q3
  have r4 : VG.Proof.MlDsa.X86_64.Sign.Pl s4 4 (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP4.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 4)]; exact polyIs_of_bytes hb4 hw3
  have hw4 : VG.Proof.MlDsa.X86_64.Sign.Pl s4 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) i) := I4.w' 0 (by omega)
  -- `w[i] ← w[i] - cs₂[i] + ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.addAt_ok hP I4.b.l.st.lay ca hw4.1 q4.1) fun s5 ⟨hP5, hcs5, hq5⟩ => ?_)
  rw [hw4.2, q4.2] at hq5
  have L4 := I4.b.l.st.lay
  have hw5 : VG.Proof.MlDsa.X86_64.Sign.Pl s5 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.W''v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP5.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq5
  have J5 : VG.Proof.MlDsa.X86_64.Sign.IHb p D σ t (i + 1) i s5 := ⟨I4.b.step hP5 g5.1.1, Fam.keep L4 hP5 g5.1.2 I4.z,
    Fam.snoc (Fam.keep L4 hP5 f5a I4.w'') hw5, Fam.keep L4 hP5 f5b (I4.w'.shift hi), HFam.keep L4 hP5 g5.2 I4.h,
    (L4.keepW hP5 o5).trans I4.ones⟩
  have r5 : VG.Proof.MlDsa.X86_64.Sign.Pl s5 4 (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) i) := L4.keepPoly hP5 u5 r4
  -- `T4 ← -ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.subAt_ok hP J5.b.l.st.lay cs r5.1 hw5.1) fun s6 ⟨hP6, hcs6, hq6⟩ => ?_)
  rw [r5.2, hw5.2, show VG.Proof.MlDsa.X86_64.Sign.W''v p σ (p.ℓ * t) i = add (VG.Proof.MlDsa.X86_64.Sign.W'v p σ (p.ℓ * t) i) (VG.Proof.MlDsa.X86_64.Sign.CT0v p σ (p.ℓ * t) i) from rfl,
    VG.Proof.MlDsa.X86_64.Sign.sub_add_neg] at hq6
  have J6 := J5.step hP6 g6 o4
  have r6 : VG.Proof.MlDsa.X86_64.Sign.Pl s6 4 (neg (VG.Proof.MlDsa.X86_64.Sign.CT0v p σ (p.ℓ * t) i)) := by show PolyIs _ _ _; rw [hP6.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 4)]; exact hq6
  have hw6 : VG.Proof.MlDsa.X86_64.Sign.Pl s6 (VG.Proof.MlDsa.X86_64.Sign.wBase p + i) (VG.Proof.MlDsa.X86_64.Sign.W''v p σ (p.ℓ * t) i) := J6.w'' i (by omega)
  -- the hint
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.hintCall_ok hP J6.b.l.st.lay hγ ch r6.1 hw6.1) fun s7 ⟨hP7, hcs7, hq7, he7⟩ => ?_)
  rw [r6.2, hw6.2] at hq7 he7
  have J7 := J6.step hP7 g7 o7
  have hh7 : VG.Proof.MlDsa.X86_64.Sign.HFam s7 5 (i + 1) (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t)) :=
    HFam.snoc J7.h (by rw [hP7.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq7)
  -- `ONES`
  have ho7 : s7.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s7 (sc oONES)) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.X86_64.Sign.onesSum (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t)) i) := VG.Proof.MlDsa.X86_64.Sign.ones32 J7.ones
  have L7 := J7.b.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.onesAdd_ok s7 (L7.iR i1) (L7.iW i2)) fun s8 ⟨hm8, k8⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s7 (sc oONES), 8⟩] s7.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨hP8, hcs8⟩ := VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k8 (by decide) hf
  have hP8' : VG.Proof.MlDsa.X86_64.Sign.PPostB D s7 s8 [(sc oONES, 8)] := hP8
  simp only [VG.Proof.MlDsa.X86_64.Sign.hfam, Bool.and_eq_true] at g8
  have hS := VG.Proof.MlDsa.X86_64.Sign.onesSum_le (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t)) i
  have hS1 := VG.Proof.MlDsa.X86_64.Sign.hintOnes_le (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t) i)
  have hik : 256 * (i + 1) ≤ 256 * p.k := Nat.mul_le_mul_left _ hi
  refine ⟨⟨J7.b.step hP8' g8.1.1.1.1, Fam.keep L7 hP8' g8.1.1.1.2 J7.z, Fam.keep L7 hP8' g8.1.1.2 J7.w'',
    Fam.keep L7 hP8' g8.1.2 J7.w', HFam.keep L7 hP8' g8.2 hh7, ?_⟩, ?_⟩
  · rw [hP8'.pa (VG.Proof.MlDsa.X86_64.Sign.sc_bases _), hm8, Mem.readW_writeW_self64, ho7, VG.Proof.MlDsa.X86_64.Sign.onesSum_succ]
    have he7' : ((s7.gpr .rax).setWidth 32).toNat = hintOnes [VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t) i] := he7
    have ea : (s7.gpr .rax).setWidth 32 = BitVec.ofNat 32 (hintOnes [VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq; rw [he7', BitVec.toNat_ofNat]; omega
    have hlt : VG.Proof.MlDsa.X86_64.Sign.onesSum (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t)) i + hintOnes [VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t) i] < 2 ^ 32 := by omega
    rw [ea, ← BitVec.ofNat_add, VG.Proof.MlDsa.X86_64.Sign.sw_ofNat hlt]
  · have e8 : s8.gpr .r15 = s3.gpr .r15 := by
      rw [hcs8 _ (by decide), hcs7 _ (by decide), hcs6 _ (by decide), hcs5 _ (by decide), hcs4 _ (by decide)]
    rw [e8, h3]
    exact VG.Proof.MlDsa.X86_64.Sign.bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
      fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## `ω` -/

theorem onesOk_run (p : Params) (hω : p.ω + 1 < 2 ^ 31) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 4) :
    WP isa (.block (onesOk p)) s fun s' => (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
      ((BitVec.setWidth 64 (s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oONES)) 32) - BitVec.ofNat 64 (p.ω + 1)) >>> 63).setWidth 32) ∧
      s'.mem = s.mem) ∧ Keep [.rax, .r15] s s' := by
  refine WP.keep [.rax, .r15] ?_ (by rfl)
  unfold onesOk
  xrun [h1, VG.Proof.MlDsa.X86_64.Sign.sx_ofNat hω]

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 32) (hw : w < 2 ^ 31) :
    ((BitVec.setWidth 64 (BitVec.ofNat 32 S) - BitVec.ofNat 64 w) >>> 63).setWidth 32 = if S < w then 1 else 0 := by
  rw [VG.Proof.MlDsa.X86_64.Sign.sw_ofNat hS]
  by_cases h : S < w
  · rw [ifp h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · rw [ifn h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-! ## The checks -/

/-- Iteration `t` after `SampleInBall` succeeded. -/
structure KA (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)
  cc : VG.Proof.MlDsa.X86_64.Sign.Pl s 0 (toRq (VG.Proof.MlDsa.X86_64.Sign.cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `CNT = 1`. -/
structure EP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s
  ct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)
  z : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t))
  h : VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t))
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome
  pass : VG.Proof.MlDsa.X86_64.Sign.PassV p σ (p.ℓ * t)
  r15 : s.gpr .r15 = 1
  cnt : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `CNT = 814 - t`. -/
structure EF (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s
  kap : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  cnt : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome
  fail : ¬ VG.Proof.MlDsa.X86_64.Sign.PassV p σ (p.ℓ * t)
  r15 : s.gpr .r15 = 0
  t_lt : t < 814
  rej : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t

/-- What the checks need of the layout. -/
def ksChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) cP && VG.Proof.MlDsa.X86_64.Sign.icwChk p [(cP, 1024), (sc oPS, 1024)] p.k &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oONES) 8 &&
    VG.Proof.MlDsa.X86_64.Sign.kbChk p [(sc oONES, 8)] && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oONES, 8)] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oONES, 8)] (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k &&
    (List.range p.ℓ).all (VG.Proof.MlDsa.X86_64.Sign.zChk p) && (List.range p.k).all (VG.Proof.MlDsa.X86_64.Sign.rChk p) && (List.range p.k).all (VG.Proof.MlDsa.X86_64.Sign.hChk2 p) &&
    VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oONES) 4 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oCNT) 8 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oKAP) 8 &&
    VG.Proof.MlDsa.X86_64.Sign.kbChk p [] &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] 5 p.k &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] 5 p.k &&
    VG.Proof.MlDsa.X86_64.Sign.ikChk p [(sc oCNT, 8)] && VG.Proof.MlDsa.X86_64.Sign.ikChk p [(sc oKAP, 8)] && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oKAP, 8)] (sc oCNT) 8 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) && decide (p.ω + 1 < 2 ^ 31) && decide (p.ℓ < 2 ^ 31) &&
    decide (256 * p.k < 2 ^ 32) && decide (0 < p.ℓ) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oKAP) 8

theorem bit_ne {a : Prop} [Decidable a] : (VG.Proof.MlDsa.X86_64.Sign.bit a).setWidth 32 ≠ 0 ↔ a := by
  by_cases ha : a
  · rw [show VG.Proof.MlDsa.X86_64.Sign.bit a = 1 from ifp ha _ _]; exact ⟨fun _ => ha, fun _ => by decide⟩
  · rw [show VG.Proof.MlDsa.X86_64.Sign.bit a = 0 from ifn ha _ _]; exact ⟨fun h => absurd rfl h, fun h => absurd h ha⟩

theorem bit_and' {a b : Prop} [Decidable a] [Decidable b] :
    BitVec.setWidth 64 ((VG.Proof.MlDsa.X86_64.Sign.bit a).setWidth 32 &&& (if b then (1 : BitVec 32) else 0)) = VG.Proof.MlDsa.X86_64.Sign.bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [VG.Proof.MlDsa.X86_64.Sign.bit, ha, hb]

theorem passV_iff {p : Params} {σ : State} {κ : Nat} :
    (((VG.Proof.MlDsa.X86_64.Sign.ZOk p σ κ ∧ VG.Proof.MlDsa.X86_64.Sign.R0Ok p σ κ) ∧ ∀ j < p.k, normRq [VG.Proof.MlDsa.X86_64.Sign.CT0v p σ κ j] < p.γ₂) ∧ VG.Proof.MlDsa.X86_64.Sign.onesSum (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ) p.k < p.ω + 1) ↔
      VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ :=
  ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, Nat.le_of_lt_succ d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, Nat.lt_succ_of_le d⟩⟩

theorem ksChk_spec {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) : ∀ {Q : Prop}, (VG.Proof.MlDsa.X86_64.Sign.ipChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) cP = true →
    VG.Proof.MlDsa.X86_64.Sign.icwChk p [(cP, 1024), (sc oPS, 1024)] p.k = true →
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) = true → VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oONES) 8 = true →
    VG.Proof.MlDsa.X86_64.Sign.kbChk p [(sc oONES, 8)] = true → VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oONES, 8)] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oONES, 8)] (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k = true →
    (∀ r < p.ℓ, VG.Proof.MlDsa.X86_64.Sign.zChk p r = true) → (∀ i < p.k, VG.Proof.MlDsa.X86_64.Sign.rChk p i = true) → (∀ i < p.k, VG.Proof.MlDsa.X86_64.Sign.hChk2 p i = true) →
    VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oONES) 4 = true → VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oCNT) 8 = true → VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oKAP) 8 = true →
    VG.Proof.MlDsa.X86_64.Sign.kbChk p [] = true → VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] 5 p.k = true → VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] 5 p.k = true → VG.Proof.MlDsa.X86_64.Sign.ikChk p [(sc oCNT, 8)] = true → VG.Proof.MlDsa.X86_64.Sign.ikChk p [(sc oKAP, 8)] = true →
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oKAP, 8)] (sc oCNT) 8 = true → VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) = true →
    p.ω + 1 < 2 ^ 31 → p.ℓ < 2 ^ 31 → 256 * p.k < 2 ^ 32 → 0 < p.ℓ → VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k = true →
    VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oKAP) 8 = true → Q) → Q := by
  intro Q k
  simp only [VG.Proof.MlDsa.X86_64.Sign.ksChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, hz⟩, hr⟩, hh⟩, c8⟩, c9⟩, c10⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, hω⟩, hl⟩, hk⟩, hl0⟩, c22⟩, c23⟩ := hc
  exact k c1 c2 c3 c4 c5 c6 c7 hz hr hh c8 c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 hω hl hk hl0 c22 c23

/-- The checks, after `ĉ = NTT(c)`. -/
structure KN (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s
  y : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Yv p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.wBase p) p.k (VG.Proof.MlDsa.X86_64.Sign.Wv p σ (p.ℓ * t))

theorem cntt_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.KA p D σ t s) : WP isa (nttAt P cP) s (VG.Proof.MlDsa.X86_64.Sign.KN p D σ t) := by
  refine VG.Proof.MlDsa.X86_64.Sign.ksChk_spec hc fun c1 c2 c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have L := h.c.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := ntt) hP.ntt L c1 h.cc.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_
  rw [h.cc.2] at hq1
  have I1 := h.c.step hP1 c2
  exact ⟨⟨I1.l, by rw [L.keepBytes hP1 c3, h.ct], by
    show PolyIs _ _ _; rw [hP1.pa (by decide)]; exact hq1, h.some⟩, I1.y, I1.w⟩

/-- `r15 ← 1`, `ONES ← 0`. -/
abbrev kInit : List Instr := [.mov32 .r15 (.imm 1)] ++ setQ (sc oONES) 0

theorem kInit_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.KN p D σ t s) : WP isa (.block VG.Proof.MlDsa.X86_64.Sign.kInit) s (VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t 0) := by
  refine VG.Proof.MlDsa.X86_64.Sign.ksChk_spec hc fun _ _ _ c4 c5 c6 c7 _ _ _ _ _ _ c13 _ _ c16 _ _ _ _ _ _ _ _ _ c22 _ => ?_
  have L1 := h.b.l.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r15] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r15 = 1) (by xrun) (by decide))
    fun s2 ⟨⟨hm2, h152⟩, k2⟩ => ?_
  have hP2 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s2 [] := (VG.Proof.MlDsa.X86_64.Sign.postB15 k2 hm2 _).1
  have B2 := h.b.step hP2 c13
  have L2 := B2.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setQ_okB L2 (by decide) (by decide) c4) fun s3 ⟨hP3, hcs3, hm3⟩ => ?_
  have y3 := Fam.keep L2 hP3 c6 (Fam.keep L1 hP2 c16 h.y)
  exact ⟨⟨B2.step hP3 c5, fun _ h => absurd h (Nat.not_lt_zero _), y3.zero,
    Fam.keep L2 hP3 c7 (Fam.keep L1 hP2 c22 h.w), by rw [hP3.pa (by decide), hm3, Mem.readW_writeW_self64]; rfl⟩,
    by rw [hcs3 _ (by decide), h152]; exact (bit_one.mpr fun _ h => absurd h (Nat.not_lt_zero _)).symm⟩

theorem IZ.ir {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t p.ℓ s) : VG.Proof.MlDsa.X86_64.Sign.IR p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w.zero, h.1.ones⟩,
    by rw [h.2]; exact VG.Proof.MlDsa.X86_64.Sign.bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

theorem IR.ih {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IR p D σ t p.k s) : VG.Proof.MlDsa.X86_64.Sign.IH p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w'.zero, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h.1.ones]; rfl⟩,
    by rw [h.2]; exact VG.Proof.MlDsa.X86_64.Sign.bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-- The checks done: whether the iteration passes in `r15`. -/
structure KO (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.X86_64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t))
  h : VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t))
  r15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Sign.bit (VG.Proof.MlDsa.X86_64.Sign.PassV p σ (p.ℓ * t))

theorem onesOk_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.IH p D σ t p.k s) : WP isa (.block (onesOk p)) s (VG.Proof.MlDsa.X86_64.Sign.KO p D σ t) := by
  refine VG.Proof.MlDsa.X86_64.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ c13 _ _ c16 c17 _ _ _ _ hω _ hk _ _ _ => ?_
  obtain ⟨J6, h156⟩ := h
  have L6 := J6.b.l.st.lay
  have hS := VG.Proof.MlDsa.X86_64.Sign.onesSum_le (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t)) p.k
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.onesOk_run p hω s (L6.iR c8)) fun s7 ⟨⟨h157, hm7⟩, k7⟩ => ?_
  rw [VG.Proof.MlDsa.X86_64.Sign.ones32 J6.ones, VG.Proof.MlDsa.X86_64.Sign.sign_bit (by omega) (by omega), h156, VG.Proof.MlDsa.X86_64.Sign.bit_and', VG.Proof.MlDsa.X86_64.Sign.bit_congr VG.Proof.MlDsa.X86_64.Sign.passV_iff] at h157
  have hP7 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s7 [] := ⟨k7.2.1, k7.2.2, fun r hr => k7.gpr (by
      simp only [VG.Proof.MlDsa.X86_64.Sign.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k7.gpr (by decide),
      by rw [hm7]; exact Frame.refl _ _⟩
  exact ⟨J6.b.step hP7 c13, Fam.keep L6 hP7 c16 J6.z, HFam.keep L6 hP7 c17 J6.h, h157⟩

/-- `κ ← κ + ℓ`. -/
abbrev kapAdd (p : Params) : List Instr := [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oKAP)),
  .alu .add .rax (.imm (BitVec.ofNat 32 p.ℓ)), .store (VG.Impl.MlKem.X86_64.at_ .rbx oKAP) .rax]

theorem kBranch_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.KO p D σ t s) :
    WP isa (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (VG.Proof.MlDsa.X86_64.Sign.kapAdd p))) s fun s' => VG.Proof.MlDsa.X86_64.Sign.EP p D σ t s' ∨ VG.Proof.MlDsa.X86_64.Sign.EF p D σ t s' := by
  refine VG.Proof.MlDsa.X86_64.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 _ hl _ _ _ c23 => ?_
  have B7 := h.b
  have L7 := B7.l.st.lay
  refine VG.Proof.MlDsa.X86_64.Sign.ifOkElse_ok (D := D) (fun s8 hP8 hcs8 hm8 hne => ?_) fun s8 hP8 hcs8 hm8 he => ?_
  · rw [h.r15] at hne
    have hpass := bit_ne.mp hne
    have B8 := B7.step hP8 c13
    have L8 := B8.l.st.lay
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setQ_okB L8 (by decide) (by decide) c9) fun s9 ⟨hP9, hcs9, hm9⟩ => ?_
    exact .inl ⟨B8.l.k.step hP9 c18, by rw [L8.keepBytes hP9 c21, B8.ct],
      Fam.keep L8 hP9 c14 (Fam.keep L7 hP8 c16 h.z), HFam.keep L8 hP9 c15 (HFam.keep L7 hP8 c17 h.h), B8.some,
      hpass, by rw [hcs9 _ (by decide), hcs8 _ (by decide), h.r15]; exact bit_one.mpr hpass,
      by rw [hP9.pa (by decide), hm9, Mem.readW_writeW_self64]; rfl, B8.l.t_lt, B8.l.rej⟩
  · rw [h.r15] at he
    have hfail : ¬ VG.Proof.MlDsa.X86_64.Sign.PassV p σ (p.ℓ * t) := fun hp => (bit_ne.mpr hp) he
    have B8 := B7.step hP8 c13
    have L8 := B8.l.st.lay
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.addQ_ok (sc oKAP) p.ℓ (by decide) hl s8 (L8.iW c10) (L8.iR c23)) fun s9 ⟨hm9, k9⟩ => ?_
    have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s8 (sc oKAP), 8⟩] s8.mem s9.mem := by
      rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain ⟨hP9, hcs9⟩ := VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k9 (by decide) hf
    have hP9' : VG.Proof.MlDsa.X86_64.Sign.PPostB D s8 s9 [(sc oKAP, 8)] := hP9
    refine .inr ⟨B8.l.k.step hP9' c19, ?_, by rw [L8.keepW hP9' c20, B8.l.cnt], B8.some, hfail,
      by rw [hcs9 _ (by decide), hcs8 _ (by decide), h.r15]; exact bit_zero.mpr hfail, B8.l.t_lt, B8.l.rej⟩
    rw [hP9'.pa (by decide), hm9, Mem.readW_writeW_self64, B8.l.kap, VG.Proof.MlDsa.X86_64.Sign.ofNat64_add, Nat.mul_succ]

theorem checks_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.KA p D σ t s) :
    WP isa (checks P p) s fun s' => VG.Proof.MlDsa.X86_64.Sign.EP p D σ t s' ∨ VG.Proof.MlDsa.X86_64.Sign.EF p D σ t s' := by
  refine VG.Proof.MlDsa.X86_64.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.cntt_ok hP hc h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.kInit_ok hc h1) fun s3 I3 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t r) p.ℓ 0 (fun r _ hr s hs => VG.Proof.MlDsa.X86_64.Sign.zR_ok hP (hz r (by omega)) hs)
    s3 I3) fun s4 hs4 => ?_)
  rw [Nat.zero_add] at hs4
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Sign.IR p D σ t i) p.k 0 (fun i _ hi s hs => VG.Proof.MlDsa.X86_64.Sign.r0R_ok hP (hr i (by omega)) hs)
    s4 hs4.ir) fun s5 hs5 => ?_)
  rw [Nat.zero_add] at hs5
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Sign.IH p D σ t i) p.k 0 (fun i _ hi s hs => VG.Proof.MlDsa.X86_64.Sign.hR_ok hP (hh i (by omega)) hs)
    s5 hs5.ih) fun s6 hs6 => ?_)
  rw [Nat.zero_add] at hs6
  exact WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.onesOk_ok hc hs6) fun s7 h7 => VG.Proof.MlDsa.X86_64.Sign.kBranch_ok hc h7)

theorem ksChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem bChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.bChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseL`. -/
section

/-!
# ML-DSA signing on x86-64: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `r15 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `r15 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem paramsOk {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : ParamsOk p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    VG.Proof.MlDsa.X86_64.Sign.iterF p σ b κ = (sampleInBall p.τ b.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)).map fun c =>
      (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ, if passF p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S1v p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.T0v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (VG.Proof.MlDsa.X86_64.Sign.S1v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ c),
          (List.range p.k).map (hF p (VG.Proof.MlDsa.X86_64.Sign.Am p σ) (VG.Proof.MlDsa.X86_64.Sign.S2v p σ) (VG.Proof.MlDsa.X86_64.Sign.T0v p σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ) = some (VG.Proof.MlDsa.X86_64.Sign.cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [VG.Proof.MlDsa.X86_64.Sign.cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)).isSome)
    (hf : ¬ VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ) : VG.Proof.MlDsa.X86_64.Sign.iterF p σ maxBounds κ = some (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ, none) := by
  rw [VG.Proof.MlDsa.X86_64.Sign.iterF_eq hp, VG.Proof.MlDsa.X86_64.Sign.cV_eq h, Option.map_some, ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)).isSome)
    (hf : VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ) : VG.Proof.MlDsa.X86_64.Sign.iterF p σ maxBounds κ =
      some (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ, some ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ), (List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ))) := by
  rw [VG.Proof.MlDsa.X86_64.Sign.iterF_eq hp, VG.Proof.MlDsa.X86_64.Sign.cV_eq h, Option.map_some, ifp hf]

theorem iter_none (h : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ) = none) : VG.Proof.MlDsa.X86_64.Sign.iterF p σ minBounds κ = none := by
  rw [VG.Proof.MlDsa.X86_64.Sign.iterF, signIteration_eq, signCommit_eq, h]; rfl

end

/-! ## The end of the loop -/

/-- The loop ended: in `r15`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s
  r01 : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1
  pass : s.gpr .r15 = 1 → ∃ t < 814, VG.Proof.MlDsa.X86_64.Sign.RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome ∧ VG.Proof.MlDsa.X86_64.Sign.PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t) ∧ VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ (p.ℓ * t)) ∧
    VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ (p.ℓ * t))
  fail : s.gpr .r15 = 0 → VG.Proof.MlDsa.X86_64.Sign.loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `r15 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s
  none : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)) = none
  r15 : s.gpr .r15 = 0
  cnt : s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t

theorem rej_zero {p : Params} {σ : State} {t : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t) :
    Rej p (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ))
      ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) maxBounds 0 t := h

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t)) = none) : VG.Proof.MlDsa.X86_64.Sign.loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.X86_64.Sign.iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : VG.Proof.MlDsa.X86_64.Sign.RejT p σ 814) : VG.Proof.MlDsa.X86_64.Sign.loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## An iteration -/

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.zf = some false ∧ VG.Proof.MlDsa.X86_64.Sign.IL p D σ (t + 1) s) ∨ (s.zf = some true ∧ VG.Proof.MlDsa.X86_64.Sign.XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oCNT) 8 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc oCNT) 8 && VG.Proof.MlDsa.X86_64.Sign.ikChk p [(sc oCNT, 8)] && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (sc oKAP) 8 &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oCNT, 8)] 5 p.k && VG.Proof.MlDsa.X86_64.Sign.icwChk p [] p.k && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (sc oCT) (cLen p) &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] cP 1024 && VG.Proof.MlDsa.X86_64.Sign.ikChk p [] &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(sc oKAP, 8)] (sc oCNT) 8 && VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgW p) (sc oKAP) 8 && VG.Proof.MlDsa.X86_64.Sign.ikChk p [(sc oKAP, 8)]

theorem lChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ofNat64_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 64) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) :=
  VG.Proof.MlKem.X86_64.ofNat64_pred h hk

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.X86_64.Sign.EF p D σ t s ∨ VG.Proof.MlDsa.X86_64.Sign.EB p D σ t s) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
      .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) s (VG.Proof.MlDsa.X86_64.Sign.LP p D σ t) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.decQ_ok (sc oCNT) (by decide) s (L.iW w1) (L.iR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨hP', hcs⟩ := VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf
  have hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(sc oCNT, 8)] := hP'
  have K := hk.step hP k1
  have e15 : s'.gpr .r15 = s.gpr .r15 := hcs _ (by decide)
  rcases h with h | h | h
  · -- passed
    rw [h.cnt] at hz
    refine .inr ⟨by rw [hz]; rfl, K, .inr (e15.trans h.r15), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.r15)) (by decide)⟩
  · -- rejected
    have hr : VG.Proof.MlDsa.X86_64.Sign.RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.X86_64.Sign.iter_rej hp h.some h.fail)
    rw [h.cnt, VG.Proof.MlDsa.X86_64.Sign.ofNat64_sub_one (by have := h.t_lt; omega) (by have := h.t_lt; omega),
      VG.Proof.MlKem.X86_64.ofNat64_beq_zero (by have := h.t_lt; omega)] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r15),
        fun h1 => absurd (h1.symm.trans (e15.trans h.r15)) (by decide), fun _ => VG.Proof.MlDsa.X86_64.Sign.loop_none_exh hr⟩
    · have hne : decide (814 - t - 1 = 0) = false := by have := h.t_lt; simp only [decide_eq_false_iff_not]; omega
      refine .inl ⟨by rw [hz, hne], K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega, hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self64, h.cnt,
        VG.Proof.MlDsa.X86_64.Sign.ofNat64_sub_one (by have := h.t_lt; omega) (by have := h.t_lt; omega), Nat.sub_sub]
  · -- `SampleInBall` failed
    rw [h.cnt] at hz
    exact .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r15),
      fun h1 => absurd (h1.symm.trans (e15.trans h.r15)) (by decide), fun _ => VG.Proof.MlDsa.X86_64.Sign.loop_none_ball h.rej h.none⟩

theorem testRax_ok (s : State) : WP isa (.block [.alu32 .test .rax (.reg .rax)]) s fun s₁ =>
    (s₁.mem = s.mem ∧ s₁.gpr .rax = s.gpr .rax ∧
      s₁.zf = some (((s.gpr .rax).setWidth 32 &&& (s.gpr .rax).setWidth 32) == 0)) ∧ Keep [.rax] s s₁ :=
  WP.keep [.rax] (by xrun) (by decide)

theorem IB.step0 {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s) (hc : VG.Proof.MlDsa.X86_64.Sign.lChk p = true)
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' []) (hax : s'.gpr .rax = s.gpr .rax) : VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, c1⟩, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := h.c.l.st.lay
  refine ⟨h.c.step hP c1, by rw [L.keepBytes hP c2, h.ct], hax ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (hax ▸ h0)⟩
  obtain ⟨hc', hs⟩ := h.ok (hax ▸ h1)
  exact ⟨L.keepPoly hP c3 hc', hs⟩

theorem test_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s) :
    WP isa (.block [.alu32 .test .rax (.reg .rax)]) s fun s' =>
      (VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s' ∧ s'.zf = some ((s'.gpr .rax).setWidth 32 == 0)) ∧
        (s'.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32 := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.testRax_ok s) fun s3 ⟨⟨hm3, hax3, hz3⟩, k3⟩ => ?_
  have hf3 : Frame [] s.mem s3.mem := by rw [hm3]; exact Frame.refl _ _
  obtain ⟨hP3', _⟩ := VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k3 (by decide) hf3
  have hP3 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s3 [] := hP3'
  rw [BitVec.and_self] at hz3
  exact ⟨⟨h.step0 hc4 hP3 hax3, by rw [hz3, hax3]⟩, by rw [hax3]⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s)
    (h1 : (s.gpr .rax).setWidth 32 = 1) : VG.Proof.MlDsa.X86_64.Sign.KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem else_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s)
    (h0 : (s.gpr .rax).setWidth 32 = 0) :
    WP isa (.block (([.mov32 .r15 (.imm 0)] : List Instr) ++ setQ (sc oCNT) 1)) s (VG.Proof.MlDsa.X86_64.Sign.EB p D σ t) := by
  have hc4' := hc4
  simp only [VG.Proof.MlDsa.X86_64.Sign.lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r15] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r15 = 0) (by xrun) (by decide))
    fun s4 ⟨⟨hm4, h154⟩, k4⟩ => ?_
  have hP4 : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s4 [] := (VG.Proof.MlDsa.X86_64.Sign.postB15 k4 hm4 _).1
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setQ_okB L4 (by decide) (by decide) w1) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5 _ (by decide), h154],
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self64]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {s : State} (hk : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
      .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) s fun s' =>
      s'.zf = some (s.mem.readW (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT)) 64 - 1 == 0) ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' (sc oCT)) (cLen p) = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) ∧
      ∀ f, VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.X86_64.Sign.HFam s' 5 p.k f := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.decQ_ok (sc oCNT) (by decide) s (L.iW w1) (L.iR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨hP', hcs⟩ := VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide) hf
  have hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [(sc oCNT, 8)] := hP'
  exact ⟨hz, hcs _ (by decide), L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem iter_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.X86_64.Sign.cChk p = true)
    (hc2 : VG.Proof.MlDsa.X86_64.Sign.bChk p = true) (hc3 : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) : WP isa (iter P p) s (VG.Proof.MlDsa.X86_64.Sign.LP p D σ t) := by
  unfold iter
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.ball_ok hP hc2 h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.test_ok hc4 h2) fun s3 ⟨⟨I3, hz3⟩, _⟩ => ?_)
  refine WP.seq (WP.ite (!((s3.gpr .rax).setWidth 32 == 0)) (show s3.zf.map (!·) = _ by rw [hz3]; rfl)
    (fun hb => ?_) fun hb => ?_)
  · have h1 : (s3.gpr .rax).setWidth 32 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.checks_ok hP hc3 (I3.ka h1)) fun s' h' => VG.Proof.MlDsa.X86_64.Sign.dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.else_ok hc4 I3 (by simpa using hb)) fun s' h' => VG.Proof.MlDsa.X86_64.Sign.dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) :
    WP isa (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) s (VG.Proof.MlDsa.X86_64.Sign.IL p D σ 0) := by
  have hc4' := hc4
  simp only [VG.Proof.MlDsa.X86_64.Sign.lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setQ_okB L (by decide) (by decide) wk) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setQ_okB K1.d.im.st.lay (by decide) (by decide) w1) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self64]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self64], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.X86_64.Sign.cChk p = true)
    (hc2 : VG.Proof.MlDsa.X86_64.Sign.bChk p = true) (hc3 : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {σ : State} {s : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) : WP isa (Impl.MlDsa.X86_64.Sign.signLoop P p) s (VG.Proof.MlDsa.X86_64.Sign.XS p D σ) := by
  unfold Impl.MlDsa.X86_64.Sign.signLoop
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.iter_ok hP hp hc1 hc2 hc3 hc4 hs) fun s' h' => ?_
  have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [hev, hz]; rfl, 814 - (t + 1), by have := hs.t_lt; omega, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [hev, hz]; rfl, hX⟩

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseO`. -/
section

/-!
# ML-DSA signing on x86-64: the signature

Once an iteration passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r`
(in range, as `z` passed its norm check: `inRange_of_norm`), then
`HintBitPack(h)` (with at most `ω` 1s) to `sig`, which then holds
`sigEncode(c̃, z mod± q, h)` (`output_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : VG.Proof.MlDsa.X86_64.Sign.InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [VG.Proof.MlDsa.X86_64.Sign.coeff_val h hi]
  simp only [normZq] at this
  omega

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [VG.Proof.MlKem.X86_64.off_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = VG.Proof.MlDsa.X86_64.Sign.onesSum f k := by
  simp only [hintOnes, VG.Proof.MlDsa.X86_64.Sign.onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    VG.Proof.MlDsa.X86_64.Sign.pa s (pS (5 + i)) = VG.Proof.MlDsa.X86_64.Sign.pa s (Impl.MlDsa.X86_64.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show s.gpr .rbx + BitVec.ofNat 64 (VG.Impl.MlDsa.X86_64.Sign.oP (5 + i)) = s.gpr .rbx + BitVec.ofNat 64 (VG.Impl.MlDsa.X86_64.Sign.oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [VG.Proof.MlKem.X86_64.off_add, show VG.Impl.MlDsa.X86_64.Sign.oP (5 + 0) + 1024 * i = VG.Impl.MlDsa.X86_64.Sign.oP (5 + i) by simp only [VG.Impl.MlDsa.X86_64.Sign.oP]; omega]

theorem r14_bases (o : Nat) : ((.r14, o) : Ptr).1 ∈ VG.Proof.MlDsa.X86_64.Sign.bases := by
  show Reg.r14 ∈ VG.Proof.MlDsa.X86_64.Sign.bases; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s
  z : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ)
  h : VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ)
  sig : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (.r14, 0)) (cLen p + zLen p * r) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ ++ VG.Proof.MlDsa.X86_64.Sign.zEnc p σ κ r
  r15 : s.gpr .r15 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.ikChk p ws && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.X86_64.Sign.ofam p ws = true)
    (hs : VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) ws (.r14, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .r15 = s.gpr .r15) :
    VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ r s' := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ofam, Bool.and_eq_true] at hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.r15⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.copyChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (.r14, 0) (sc oCT) (cLen p) && VG.Proof.MlDsa.X86_64.Sign.ofam p [((.r14, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => VG.Proof.MlDsa.X86_64.Sign.rwChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (yP p r) 1024 (.r14, sigZ p r) (zLen p) &&
      VG.Proof.MlDsa.X86_64.Sign.ofam p [((.r14, sigZ p r), zLen p)] && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [((.r14, sigZ p r), zLen p)] (.r14, 0) (cLen p + zLen p * r)) &&
    VG.Proof.MlDsa.X86_64.Sign.rwChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) (hP 0) (256 * p.k * 4) (.r14, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    VG.Proof.MlDsa.X86_64.Sign.ikChk p [((.r14, sigH p), p.ω + p.k)] &&
    VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [((.r14, sigH p), p.ω + p.k)] (.r14, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ, (List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ), (List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ))

section
variable {P : Prims} {D : Nat} (hPO : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.oChk p = true) {σ : State} {κ : Nat}
include hc

omit hPO in
theorem outCopy_ok {s : State} (hk : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) (hct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)
    (hz : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ)) (hh : VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ)) (h15 : s.gpr .r15 = 1) :
    WP isa (copy (.r14, 0) (sc oCT) (cLen p)) s fun s1 =>
      VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ 0 s1 ∧ ∀ f, VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.X86_64.Sign.HFam s1 5 p.k f := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_
  simp only [VG.Proof.MlDsa.X86_64.Sign.ofam, Bool.and_eq_true] at c0
  refine ⟨⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
    by rw [hcs1 _ (by decide), h15]⟩, fun f h => HFam.keep L hP1 c0.2 h⟩
  rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
  simp [VG.Proof.MlDsa.X86_64.Sign.zEnc]

include hPO in
theorem packZ_ok {r : Nat} (hr : r < p.ℓ) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ r s) (hpass : VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ) :
    WP isa (packZ P p r) s fun s' => VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ (r + 1) s' ∧ ∀ f, VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.X86_64.Sign.HFam s' 5 p.k f := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, cz⟩, -⟩, -⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := cz r hr
  have Lh := h.k.d.im.st.lay
  have hzr := h.z r hr
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.bpAt_ok hPO Lh hbp hzl c1 hzr.1 (VG.Proof.MlDsa.X86_64.Sign.inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)))
    fun s' ⟨hP', hcs', hb'⟩ => ?_
  have O' := h.step hP' c2 c3 (hcs' _ (by decide))
  have c2' := c2
  simp only [VG.Proof.MlDsa.X86_64.Sign.ofam, Bool.and_eq_true] at c2'
  refine ⟨⟨O'.k, O'.z, O'.h, ?_, O'.r15⟩, fun f hf => HFam.keep Lh hP' c2'.2 hf⟩
  rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, VG.Proof.MlDsa.X86_64.Sign.pa_add, Nat.zero_add,
    hP'.pa (VG.Proof.MlDsa.X86_64.Sign.r14_bases _), hb', hzr.2, VG.Proof.MlDsa.X86_64.Sign.zEnc, VG.Proof.MlDsa.X86_64.Sign.zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

omit hc in
theorem hones_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ p.ℓ s) (hpass : VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ) :
    hintOnes (hintAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (Impl.MlDsa.X86_64.Sign.hP 0)) p.k) ≤ p.ω := by
  rw [VG.Proof.MlDsa.X86_64.Sign.hintAt_of (f := VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ) fun i hi => by
      have := h.h i hi; rwa [VG.Proof.MlDsa.X86_64.Sign.pS_hint] at this,
    VG.Proof.MlDsa.X86_64.Sign.hintOnes_map]
  exact hpass.2.2.2

include hPO in
theorem hpack_ok {s : State} (h2 : VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ p.ℓ s) (hpass : VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ) :
    WP isa (hintBitPackAt P (Impl.MlDsa.X86_64.Sign.hP 0) (256 * p.k) p.ω (.r14, sigH p) (p.ω + p.k)) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sign.IK p D σ s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' (.r14, 0)) p.sigLen = VG.Proof.MlDsa.X86_64.Sign.sigV p σ κ ∧ s'.gpr .r15 = 1 := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ch⟩, hhp⟩, -⟩, -⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L2 := h2.k.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.hbpAt_ok hPO L2 hhp ch (VG.Proof.MlDsa.X86_64.Sign.hones_ok h2 hpass)) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3 _ (by decide), h2.r15]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), VG.Proof.MlDsa.X86_64.Sign.pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, VG.Proof.MlDsa.X86_64.Sign.hintAt_of (f := VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [VG.Proof.MlDsa.X86_64.Sign.pS_hint] at this]
  simp only [VG.Proof.MlDsa.X86_64.Sign.sigV, sigOf, sigEncode, VG.Proof.MlDsa.X86_64.Sign.zEnc, List.map_map, List.flatMap_map]
  rfl

include hPO in
theorem output_ok {s : State} (hk : VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) (hct : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)
    (hz : VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ)) (hh : VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ)) (hpass : VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ)
    (h15 : s.gpr .r15 = 1) :
    WP isa (output P p) s fun s' => VG.Proof.MlDsa.X86_64.Sign.IK p D σ s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Sign.pa s' (.r14, 0)) p.sigLen = VG.Proof.MlDsa.X86_64.Sign.sigV p σ κ ∧
      s'.gpr .r15 = 1 := by
  unfold output
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.outCopy_ok hc hk hct hz hh h15) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ r) p.ℓ 0
    (fun r _ hr s h => WP.mono (VG.Proof.MlDsa.X86_64.Sign.packZ_ok hPO hc (by omega) h hpass) fun _ h => h.1) s1 h1.1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact VG.Proof.MlDsa.X86_64.Sign.hpack_ok hPO hc h2 hpass

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Correct`. -/
section

/-!
# ML-DSA signing on x86-64: correctness

The function returns 1 with `Sign_internal`'s signature (within `maxBounds`)
in `sig`, or 0 when `Sign_internal` returns nothing within `minBounds`
(`sign_correct`): its `ExpandA` or its loop does not finish (`signMu_min_A`,
`signMu_min_L`), or an iteration passes (`signMu_max`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.X86_64.Sign.seedE p σ (p.ℓ * i + j) = aSeed (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.X86_64.Sign.seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.seedE p σ e)).isSome) :
    expandA p maxBounds (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)) :=
  expandA_some fun i hi j hj => by rw [← VG.Proof.MlDsa.X86_64.Sign.seedE_ij hj]; exact hok _ (VG.Proof.MlDsa.X86_64.Sign.ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.X86_64.Sign.seedE p σ e) = none) :
    signMu p minBounds (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)))
    (hL : VG.Proof.MlDsa.X86_64.Sign.loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rndOf σ) = none := by
  cases e : expandA p minBounds (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ))) {t : Nat}
    (ht : t < 814) (hr : VG.Proof.MlDsa.X86_64.Sign.RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ (p.ℓ * t))).isSome)
    (hpass : VG.Proof.MlDsa.X86_64.Sign.PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rndOf σ) = some (VG.Proof.MlDsa.X86_64.Sign.sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega) (VG.Proof.MlDsa.X86_64.Sign.iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `r15`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : VG.Proof.MlDsa.X86_64.Sign.St p D σ s
  r01 : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1
  ok : s.gpr .r15 = 1 →
    signMu p maxBounds (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rndOf σ) = some (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (.r14, 0)) p.sigLen)
  bad : s.gpr .r15 = 0 → signMu p minBounds (VG.Proof.MlDsa.X86_64.Sign.skOf p σ) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.stChk p [] && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.aBase p) (p.k * p.ℓ) && VG.Proof.MlDsa.X86_64.Sign.ikChk p [] && VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.X86_64.Sign.famChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] 5 p.k && VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [] (sc oCT) (cLen p) &&
    (List.range 6).all (fun k => VG.Proof.MlDsa.X86_64.Sign.inB (VG.Proof.MlDsa.X86_64.Sign.sgB p) (sc (oSV + 8 * k)) 8) &&
    decide (VG.Proof.MlDsa.X86_64.Sign.scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32)

theorem fChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Sign.aChk p && VG.Proof.MlDsa.X86_64.Sign.dChk p && VG.Proof.MlDsa.X86_64.Sign.cChk p && VG.Proof.MlDsa.X86_64.Sign.bChk p && VG.Proof.MlDsa.X86_64.Sign.ksChk p && VG.Proof.MlDsa.X86_64.Sign.lChk p && VG.Proof.MlDsa.X86_64.Sign.oChk p && VG.Proof.MlDsa.X86_64.Sign.fChk p

theorem allChk_ok {p : Params} (h : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) : VG.Proof.MlDsa.X86_64.Sign.allChk p = true := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.allChk, VG.Proof.MlDsa.X86_64.Sign.aChk_ok h, VG.Proof.MlDsa.X86_64.Sign.dChk_ok h, VG.Proof.MlDsa.X86_64.Sign.cChk_ok h, VG.Proof.MlDsa.X86_64.Sign.bChk_ok h, VG.Proof.MlDsa.X86_64.Sign.ksChk_ok h, VG.Proof.MlDsa.X86_64.Sign.lChk_ok h, VG.Proof.MlDsa.X86_64.Sign.oChk_ok h, VG.Proof.MlDsa.X86_64.Sign.fChk_ok h,
    Bool.and_self]

theorem r15_one {s : State} (h : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1) (hne : (s.gpr .r15).setWidth 32 ≠ 0) :
    s.gpr .r15 = 1 := by
  rcases h with e | e
  · rw [e] at hne; exact absurd rfl hne
  · exact e

theorem r15_zero {s : State} (h : s.gpr .r15 = 0 ∨ s.gpr .r15 = 1) (he : (s.gpr .r15).setWidth 32 = 0) :
    s.gpr .r15 = 0 := by
  rcases h with e | e
  · exact e
  · rw [e] at he; exact absurd he (by decide)

theorem rest_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IM p D σ s) :
    WP isa (rest P p) s (VG.Proof.MlDsa.X86_64.Sign.FS p D σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.X86_64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.X86_64.Sign.fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf'
  have hp := VG.Proof.MlDsa.X86_64.Sign.paramsOk h3
  have hA := VG.Proof.MlDsa.X86_64.Sign.expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.decode_ok hP hd h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.signLoop_ok hP hp hc1 hb hks hl h1) fun s2 h2 => ?_)
  have L2 := h2.k.d.im.st.lay
  unfold ifOk
  refine VG.Proof.MlDsa.X86_64.Sign.ifOkElse_ok (D := D) (fun s3 hP3 hcs3 hm3 hne => ?_) fun s3 hP3 hcs3 hm3 he => ?_
  · have h15 := VG.Proof.MlDsa.X86_64.Sign.r15_one h2.r01 hne
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h15
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.output_ok hP ho (h2.k.step hP3 ik) (by rw [L2.keepBytes hP3 kct, hct])
      (Fam.keep L2 hP3 fy hz) (HFam.keep L2 hP3 f5 hh) hpass (by rw [hcs3 _ (by decide), h15]))
      fun s4 ⟨k4, hb4, h154⟩ => ⟨k4.d.im.st, .inr h154, fun _ => by rw [hb4]; exact VG.Proof.MlDsa.X86_64.Sign.signMu_max hp hA ht hr hs hpass,
        fun h0 => absurd (h0.symm.trans h154) (by decide)⟩
  · have h15 := VG.Proof.MlDsa.X86_64.Sign.r15_zero h2.r01 he
    have e15 : s3.gpr .r15 = 0 := by rw [hcs3 _ (by decide), h15]
    exact WP.block_nil ⟨(h2.k.step hP3 ik).d.im.st, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
      fun _ => VG.Proof.MlDsa.X86_64.Sign.signMu_min_L hA (h2.fail h15)⟩

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨σ.gpr r, len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (b, 0)) len = bytesAt σ.mem (σ.gpr r) len := by
  rw [VG.Proof.MlDsa.X86_64.Sign.pa, hb, VG.Proof.MlKem.X86_64.add_ofNat_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) {σ s : State}
    (hpre : (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ) (ht : VG.Proof.MlDsa.X86_64.Sign.Top σ s) (hf : Frame [⟨σ.gpr .r8, VG.Proof.MlDsa.X86_64.Sign.scrLen p⟩] σ.mem s.mem) : VG.Proof.MlDsa.X86_64.Sign.St p D σ s := by
  have hc := VG.Proof.MlDsa.X86_64.Sign.fChk_ok h3
  simp only [VG.Proof.MlDsa.X86_64.Sign.fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hsz := hc.2
  have hpre' := hpre
  obtain ⟨_, _, d1, d2, d3, d4, d5, d6, d7, _, _, _, _, _, _, _, _, _, _, n1, n2, n3, n4, n5, _⟩ := hpre'
  exact ⟨ht, VG.Proof.MlDsa.X86_64.Sign.sgLay hpre hP.hD' hsz ht,
    VG.Proof.MlDsa.X86_64.Sign.entry_bytes hf d2 (by omega) (ht.regs (.rbp, .rdi) (by decide)),
    VG.Proof.MlDsa.X86_64.Sign.entry_bytes hf d4 (by omega) (ht.regs (.r12, .rsi) (by decide)),
    VG.Proof.MlDsa.X86_64.Sign.entry_bytes hf d6 (by omega) (ht.regs (.r13, .rdx) (by decide))⟩

theorem sign_correct {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.X86_64.Sign.Ok3 p)
    (hmx : ctlOk (Impl.MlDsa.X86_64.Sign.sign P p) = true) (σ : State)
    (hpre : (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ) :
    ∃ t s', Exec isa (Impl.MlDsa.X86_64.Sign.sign P p) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlDsa.X86_64.Sign.signK p D).post σ s' := by
  have hc := VG.Proof.MlDsa.X86_64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.X86_64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.X86_64.Sign.fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, hsv⟩, hsz⟩ := hf'
  have main : WP isa (Impl.MlDsa.X86_64.Sign.sign P p) σ fun s₅ => gprPreserved σ s₅ ∧
      ∃ s₄, VG.Proof.MlDsa.X86_64.Sign.FS p D σ s₄ ∧ (s₅.gpr .rax).setWidth 32 = (s₄.gpr .r15).setWidth 32 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.X86_64.Sign.sign
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.pro_ok hpre hsz.1) fun s₁ ⟨h₁, _, hf₁, h15⟩ => ?_)
    have S1 := VG.Proof.MlDsa.X86_64.Sign.entry_st hP h3 hpre h₁ hf₁
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.expandA_ok hP ha S1 h15) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (VG.Proof.MlDsa.X86_64.Sign.FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine VG.Proof.MlDsa.X86_64.Sign.ifOkElse_ok (D := D) (fun s₃ hP₃ hcs₃ hm₃ hne => ?_) fun s₃ hP₃ hcs₃ hm₃ he => ?_
      · have h1 := VG.Proof.MlDsa.X86_64.Sign.r15_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact VG.Proof.MlDsa.X86_64.Sign.rest_ok hP h3 ⟨h₂.st.step hP₃ st0, ok, Fam.keep h₂.st.lay hP₃ fa0 fam⟩
      · have h0 := VG.Proof.MlDsa.X86_64.Sign.r15_zero h₂.r01 he
        have e15 : s₃.gpr .r15 = 0 := by rw [hcs₃ _ (by decide), h0]
        exact WP.block_nil ⟨h₂.st.step hP₃ st0, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
          fun _ => VG.Proof.MlDsa.X86_64.Sign.signMu_min_A (h₂.bad h0)⟩
    · exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.topEpi_ok h₄.st.top fun k hk => h₄.st.lay.iR (hsv k hk)) fun s₅ ⟨hr, hg, hm⟩ =>
        ⟨hg, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, abiPreserved_of_ctl hmx he hg, ?_⟩
  have e14 : VG.Proof.MlDsa.X86_64.Sign.pa s₄ (.r14, 0) = σ.gpr .rcx := by
    rw [VG.Proof.MlDsa.X86_64.Sign.pa, h₄.st.top.regs (.r14, .rcx) (by decide), VG.Proof.MlKem.X86_64.add_ofNat_zero]
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0]; rfl, h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1]; rfl, maxBounds, by rw [hm, ← e14]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Rel`. -/
section

/-!
# ML-DSA signing on x86-64: two runs

Constant time is proven piece by piece (`RelCT`) for two runs from entry
states that satisfy `signK`'s precondition and agree on its public data, each
satisfying the invariant `I` of the correctness proof, and related by `E`
(`RR`): each piece leaks the same, correctness gives each run's next
invariant, and the piece's own proof the next relation (`relInvE`). The runs
are in the same layout (`RR.lrel`) and agree on `ρ` (`RR.rho`), which the
leakage begins with.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Rel2)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (D : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre (VG.Proof.MlDsa.X86_64.Sign.signK p D).pub I x y ∧ E x y

section
variable {p : Params} {D : Nat}

theorem relInvE {I J E E' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D I E) c E') : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D I E) c (VG.Proof.MlDsa.X86_64.Sign.RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', he⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, he⟩

theorem RR.mono {I I' E E' : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.X86_64.Sign.RR p D I E x y)
    (hI : ∀ σ s, I σ s → I' σ s) (hE : E x y → E' x y) : VG.Proof.MlDsa.X86_64.Sign.RR p D I' E' x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, e⟩ := h
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, hI _ _ i₁, hI _ _ i₂⟩, hE e⟩

theorem RR.lrel {I E : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Sign.St p D σ s) {x y : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.RR p D I E x y) : VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y := by
  obtain ⟨⟨σ₁, σ₂, _, _, hpub, i₁, i₂⟩, _⟩ := h
  have S₁ := hI _ _ i₁
  have S₂ := hI _ _ i₂
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.rsp, S₂.top.rsp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ (.rbp, .rdi) (by decide), r₂ (.rbp, .rdi) (by decide), h1]
  · rw [r₁ (.r12, .rsi) (by decide), r₂ (.r12, .rsi) (by decide), h2]
  · rw [r₁ (.r13, .rdx) (by decide), r₂ (.r13, .rdx) (by decide), h3]
  · rw [r₁ (.rbx, .r8) (by decide), r₂ (.rbx, .r8) (by decide), h5]
  · rw [r₁ (.r14, .rcx) (by decide), r₂ (.r14, .rcx) (by decide), h4]

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR p D I E`, with `Q₀` of
the final states. -/
theorem stepRR {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D I E) c Q₀)
    (hE : ∀ x y x' y', VG.Proof.MlDsa.X86_64.Sign.RR p D I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D I E) c (VG.Proof.MlDsa.X86_64.Sign.RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

end

/-! ## Runs related through their entry states -/

/-- Two runs, each satisfying `I` from its entry state, the entry states related by `E`. -/
def RS (p : Params) (D : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  ∃ σ₁ σ₂, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ₁ ∧ (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ₂ ∧ (VG.Proof.MlDsa.X86_64.Sign.signK p D).pub σ₁ σ₂ ∧ E σ₁ σ₂ ∧ I σ₁ x ∧ I σ₂ y

section
variable {p : Params} {D : Nat}

theorem lrel_of {σ₁ σ₂ x y : State} (hpub : (VG.Proof.MlDsa.X86_64.Sign.signK p D).pub σ₁ σ₂) (S₁ : VG.Proof.MlDsa.X86_64.Sign.St p D σ₁ x) (S₂ : VG.Proof.MlDsa.X86_64.Sign.St p D σ₂ y) :
    VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.rsp, S₂.top.rsp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ (.rbp, .rdi) (by decide), r₂ (.rbp, .rdi) (by decide), h1]
  · rw [r₁ (.r12, .rsi) (by decide), r₂ (.r12, .rsi) (by decide), h2]
  · rw [r₁ (.r13, .rdx) (by decide), r₂ (.r13, .rdx) (by decide), h3]
  · rw [r₁ (.rbx, .r8) (by decide), r₂ (.rbx, .r8) (by decide), h5]
  · rw [r₁ (.r14, .rcx) (by decide), r₂ (.r14, .rcx) (by decide), h4]

theorem RS.lrel {E I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Sign.St p D σ s) {x y : State}
    (h : VG.Proof.MlDsa.X86_64.Sign.RS p D E I x y) : VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  exact VG.Proof.MlDsa.X86_64.Sign.lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem RS.mono {E I E' I' : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.X86_64.Sign.RS p D E I x y)
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → E' σ₁ σ₂) (hI : ∀ σ s, I σ s → I' σ s) : VG.Proof.MlDsa.X86_64.Sign.RS p D E' I' x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, e, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, hE _ _ e, hI _ _ i₁, hI _ _ i₂⟩

/-- A piece that leaks the same from two runs in the layout that satisfy `T`, and takes each run from
`I` to `J`. -/
theorem liftL {E I J : State → State → Prop} {T : State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Sign.St p D σ s ∧ T s) (hw : ∀ σ s, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ T x ∧ T y) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E I) c (VG.Proof.MlDsa.X86_64.Sign.RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ ⟨VG.Proof.MlDsa.X86_64.Sign.lrel_of hpub (hI _ _ i₁).1 (hI _ _ i₂).1, (hI _ _ i₁).2, (hI _ _ i₂).2⟩ e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- `liftL`, with a leakage proof from any relation the runs satisfy. -/
theorem liftR {E I J : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E I) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E I) c (VG.Proof.MlDsa.X86_64.Sign.RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- Two pieces in sequence, from two runs in the layout that satisfy `I` (what the first piece needs),
each piece leaving the layout. -/
theorem seqL {c₁ c₂ : Prog isa} {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, VG.Proof.MlDsa.X86_64.Sign.Lay D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x → I x → WP isa c₁ x fun x' => (∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep h₁ (F := fun x x' => (∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.lx h.2.1, w₁ y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hx hy, jx, jy⟩) h₂

theorem trL_mono {c : Prog isa} {I I' : State → Prop}
    (h : RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I x ∧ I y) c fun _ _ => True) (hI : ∀ s, I' s → I s) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I' x ∧ I' y) c fun _ _ => True :=
  RelCT.mono h (fun _ _ h => ⟨h.1, hI _ h.2.1, hI _ h.2.2⟩) fun _ _ h => h

end

/-! ## `ρ` -/

theorem signLeakT_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeakT p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeakT p sk₁ μ₁ r₁ = signLeakT p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := VG.Proof.MlDsa.X86_64.Sign.signLeakT_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := VG.Proof.MlDsa.X86_64.Sign.signLeakT_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine leakBytes_inj (List.append_inj h ?_).1
  rw [leakBytes_length, leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {D : Nat} {σ₁ σ₂ : State} (h : (VG.Proof.MlDsa.X86_64.Sign.signK p D).pub σ₁ σ₂) :
    VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ₁ = VG.Proof.MlDsa.X86_64.Sign.rhoOf p σ₂ :=
  VG.Proof.MlDsa.X86_64.Sign.leak_rho (VG.Proof.MlKem.bytesAt_length _ _ _) (VG.Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseACT`. -/
section

/-!
# ML-DSA signing on x86-64: `ExpandA` leaks only `ρ`

Two runs of `ExpandA` with the same `ρ` compute the same results of
`vg_mldsa_rej_ntt_poly` and `vg_mldsa_rej_ntt_poly4`, so they agree on `r15`
(`RA`), and leak the same (`expandA_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `r15`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s) fun x y => x.gpr .r15 = y.gpr .r15

theorem callE_ok' {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s) (hs : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS)) 34 = VG.Proof.MlDsa.X86_64.Sign.seedE p σ e) :
    WP isa (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)), .ptr (sc oPS)]) s
      fun s' => VG.Proof.MlDsa.X86_64.Sign.JE p D e σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.eChk_spec he
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3 _ (by decide)⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem sampleE_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {e : Nat} (he : VG.Proof.MlDsa.X86_64.Sign.eChk p e = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RA p D e) (sampleE P p e) (VG.Proof.MlDsa.X86_64.Sign.RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.X86_64.Sign.eChk_spec he
  rw [VG.Proof.MlDsa.X86_64.Sign.sampleE_eq]
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA p D σ e s ∧ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oRS)) 34 = VG.Proof.MlDsa.X86_64.Sign.seedE p σ e)
    fun x y => x.gpr .r15 = y.gpr .r15) ?_ (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RR p D (VG.Proof.MlDsa.X86_64.Sign.JE p D e)
      fun x y => x.gpr .r15 = y.gpr .r15 ∧ (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32) ?_ ?_)
  · refine VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sign.blkE_ok he h)
      (VG.Proof.MlDsa.X86_64.Sign.block_tr (rs := [.rbx]) rfl fun x y h r hr => ?_) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.lrel fun _ _ h => h.st).regs (.rbx, VG.Proof.MlDsa.X86_64.Sign.scrLen p) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW])
  · refine VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sign.callE_ok' hP he h.1 h.2)
      ((VG.Proof.MlDsa.X86_64.Sign.rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, VG.Proof.MlDsa.X86_64.Sign.seedE, VG.Proof.MlDsa.X86_64.Sign.seedE, VG.Proof.MlDsa.X86_64.Sign.pub_rho hpub]
  · refine VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun s s' => s'.gpr .r15 =
        BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32))
      (fun σ s _ h => WP.conj (VG.Proof.MlDsa.X86_64.Sign.andE_ok he h) (WP.mono (VG.Proof.MlDsa.X86_64.Sign.and15_ok s) fun _ h => h.1))
      (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

/-! ## Four entries at a time -/

/-- Two runs in a group, after the seeds of its first `j` entries, with the same `r15`. -/
abbrev RG (p : Params) (D e j : Nat) : State → State → Prop :=
  VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.GS p D σ e j s) fun x y => x.gpr .r15 = y.gpr .r15

theorem slot_tr {p : Params} {D e j : Nat} (hj4 : j < 4) (hc : VG.Proof.MlDsa.X86_64.Sign.slotChk p e j = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RG p D e j) (.block (setSR p e j)) (VG.Proof.MlDsa.X86_64.Sign.RG p D e (j + 1)) :=
  VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sign.slot_ok hj4 hc h)
    (VG.Proof.MlDsa.X86_64.Sign.block_tr (rs := [.rbx]) rfl fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.lrel fun _ _ h => h.ia4.ia.st).regs (.rbx, VG.Proof.MlDsa.X86_64.Sign.scrLen p) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW]))
    fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]

theorem call4_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {e : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.callChk p e = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RG p D e 4) (rej4At P (pS (VG.Proof.MlDsa.X86_64.Sign.aBase p + e)) (r4P p))
      (VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (e + 4) s) fun x y => x.gpr .r15 = y.gpr .r15) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Sign.callChk, Bool.and_eq_true] at hc'
  unfold rej4At
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RR p D (VG.Proof.MlDsa.X86_64.Sign.J4 p D e)
      fun x y => x.gpr .r15 = y.gpr .r15 ∧ (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32) ?_ ?_
  · refine VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sign.callG_ok hP hc h)
      ((VG.Proof.MlDsa.X86_64.Sign.rej4Call_tr hP hc'.2).mono (fun x y h => ⟨h.lrel fun _ _ h => h.ia4.ia.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, g₁, g₂⟩, _⟩ := h
    rw [g₁.seeds, g₂.seeds, VG.Proof.MlDsa.X86_64.Sign.pub_rho hpub]
  · refine VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun s s' => s'.gpr .r15 =
        BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32))
      (fun σ s _ h => WP.conj (VG.Proof.MlDsa.X86_64.Sign.and4_ok hc h) (WP.mono (VG.Proof.MlDsa.X86_64.Sign.and15_ok s) fun _ h => h.1))
      (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

theorem sample4_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {g : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.g4Chk p (4 * g) = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (4 * g) s) fun x y => x.gpr .r15 = y.gpr .r15) (sample4 P p g)
      (VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (4 * g + 4) s) fun x y => x.gpr .r15 = y.gpr .r15) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.g4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, cc⟩ := hc
  unfold sample4
  refine RelCT.seq (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.slot_tr (by decide) s0) (fun x y h => RR.mono h
    (fun σ s h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) id) fun _ _ h => h) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.slot_tr (by decide) s1) (RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.slot_tr (by decide) s2) (RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.slot_tr (by decide) s3) ?_))
  exact VG.Proof.MlDsa.X86_64.Sign.call4_tr hP cc

/-! ## The matrix -/

theorem cpR4_tr {p : Params} {D j : Nat} (hj : j < 4) (hc : VG.Proof.MlDsa.X86_64.Sign.cpChk p j = true) (hsk : 32 ≤ p.skLen) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ j s) fun _ _ => True) (cpR4 j)
      (VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ (j + 1) s) fun _ _ => True) :=
  VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun _ _ => True) (fun σ s _ h => WP.mono (VG.Proof.MlDsa.X86_64.Sign.cpR4_ok hc hsk h) fun _ h => ⟨h, trivial⟩)
    (VG.Proof.MlDsa.X86_64.Sign.copy_tr (by decide) (by decide) (show oRS4 + 34 * j < 2 ^ 31 by simp only [oRS4]; omega) (by decide) (by decide)
      fun x y h => ⟨(h.lrel fun _ _ h => h.st).regs (.rbx, VG.Proof.MlDsa.X86_64.Sign.scrLen p) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW]),
        (h.lrel fun _ _ h => h.st).regs (.rbp, p.skLen) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW])⟩)
    fun _ _ _ _ _ _ _ _ => trivial

theorem expandA_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.aChk p = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.St p D σ s ∧ s.gpr .r15 = 1) fun _ _ => True)
      (Impl.MlDsa.X86_64.Sign.expandA P p) (VG.Proof.MlDsa.X86_64.Sign.RA p D (p.k * p.ℓ)) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩, hc4⟩, hg⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ 0 s) fun _ _ => True) (VG.Proof.MlDsa.X86_64.Sign.stepRR (F := fun _ _ => True)
    (fun σ s _ h => WP.mono (VG.Proof.MlDsa.X86_64.Sign.copyRho_ok hcp hst hsk h.1) fun s1 ⟨S1, _, hb, e15⟩ =>
      ⟨⟨S1, hb, fun _ h => absurd h (Nat.not_lt_zero _), e15.trans h.2⟩, trivial⟩)
    (VG.Proof.MlDsa.X86_64.Sign.copy_tr (by decide) (by decide) (by decide) (by decide) (by decide) fun x y h =>
      ⟨(h.lrel fun _ _ h => h.1).regs (.rbx, VG.Proof.MlDsa.X86_64.Sign.scrLen p) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW]),
        (h.lrel fun _ _ h => h.1).regs (.rbp, p.skLen) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW])⟩)
    fun _ _ _ _ _ _ _ _ => trivial) ?_
  have hC := VG.Proof.MlDsa.X86_64.Sign.seqR_tr (f := cpR4) (R := fun j => VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ j s) fun _ _ => True) 4 0
    fun j _ hj => VG.Proof.MlDsa.X86_64.Sign.cpR4_tr (by omega) (hc4 j (by omega)) hsk
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICopy p D σ 4 s) fun _ _ => True) hC ?_
  have hG := VG.Proof.MlDsa.X86_64.Sign.seqR_tr (f := sample4 P p)
    (R := fun g => VG.Proof.MlDsa.X86_64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA4 p D σ (4 * g) s) fun x y => x.gpr .r15 = y.gpr .r15) (p.k * p.ℓ / 4) 0
    fun g _ hg' => VG.Proof.MlDsa.X86_64.Sign.sample4_tr hP (hg g (by omega))
  rw [Nat.zero_add] at hG
  refine RelCT.seq (RelCT.mono hG (fun x y h => ?_) fun _ _ h => h) ?_
  · obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
    exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁.ia4, i₂.ia4⟩, i₁.r15.trans i₂.r15.symm⟩
  have hE := VG.Proof.MlDsa.X86_64.Sign.seqR_tr (f := sampleE P p) (R := fun k => VG.Proof.MlDsa.X86_64.Sign.RA p D k) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    fun k h1 hk => VG.Proof.MlDsa.X86_64.Sign.sampleE_tr hP (he k (by omega))
  rw [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega] at hE
  exact RelCT.mono hE (fun x y h => RR.mono h (fun σ s h => h.ia) id) fun _ _ h => h

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT`. -/
section

/-!
# ML-DSA signing on x86-64: decoding leaks only the pointers

Each call while decoding leaks only its pointers, given that its input
polynomial is reduced (`dec_tr`); so two runs agree on what decoding leaks
(`decode_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A piece that leaks only its pointers, from runs in the layout. -/
theorem liftT {p : Params} {D : Nat} {E I J : State → State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Sign.St p D σ s) (hw : ∀ σ s, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p)) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E I) c (VG.Proof.MlDsa.X86_64.Sign.RS p D E J) :=
  VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun _ => True) (fun σ s h => ⟨hI σ s h, trivial⟩) hw (RelCT.mono ht (fun _ _ h => h.1) fun _ _ h => h)

theorem dec_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y)) (hc : VG.Proof.MlDsa.X86_64.Sign.decChk p a b c src len j = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p)) (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hc
  refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqL (p := p) (I := fun _ => True) (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (pS j)))
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.bupAt_tr hP hp hl h1) (fun _ _ h => h.1) fun _ _ h => h)
    (fun s L _ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.bupAt_ok hP L hp hl h1) fun s' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩)
    (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := ntt) hP.ntt h2)) (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem decode_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.dChk p = true) {E : State → State → Prop} :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E (VG.Proof.MlDsa.X86_64.Sign.IM p D)) (decode P p) (VG.Proof.MlDsa.X86_64.Sign.RS p D E (VG.Proof.MlDsa.X86_64.Sign.IK p D)) := by
  have hs := VG.Proof.MlDsa.X86_64.Sign.dChk_spec hc
  unfold decode
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ 0 0 s) ?_ (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k 0 s)
    ?_ (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k p.k s) ?_ ?_))
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ID p D σ r 0 0 s) p.ℓ 0 fun r _ hr =>
      VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.decS1_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.X86_64.Sign.dec_tr hP hs.2.2.2.2.2.2.1 (VG.Proof.MlDsa.X86_64.Sign.sLen_eq p) (hs.1 r (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ i 0 s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.decS2_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.X86_64.Sign.dec_tr hP hs.2.2.2.2.2.2.1 (VG.Proof.MlDsa.X86_64.Sign.sLen_eq p) (hs.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ID p D σ p.ℓ p.k i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.decT0_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.X86_64.Sign.dec_tr hP (by decide) (by decide) (hs.2.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, h.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · exact VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.rpp_ok hP hc h)
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.shake_tr (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hP.hD hs.2.2.2.1) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT`. -/
section

/-!
# ML-DSA signing on x86-64: the commitment leaks only the pointers

Each piece of the commitment leaks only its pointers, given that its inputs
are reduced (and the coefficients of `HighBits(w[i])` bounded): `maskR_trL`,
`rowW_trL`, `w1R_trL`; so two runs agree on what the commitment leaks
(`commit_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- A piece that keeps `I`, from runs in the layout that satisfy it. -/
theorem stepSelf {c : Prog isa} {I : State → Prop}
    (h : RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I x ∧ I y) c fun _ _ => True)
    (w : ∀ x, VG.Proof.MlDsa.X86_64.Sign.Lay D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x → I x → WP isa c x fun x' => (∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W) ∧ I x') :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I x ∧ I y) c
      fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ I x ∧ I y :=
  VG.Proof.MlKem.X86_64.RelCT.postDep h (F := fun x x' => (∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x x' W) ∧ I x')
    (fun x y h => ⟨w x h.1.lx h.2.1, w y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hx hy, jx, jy⟩

theorem lrel_rbx {x y : State} (h : VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y) : ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact h.regs (.rbx, VG.Proof.MlDsa.X86_64.Sign.scrLen p) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW])

end

/-! ## `y` and `ŷ` -/

theorem setKappa_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D rbs wbs s) {r : Nat}
    (hr : r < 2 ^ 31) (h1 : VG.Proof.MlDsa.X86_64.Sign.inB (rbs ++ wbs) (sc oKAP) 8 = true) (h2 : VG.Proof.MlDsa.X86_64.Sign.inB wbs (sc (oMS + 64)) 2 = true) :
    WP isa (.block (setKappa r)) s fun s' => ∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D s s' W := by
  have e65 : VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 65)) = VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64)) + 1 := (VG.Proof.MlDsa.X86_64.Sign.pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.iW h2
  have c0 : (⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64))) 1 := by
    have := VG.Proof.MlDsa.X86_64.Sign.contains_offset' (base := VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64))) (off := 0) (len := 1) (n := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.X86_64.Sign.contains_offset' (off := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64))) 1 := by
    have := VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.X86_64.Sign.inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.setKap_ok (oMS + 64) r hr s (L.iR h1) i0 i1) fun s' ⟨hm, k⟩ => ⟨_, (VG.Proof.MlDsa.X86_64.Sign.postB_of_keep (D := D) k (by decide)
    (W := [⟨VG.Proof.MlDsa.X86_64.Sign.pa s (sc (oMS + 64)), 2⟩]) ?_).1⟩
  rw [hm]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1

theorem maskR_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {r : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.mChk p r = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p)) (maskR P p r) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, k1⟩, w1⟩, cm⟩, _⟩, cc⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩, hr⟩, hγ⟩ := hc
  have hcc := VG.Proof.MlDsa.X86_64.Sign.copyChk_spec cc
  unfold maskR
  refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1) (fun x L _ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.setKappa_post L hr k1 w1) fun _ h => ⟨h, trivial⟩)
    (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yP p r)))
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.maskAt_tr hP hγ cm) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x L _ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.maskAt_ok hP L hγ cm) fun x' ⟨hP', _, hq⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩)
      (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yhP p r)))
        (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
          fun x y h => ⟨VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _), VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
          (fun _ _ h => h) fun _ _ h => h)
        (fun x L hy => WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
          ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
        (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := ntt) hP.ntt ci))))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

/-! ## `y` and `ŷ`, four at a time -/

theorem ms4_trL {D : Nat} {p : Params} {g k : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.ms4Chk p g k = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p)) (cpM4 g k) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.ms4Chk, Bool.and_eq_true] at hc
  have cc := hc.1.1.1.1.1.1.1.1
  have hcc := VG.Proof.MlDsa.X86_64.Sign.copyChk_spec cc
  unfold cpM4
  exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _), VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L _ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB L cc) fun _ ⟨hP', _⟩ => ⟨⟨_, hP'⟩, trivial⟩)
    (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem yhR_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {t ry r : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.yhChk p ry r = true)
    (hr : r < ry) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t ry r x) ∧ ∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t ry r y)
      (yhR P p r) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.yhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨cc, _⟩, ci⟩, _⟩ := hc
  have hcc := VG.Proof.MlDsa.X86_64.Sign.copyChk_spec cc
  unfold yhR
  exact VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yhP p r)))
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _), VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L ⟨_, I⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.y r hr).1⟩)
    (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := ntt) hP.ntt ci)

theorem mask4_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {g : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.m4Chk p g = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * g) s) (mask4 P p g)
      (VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * (g + 1)) s) := by
  obtain ⟨hcp, cm, c2, hyh, hγ⟩ := VG.Proof.MlDsa.X86_64.Sign.m4Chk_spec hc
  unfold mask4
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.SD p D σ t g 4 s) ?_
    (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t (4 * g + 4) (4 * g) s) ?_ ?_)
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun k => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.SD p D σ t g k s) 4 0 fun k _ hk =>
      VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.ms4_ok (hcp k (by omega)) h) (VG.Proof.MlDsa.X86_64.Sign.ms4_trL (hcp k (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.m4call_ok hP hγ cm c2 h) (VG.Proof.MlDsa.X86_64.Sign.mask4Call_tr hP hγ cm)
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t (4 * g + 4) r s) 4 (4 * g)
      fun r h1 hr => VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICy p D σ t (4 * g + 4) r s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.yhR_ok hP (hyh r h1 hr) (by omega) h) (VG.Proof.MlDsa.X86_64.Sign.yhR_trL hP (hyh r h1 hr) (by omega)))
      (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h.l, h.y, h.yh⟩

/-! ## `w` -/

/-- `w[i]` from runs in iteration `t` with `y`, `ŷ` and the first `i` polynomials of `w`. -/
theorem rowW_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {t i : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.wChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i y) (rowW P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, _⟩, hl⟩ := hc
  have hA : ∀ {σ s : State} (I : VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) j, j < p.ℓ → Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (VG.Impl.MlDsa.X86_64.Sign.aP p i j)) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [VG.Proof.MlDsa.X86_64.Sign.aP_ij]; exact this.1
  let J : State → Prop := fun s => (∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (wP p i))
  unfold rowW
  refine VG.Proof.MlDsa.X86_64.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.X86_64.Sign.seqL (J := J) ?_ ?_ ?_)
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_tr hP.mul (cm 0 hl)) (fun x y ⟨R, ⟨σ₁, I₁⟩, ⟨σ₂, I₂⟩⟩ =>
      ⟨R, ⟨hA I₁ 0 hl, (I₁.yh 0 hl).1⟩, ⟨hA I₂ 0 hl, (I₂.yh 0 hl).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L (cm 0 hl) (hA I 0 hl) (I.yh 0 hl).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun _ x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ J x ∧ J y) (p.ℓ - 1) 1
      fun j hj1 hj => VG.Proof.MlDsa.X86_64.Sign.stepSelf ?_ ?_) (fun _ _ h => h) fun _ _ _ => trivial
    · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.mulAddAt_tr hP.mulAdd (cm j (by omega))) (fun x y ⟨R, ⟨⟨σ₁, I₁⟩, r₁⟩, ⟨⟨σ₂, I₂⟩, r₂⟩⟩ =>
        ⟨R, ⟨r₁, hA I₁ j (by omega), (I₁.yh j (by omega)).1⟩, ⟨r₂, hA I₂ j (by omega), (I₂.yh j (by omega)).1⟩⟩)
        fun _ _ h => h
    · rintro x L ⟨⟨σ, I⟩, r⟩
      refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAddAt_ok hP.mulAdd L (cm j (by omega)) r (hA I j (by omega)) (I.yh j (by omega)).1)
        fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩
  · rintro x L ⟨I, r⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_ok (I := fun _ s => ∃ W, VG.Proof.MlDsa.X86_64.Sign.PostB D x s W ∧ J s) (p.ℓ - 1) 1
      (fun j hj1 hj s ⟨W, hW, ⟨σ, I'⟩, r'⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAddAt_ok hP.mulAdd I'.l.st.lay (cm j (by omega)) r'
        (hA I' j (by omega)) (I'.yh j (by omega)).1) fun x' ⟨hP', _, hq⟩ =>
          ⟨_, hW.trans hP' (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h),
            ⟨σ, I'.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩) x ⟨[], PostB.refl D x [], I, r⟩)
      fun x' ⟨W, hW, j⟩ => ⟨⟨W, hW⟩, j⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := nttInv) hP.invNtt ci) (fun _ _ h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h

/-! ## `w₁` -/

theorem w1R_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} {t i : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.hChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t i y) (w1R P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => ∀ j < 256, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t1P) j).toNat ≤ w1Max p) ?_ ?_
    (VG.Proof.MlDsa.X86_64.Sign.sbpAt_tr hP hb rfl c2)
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.highBitsAt_tr hP hγ c1) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ => ⟨R, (I₁.c.w i hi).1, (I₂.c.w i hi).1⟩)
      fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.highBitsAt_ok hP L hγ c1 (I.c.w i hi).1) fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, fun j hj => ?_⟩
    rw [hP'.pa (by decide), VG.Proof.MlDsa.X86_64.Sign.natPolyIs_coeff hq hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _

/-! ## The commitment -/

theorem ctShake_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t p.k s) :
    WP isa (shakeAt [((.r12, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p)) s (VG.Proof.MlDsa.X86_64.Sign.IC p D σ t) := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.cChk, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hs⟩, hk⟩ := hc
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.shake_ok (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hP.hD hs h.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ => ⟨h.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [VG.Proof.MlDsa.X86_64.Sign.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, h.w1, h.c.l.st.mu]
  simp only [VG.Proof.MlDsa.X86_64.Sign.CTv, ctF, w1Encode, List.flatMap_map]

theorem commit_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.X86_64.Sign.cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) (commit P p) (VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.IC p D σ t s) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Sign.cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨⟨hm4, hm⟩, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commit
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * (p.ℓ / 4)) s) ?_
    (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t 0 s) ?_ (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t p.k s) ?_ ?_)))
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun g => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t (4 * g) s) (p.ℓ / 4) 0 fun g _ hg =>
      VG.Proof.MlDsa.X86_64.Sign.mask4_tr hP (hm4 g (by omega)))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICm p D σ t r s) (p.ℓ % 4) (4 * (p.ℓ / 4))
      fun r _ hr =>
      VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.maskR_ok hP (hm r (by omega)) h) (VG.Proof.MlDsa.X86_64.Sign.maskR_trL hP (hm r (by omega))))
      (fun x y h => h)
      fun x y h => by rw [Nat.div_add_mod] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h.l, h.y, h.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.rowW_ok hP (hw i (by omega)) (by omega) h) (VG.Proof.MlDsa.X86_64.Sign.rowW_trL hP (hw i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [VG.Proof.MlDsa.X86_64.Sign.w1Enc]; rfl⟩
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.X86_64.Sign.ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.w1R_ok hP (hh i (by omega)) (by omega) h) (VG.Proof.MlDsa.X86_64.Sign.w1R_trL hP (hh i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · exact VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.ctShake_ok hP hc h)
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.shake_tr (VG.Proof.MlDsa.X86_64.Sign.sgB_bases p) hP.hD hs) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT`. -/
section

/-!
# ML-DSA signing on x86-64: the checks leak only the pointers and whether they passed

Each check leaks only its pointers, given that its inputs are reduced
(`zR_trL`, `r0R_trL`, `hR_trL`); the branch on their result leaks whether the
iteration passed, which two runs agree on when they agree on what the
iteration leaks (`checks_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) {p : Params}
include hP

theorem normAt_post {s : State} (L : VG.Proof.MlDsa.X86_64.Sign.Lay D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : VG.Proof.MlDsa.X86_64.Sign.normChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s f)) :
    WP isa (normAt P f B) s fun s' => VG.Proof.MlDsa.X86_64.Sign.PPostB D s s' [] := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sign.normCall_ok hP L hB hc hr) fun s1 ⟨hP1, _, _⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.and15_ok s1) fun s2 ⟨_, hm2, k2⟩ => ?_
  exact PostB.trans hP1 (VG.Proof.MlDsa.X86_64.Sign.postB15 (D := D) k2 hm2 ([] : List Region)).1 (fun r h => h) fun _ h => absurd h List.not_mem_nil

theorem normAt_trL {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.X86_64.Sign.normChk (VG.Proof.MlDsa.X86_64.Sign.sgB p) f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y f)) (normAt P f B)
      fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun _ => True) (VG.Proof.MlDsa.X86_64.Sign.normCall_tr hP hB hc)
    (fun x L hr => WP.mono (VG.Proof.MlDsa.X86_64.Sign.normCall_ok hP L hB hc hr) fun _ h => ⟨⟨_, h.1⟩, trivial⟩)
    (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)

/-! ## `z` -/

theorem zR_trL {t r : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.zChk p r = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t r x) ∧ ∃ σ, VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t r y) (zR P p r)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩, hr⟩ := hc
  unfold zR
  refine VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IZb p D σ t r s) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t1P)) ?_ ?_
    (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IZb p D σ t r s) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t1P)) ?_ ?_
      (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yP p r))) ?_ ?_ (VG.Proof.MlDsa.X86_64.Sign.normAt_trL hP hB cn)))
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s1 r hr).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s1 r hr).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.s1 r hr).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.addAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.y 0 (by omega)).1, r₁⟩, ⟨(I₂.y 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.addAt_ok hP L ca (I.y 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩

/-! ## `r₀` -/

theorem r0R_trL {t i : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.rChk p i = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IR p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.X86_64.Sign.IR p D σ t i y) (r0R P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  unfold r0R
  refine VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t1P)) ?_ ?_
    (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IRb p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t1P)) ?_ ?_
      (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (wP p i))) ?_ ?_
        (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t2P)) ?_ ?_ (VG.Proof.MlDsa.X86_64.Sign.normAt_trL hP hB cn))))
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s2 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s2 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.s2 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.subAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.w 0 (by omega)).1, r₁⟩, ⟨(I₂.w 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.subAt_ok hP L ca (I.w 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩
  · exact VG.Proof.MlDsa.X86_64.Sign.lowBitsAt_tr hP hγ cl
  · intro x L r1
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.lowBitsAt_ok hP L hγ cl r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 2)]; exact hq.1⟩

/-! ## `ct₀` and `h` -/

theorem hR_trL {t i : Nat} (hc : VG.Proof.MlDsa.X86_64.Sign.hChk2 p i = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IH p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.X86_64.Sign.IH p D σ t i y) (hR P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, _⟩, g6⟩, _⟩, _⟩,
    _⟩, _⟩, o1⟩, o2⟩, o3⟩, o4⟩, _⟩, _⟩, t3⟩, t4⟩, u5⟩, _⟩, _⟩, _⟩, hγ'⟩, hγ⟩, hi⟩, _⟩ := hc
  have hcc := VG.Proof.MlDsa.X86_64.Sign.copyChk_spec cc
  have f6 : VG.Proof.MlDsa.X86_64.Sign.keepB (VG.Proof.MlDsa.X86_64.Sign.sgB p) [(t4P, 1024)] (wP p i) 1024 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Sign.hfam, Bool.and_eq_true] at g6
    exact VG.Proof.MlDsa.X86_64.Sign.famChk_one (b := VG.Proof.MlDsa.X86_64.Sign.wBase p) g6.1.1.2 (show i < i + 1 by omega)
  let J : State → Prop := fun s => (∃ σ, VG.Proof.MlDsa.X86_64.Sign.IHb p D σ t i i s) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t3P)
  unfold hR
  refine VG.Proof.MlDsa.X86_64.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.X86_64.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.X86_64.Sign.seqL (J := J) ?_ ?_
    (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => J s ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t4P)) ?_ ?_
      (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t4P) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (wP p i))) ?_ ?_
        (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s t4P) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (wP p i))) ?_ ?_
          (VG.Proof.MlDsa.X86_64.Sign.seqL (J := fun _ => True) ?_ ?_ ?_))))))
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.t0 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.t0 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.t0 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' g1 o1⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g2 o2⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.normAt_trL hP hγ' cn) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.normAt_post hP L hγ' cn r1) fun x' hP' => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g3 o3⟩, L.keepRed hP' t3 r1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _), VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r3⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_okB L cc) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, ⟨⟨σ, I.step hP' g4 o4⟩, L.keepRed hP' t4 r3⟩,
      by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 4)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.w' 0 (by omega)).1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.addAt_tr hP ca) (fun x y ⟨R, ⟨⟨⟨_, I₁⟩, r₁⟩, _⟩, ⟨⟨⟨_, I₂⟩, r₂⟩, _⟩⟩ =>
      ⟨R, ⟨(I₁.w' 0 (by omega)).1, r₁⟩, ⟨(I₂.w' 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨⟨σ, I⟩, r3⟩, r4⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.addAt_ok hP L ca (I.w' 0 (by omega)).1 r3) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, L.keepRed hP' u5 r4, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases _)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.subAt_tr hP cs) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.subAt_ok hP L cs r4 rw) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.X86_64.Sign.pS_bases 4)]; exact hq.1, L.keepRed hP' f6 rw⟩
  · exact RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.hintCall_tr hP hγ ch) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩)
      fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.hintCall_ok hP L hγ ch r4 rw) fun x' ⟨hP', _, _⟩ => ⟨⟨_, hP'⟩, trivial⟩
  · exact VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h.1

/-! ## The checks -/

omit hP in
theorem ifOk_rbx {E I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Sign.St p D σ s) {C : State → Prop} {x y : State}
    (h : ∃ x₀ y₀, VG.Proof.MlDsa.X86_64.Sign.RS p D E I x₀ y₀ ∧ (VG.Proof.MlDsa.X86_64.Sign.PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧ x.mem = x₀.mem) ∧
      (VG.Proof.MlDsa.X86_64.Sign.PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧ C x₀) :
    ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := by
  obtain ⟨x₀, y₀, R, ⟨hx, _⟩, ⟨hy, _⟩, _⟩ := h
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [hx.bs _ (by decide), hy.bs _ (by decide)]
  exact VG.Proof.MlDsa.X86_64.Sign.lrel_rbx (R.lrel hI) _ (List.mem_singleton_self _)

theorem checks_tr (hc : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) {E : State → State → Prop} {t : Nat}
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ₁ (p.ℓ * t))).isSome →
      (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ₂ (p.ℓ * t))).isSome → (VG.Proof.MlDsa.X86_64.Sign.PassV p σ₁ (p.ℓ * t) ↔ VG.Proof.MlDsa.X86_64.Sign.PassV p σ₂ (p.ℓ * t))) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.KA p D σ t s) (checks P p)
      (VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.X86_64.Sign.EF p D σ t s) := by
  refine VG.Proof.MlDsa.X86_64.Sign.ksChk_spec hc fun c1 _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.KN p D σ t s)
    (VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s cP)) (fun σ s h => ⟨h.c.l.st, h.cc.1⟩)
      (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.cntt_ok hP hc h) (VG.Proof.MlDsa.X86_64.Sign.ipAt_tr (t := ntt) hP.ntt c1)) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t 0 s)
    (VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.b.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.kInit_ok hc h) (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h)) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.IR p D σ t 0 s) (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.X86_64.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t r s) p.ℓ 0 fun r _ hr => VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.X86_64.Sign.IZ p D σ t r s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.zR_ok hP (hz r (by omega)) h) (VG.Proof.MlDsa.X86_64.Sign.zR_trL hP (hz r (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ir) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.IH p D σ t 0 s) (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.X86_64.Sign.IR p D σ t i s) p.k 0 fun i _ hi => VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.X86_64.Sign.IR p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.r0R_ok hP (hr i (by omega)) h) (VG.Proof.MlDsa.X86_64.Sign.r0R_trL hP (hr i (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ih) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.IH p D σ t p.k s) (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.X86_64.Sign.IH p D σ t i s) p.k 0 fun i _ hi => VG.Proof.MlDsa.X86_64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.X86_64.Sign.IH p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.hR_ok hP (hh i (by omega)) h) (VG.Proof.MlDsa.X86_64.Sign.hR_trL hP (hh i (by omega))))
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.X86_64.Sign.KO p D σ t s)
    (VG.Proof.MlDsa.X86_64.Sign.liftT (fun _ _ h => h.1.b.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.onesOk_ok hc h) (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h)) ?_
  refine VG.Proof.MlDsa.X86_64.Sign.liftR (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.kBranch_ok hc h) (VG.Proof.MlDsa.X86_64.Sign.ifOkElse_tr (D := D) (fun x y h => ?_)
    (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.ifOk_rbx (I := fun σ s => VG.Proof.MlDsa.X86_64.Sign.KO p D σ t s) (fun _ _ h => h.b.l.st) h)
    (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.ifOk_rbx (I := fun σ s => VG.Proof.MlDsa.X86_64.Sign.KO p D σ t s) (fun _ _ h => h.b.l.st) h))
  obtain ⟨σ₁, σ₂, _, _, _, he, k₁, k₂⟩ := h
  rw [k₁.r15, k₂.r15, VG.Proof.MlDsa.X86_64.Sign.bit_congr (hE σ₁ σ₂ he k₁.b.some k₂.b.some)]

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseLCT`. -/
section

/-!
# ML-DSA signing on x86-64: the loop leaks what `signLeakT` says

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration, and leak the
same (`iter_tr`, `signLoop_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## What the iterations leak -/

section
variable (p : Params)

/-- What the `n` iterations from counter `κ` leak, for the function entered in `σ`. -/
abbrev leakL (σ : State) (n κ : Nat) : List Nat :=
  signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ) n κ

/-- Two runs agree on what the iterations from `t` leak. -/
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := VG.Proof.MlDsa.X86_64.Sign.leakL p σ₁ (1000 - t) (p.ℓ * t) = VG.Proof.MlDsa.X86_64.Sign.leakL p σ₂ (1000 - t) (p.ℓ * t)

end

theorem map_toNat_inj : ∀ {l₁ l₂ : List Bool}, l₁.map Bool.toNat = l₂.map Bool.toNat → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [VG.Proof.MlDsa.X86_64.Sign.map_toNat_inj h.2]
    cases a <;> cases b <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem hints_inj : ∀ {a b : List (Vector Bool n)}, a.length = b.length →
    (a.flatMap fun hi => hi.toList.map Bool.toNat) = (b.flatMap fun hi => hi.toList.map Bool.toNat) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp (VG.Proof.MlDsa.X86_64.Sign.map_toNat_inj h1), VG.Proof.MlDsa.X86_64.Sign.hints_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}

theorem leq_step (h : VG.Proof.MlDsa.X86_64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ₁)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ₁)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ₁))
      ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ₁)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ₁) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.X86_64.Sign.Am p σ₂)) ((List.range p.ℓ).map (VG.Proof.MlDsa.X86_64.Sign.S1v p σ₂)) ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.S2v p σ₂))
      ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.T0v p σ₂)) (VG.Proof.MlDsa.X86_64.Sign.muOf σ₂) (VG.Proof.MlDsa.X86_64.Sign.rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : VG.Proof.MlDsa.X86_64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814) : VG.Proof.MlDsa.X86_64.Sign.CTv p σ₁ (p.ℓ * t) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ₂ (p.ℓ * t) := by
  have := (leakT_step (VG.Proof.MlDsa.X86_64.Sign.leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : VG.Proof.MlDsa.X86_64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, VG.Proof.MlDsa.X86_64.Sign.iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : VG.Proof.MlDsa.X86_64.Sign.LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakT_step (VG.Proof.MlDsa.X86_64.Sign.leq_step h ht)).2.1 hr).2
  unfold VG.Proof.MlDsa.X86_64.Sign.LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ)).isSome) :
    outTag (VG.Proof.MlDsa.X86_64.Sign.iterF p σ maxBounds κ) = if VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ then
      1 :: ((List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [VG.Proof.MlDsa.X86_64.Sign.iterF_eq hp, VG.Proof.MlDsa.X86_64.Sign.cV_eq hs, Option.map_some]
  by_cases hv : VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : VG.Proof.MlDsa.X86_64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ₂ (p.ℓ * t))).isSome) :
    VG.Proof.MlDsa.X86_64.Sign.PassV p σ₁ (p.ℓ * t) ↔ VG.Proof.MlDsa.X86_64.Sign.PassV p σ₂ (p.ℓ * t) := by
  have e := (leakT_step (VG.Proof.MlDsa.X86_64.Sign.leq_step h ht)).2.2
  rw [VG.Proof.MlDsa.X86_64.Sign.outTag_eq hp hs₁, VG.Proof.MlDsa.X86_64.Sign.outTag_eq hp hs₂] at e
  by_cases h1 : VG.Proof.MlDsa.X86_64.Sign.PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : VG.Proof.MlDsa.X86_64.Sign.PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

theorem leq_hints (hp : ParamsOk p) (h : VG.Proof.MlDsa.X86_64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.X86_64.Sign.CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : VG.Proof.MlDsa.X86_64.Sign.PassV p σ₁ (p.ℓ * t)) (h2 : VG.Proof.MlDsa.X86_64.Sign.PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (VG.Proof.MlDsa.X86_64.Sign.Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakT_step (VG.Proof.MlDsa.X86_64.Sign.leq_step h ht)).2.2
  rw [VG.Proof.MlDsa.X86_64.Sign.outTag_eq hp hs₁, VG.Proof.MlDsa.X86_64.Sign.outTag_eq hp hs₂, ifp h1, ifp h2] at e
  exact VG.Proof.MlDsa.X86_64.Sign.hints_inj (by simp) (List.cons.inj e).2

end

/-! ## Pieces from runs related through their entry states -/

section
variable {p : Params} {D : Nat}

/-- A piece that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS p D E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ₁ → (VG.Proof.MlDsa.X86_64.Sign.signK p D).pre σ₂ → (VG.Proof.MlDsa.X86_64.Sign.signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq⟩

theorem relOr {P₁ P₂ Q : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P₁ c Q) (h₂ : RelCT isa P₂ c Q) :
    RelCT isa (fun x y => P₁ x y ∨ P₂ x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  rcases hr with h | h
  exacts [h₁ _ _ _ _ _ _ h e₁ e₂, h₂ _ _ _ _ _ _ h e₁ e₂]

end

theorem zf_of_eval {s : State} {b : Bool} (h : s.zf.map (!·) = some b) : s.zf = some (!b) := by
  cases hz : s.zf with
  | none => rw [hz] at h; cases h
  | some c => rw [hz] at h; cases c <;> cases b <;> simp_all

theorem LP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.LP p D σ t s) (hz : s.zf = some false) :
    VG.Proof.MlDsa.X86_64.Sign.IL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · rw [hz] at h; cases h

theorem LP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sign.LP p D σ t s) (hz : s.zf = some true) :
    VG.Proof.MlDsa.X86_64.Sign.XS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · rw [hz] at h; cases h
  · exact h

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on `c̃` and `h`. -/
abbrev OX (p : Params) (D : Nat) (x y : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Sign.RS p D (fun _ _ => True) (VG.Proof.MlDsa.X86_64.Sign.XS p D) x y ∧ x.gpr .r15 = y.gpr .r15 ∧
    (x.gpr .r15 = 1 → bytesAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x (sc oCT)) (cLen p) = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y (sc oCT)) (cLen p) ∧
      ∃ f, VG.Proof.MlDsa.X86_64.Sign.HFam x 5 p.k f ∧ VG.Proof.MlDsa.X86_64.Sign.HFam y 5 p.k f)

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
abbrev IX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.zf = y.zf ∧ (x.zf = some false → VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p (t + 1)) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IL p D σ (t + 1) s) x y) ∧
    (x.zf = some true → VG.Proof.MlDsa.X86_64.Sign.OX p D x y)

section
variable {p : Params} {D : Nat}

theorem endPF_tr (hp : ParamsOk p) (hc : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {t : Nat} :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.X86_64.Sign.EF p D σ t s) x y ∧ True)
      (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
        .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) (VG.Proof.MlDsa.X86_64.Sign.IX p D t) := by
  refine VG.Proof.MlDsa.X86_64.Sign.liftQ (J := fun σ s => VG.Proof.MlDsa.X86_64.Sign.LP p D σ t s) (fun σ s _ h => WP.conj (VG.Proof.MlDsa.X86_64.Sign.dec_end hp hc (h.elim .inl (.inr ∘ .inl)))
      (VG.Proof.MlDsa.X86_64.Sign.decF hc (h.elim (·.k) (·.k))))
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.block_tr (rs := [.rbx]) rfl (P := fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y) fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h)
      (fun x y h => h.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.zf = some true := by rw [z₁, e₁.cnt]; rfl
    have zy : y'.zf = some true := by rw [z₂, e₂.cnt]; rfl
    refine ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r15, e₂.r15], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact VG.Proof.MlDsa.X86_64.Sign.leq_ct he e₁.t_lt,
      VG.Proof.MlDsa.X86_64.Sign.Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (VG.Proof.MlDsa.X86_64.Sign.leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((VG.Proof.MlDsa.X86_64.Sign.leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((VG.Proof.MlDsa.X86_64.Sign.leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.zf = y'.zf := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, VG.Proof.MlDsa.X86_64.Sign.leq_succ he f₁.t_lt ⟨_, VG.Proof.MlDsa.X86_64.Sign.iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩,
      by rw [r₁, r₂, f₁.r15, f₂.r15], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.r15)) (by decide)⟩⟩

theorem endB_tr (hp : ParamsOk p) (hc : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {t : Nat} :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.EB p D σ t s) x y ∧ True)
      (.block [.mov .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oCNT)), .alu .sub .rax (.imm 1),
        .store (VG.Impl.MlKem.X86_64.at_ .rbx oCNT) .rax]) (VG.Proof.MlDsa.X86_64.Sign.IX p D t) := by
  refine VG.Proof.MlDsa.X86_64.Sign.liftQ (J := fun σ s => VG.Proof.MlDsa.X86_64.Sign.LP p D σ t s) (fun σ s _ h => WP.conj (VG.Proof.MlDsa.X86_64.Sign.dec_end hp hc (.inr (.inr h))) (VG.Proof.MlDsa.X86_64.Sign.decF hc h.k))
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.block_tr (rs := [.rbx]) rfl (P := fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y) fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h)
      (fun x y h => h.1.lrel fun σ s h => h.k.d.im.st) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _
  have zx : x'.zf = some true := by rw [z₁, e₁.cnt]; rfl
  have zy : y'.zf = some true := by rw [z₂, e₂.cnt]; rfl
  exact ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r15, e₂.r15],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.r15)) (by decide)⟩⟩

theorem ax_one {s : State} (hz : s.zf = some ((s.gpr .rax).setWidth 32 == 0))
    (hr : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1) (hb : isa.eval .ne s = some true) :
    (s.gpr .rax).setWidth 32 = 1 := by
  have e := VG.Proof.MlDsa.X86_64.Sign.zf_of_eval hb
  rcases hr with h | h
  · rw [hz, h] at e; cases e
  · exact h

theorem ax_zero {s : State} (hz : s.zf = some ((s.gpr .rax).setWidth 32 == 0)) (hb : isa.eval .ne s = some false) :
    (s.gpr .rax).setWidth 32 = 0 := by
  have e := VG.Proof.MlDsa.X86_64.Sign.zf_of_eval hb
  rw [hz] at e
  simpa using e

theorem iter_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.X86_64.Sign.cChk p = true) (hc2 : VG.Proof.MlDsa.X86_64.Sign.bChk p = true)
    (hc3 : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) {t : Nat} (ht : t < 814) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) fun σ s => VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) (iter P p) (VG.Proof.MlDsa.X86_64.Sign.IX p D t) := by
  have hc2' := hc2
  simp only [VG.Proof.MlDsa.X86_64.Sign.bChk, Bool.and_eq_true, decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1, -⟩, -⟩, hbp⟩ := hc2'
  unfold iter
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.commit_tr hP hc1) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s) x y ∧
      (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32)
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.liftQ (G := fun _ _ => True) (J := fun σ s => VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s) (F := fun _ _ => True)
      (fun _ _ _ h => WP.mono (VG.Proof.MlDsa.X86_64.Sign.ball_ok hP hc2 h) fun _ h => ⟨h, trivial⟩)
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.ballCall_tr hP hbp c1) (fun x y ⟨h, _⟩ => ⟨h.lrel (fun _ _ h => h.c.l.st), by
        obtain ⟨σ₁, σ₂, _, _, _, he, i₁, i₂⟩ := h
        rw [i₁.ct, i₂.ct]; exact VG.Proof.MlDsa.X86_64.Sign.leq_ct he ht⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
      (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t)
      (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s ∧ s.zf = some ((s.gpr .rax).setWidth 32 == 0)) x y ∧
      (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32)
    (VG.Proof.MlDsa.X86_64.Sign.liftQ (F := fun s s' => (s'.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32)
      (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.test_ok hc4 h)
      (VG.Proof.MlDsa.X86_64.Sign.block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hg j₁ j₂ f₁ f₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, by rw [f₁, f₂, hg]⟩) ?_
  have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
  refine RelCT.seq (R := fun x y => (VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.X86_64.Sign.EF p D σ t s) x y ∧ True) ∨
      (VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.EB p D σ t s) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (VG.Proof.MlDsa.X86_64.Sign.relOr (VG.Proof.MlDsa.X86_64.Sign.endPF_tr hp hc4) (VG.Proof.MlDsa.X86_64.Sign.endB_tr hp hc4))
  · rintro x y ⟨⟨σ₁, σ₂, _, _, _, _, ⟨_, z₁⟩, ⟨_, z₂⟩⟩, hg⟩
    rw [hev, hev, z₁, z₂, hg]
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.checks_tr hP hc3 fun σ₁ σ₂ he s₁ s₂ => VG.Proof.MlDsa.X86_64.Sign.leq_pass hp he ht s₁ s₂)
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inl ⟨h, trivial⟩
    have h1 := VG.Proof.MlDsa.X86_64.Sign.ax_one z₁ i₁.r01 hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁.ka h1, i₂.ka (hg.symm.trans h1)⟩
  · refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.liftT (I := fun σ s => VG.Proof.MlDsa.X86_64.Sign.IB p D σ t s ∧ (s.gpr .rax).setWidth 32 = 0)
      (J := fun σ s => VG.Proof.MlDsa.X86_64.Sign.EB p D σ t s) (fun _ _ h => h.1.c.l.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.else_ok hc4 h.1 h.2)
      (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h))
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inr ⟨h, trivial⟩
    have h0 := VG.Proof.MlDsa.X86_64.Sign.ax_zero z₁ hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, h0⟩, ⟨i₂, hg.symm.trans h0⟩⟩

/-! ## The loop -/

theorem signLoop_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.X86_64.Sign.cChk p = true) (hc2 : VG.Proof.MlDsa.X86_64.Sign.bChk p = true)
    (hc3 : VG.Proof.MlDsa.X86_64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.X86_64.Sign.lChk p = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p 0) fun σ s => VG.Proof.MlDsa.X86_64.Sign.IK p D σ s) (Impl.MlDsa.X86_64.Sign.signLoop P p) (VG.Proof.MlDsa.X86_64.Sign.OX p D) := by
  unfold Impl.MlDsa.X86_64.Sign.signLoop
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.liftT (J := fun σ s => VG.Proof.MlDsa.X86_64.Sign.IL p D σ 0 s) (fun _ _ h => h.d.im.st) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Sign.loopInit_ok hc4 h)
    (VG.Proof.MlDsa.X86_64.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h)) ?_
  have hev : ∀ s : State, isa.eval .ne s = s.zf.map (!·) := fun _ => rfl
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.X86_64.Sign.IL p D σ t s) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := VG.Proof.MlDsa.X86_64.Sign.iter_tr hP hp hc1 hc2 hc3 hc4 ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [hev, hev, hz], fun h => ho (VG.Proof.MlDsa.X86_64.Sign.zf_of_eval h), fun h =>
    ⟨814 - (t + 1), by omega, t + 1, rfl, hc (VG.Proof.MlDsa.X86_64.Sign.zf_of_eval h)⟩⟩

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT`. -/
section

/-!
# ML-DSA signing on x86-64: the signature leaks only the hint

Writing the signature leaks its pointers and the hint (`output_tr`), on which
two runs whose loops leaked the same agree (`OX`); so all but `Â` leaks what
`signLeakT` says (`rest_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem hint_coeffs {x y : State} {k : Nat} {f : Nat → Vector Bool n} (hx : VG.Proof.MlDsa.X86_64.Sign.HFam x 5 k f) (hy : VG.Proof.MlDsa.X86_64.Sign.HFam y 5 k f) :
    (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.X86_64.Sign.pa x (Impl.MlDsa.X86_64.Sign.hP 0)) i).toNat) =
      (List.range (256 * k)).map (fun i => (coeffAt y.mem (VG.Proof.MlDsa.X86_64.Sign.pa y (Impl.MlDsa.X86_64.Sign.hP 0)) i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ s : State, coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (Impl.MlDsa.X86_64.Sign.hP 0)) i =
      coeffAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (pS (5 + i / 256))) (i % 256) := fun s => by
    rw [VG.Proof.MlDsa.X86_64.Sign.pS_hint s (i / 256)]
    simp only [coeffAt]
    rw [VG.Proof.MlKem.X86_64.off_add (VG.Proof.MlDsa.X86_64.Sign.pa s _) (1024 * (i / 256)), show 1024 * (i / 256) + 4 * (i % 256) = 4 * i by omega]
  have hq : i / 256 < k := by omega
  have hj : i % 256 < n := Nat.mod_lt _ (by decide)
  have ex := (hx _ hq).2 0 (by decide) _ hj
  have ey := (hy _ hq).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [e x, e y, ex, ey]

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, VG.Proof.MlDsa.X86_64.Sign.IK p D σ s ∧ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.X86_64.Sign.CTv p σ κ ∧ VG.Proof.MlDsa.X86_64.Sign.Fam s (VG.Proof.MlDsa.X86_64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.X86_64.Sign.Zv p σ κ) ∧
    VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.X86_64.Sign.Hv p σ κ) ∧ VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ ∧ s.gpr .r15 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, VG.Proof.MlDsa.X86_64.Sign.OS p D σ κ r s ∧ VG.Proof.MlDsa.X86_64.Sign.PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, VG.Proof.MlDsa.X86_64.Sign.HFam x 5 p.k f ∧ VG.Proof.MlDsa.X86_64.Sign.HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Sign.IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yP p r)) ∧ VG.Proof.MlDsa.X86_64.Sign.InRange s.mem (VG.Proof.MlDsa.X86_64.Sign.pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, VG.Proof.MlDsa.X86_64.Sign.inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) (hc : VG.Proof.MlDsa.X86_64.Sign.oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D E (VG.Proof.MlDsa.X86_64.Sign.IOi p D) x y ∧ VG.Proof.MlDsa.X86_64.Sign.HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  have hcc := VG.Proof.MlDsa.X86_64.Sign.copyChk_spec cc
  unfold output
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D E (VG.Proof.MlDsa.X86_64.Sign.IOr p D 0) x y ∧ VG.Proof.MlDsa.X86_64.Sign.HJ p x y) (VG.Proof.MlDsa.X86_64.Sign.liftQ
    (F := fun s s' => ∀ f, VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.X86_64.Sign.HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (VG.Proof.MlDsa.X86_64.Sign.outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
        (P := fun x y => VG.Proof.MlDsa.X86_64.Sign.LRel D (VG.Proof.MlDsa.X86_64.Sign.sgR p) (VG.Proof.MlDsa.X86_64.Sign.sgW p) x y)
        fun x y h => ⟨h.regs (.r14, p.sigLen) (by simp [VG.Proof.MlDsa.X86_64.Sign.sgR, VG.Proof.MlDsa.X86_64.Sign.sgW]), VG.Proof.MlDsa.X86_64.Sign.lrel_rbx h _ (List.mem_singleton_self _)⟩)
      (fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk.d.im.st) fun _ _ h => h)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.X86_64.Sign.RS p D E (VG.Proof.MlDsa.X86_64.Sign.IOr p D p.ℓ) x y ∧ VG.Proof.MlDsa.X86_64.Sign.HJ p x y) (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.seqR_tr
    (R := fun r x y => VG.Proof.MlDsa.X86_64.Sign.RS p D E (VG.Proof.MlDsa.X86_64.Sign.IOr p D r) x y ∧ VG.Proof.MlDsa.X86_64.Sign.HJ p x y) p.ℓ 0 fun r _ hr => VG.Proof.MlDsa.X86_64.Sign.liftQ
      (F := fun s s' => ∀ f, VG.Proof.MlDsa.X86_64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.X86_64.Sign.HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Sign.packZ_ok hP hc (by omega) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.bpAt_tr hP hbp hzl (cz r (by omega)).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega), i₂.zr (by omega)⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨VG.Proof.MlDsa.X86_64.Sign.hones_ok o₁ a₁, VG.Proof.MlDsa.X86_64.Sign.hones_ok o₂ a₂, VG.Proof.MlDsa.X86_64.Sign.hint_coeffs hx hy⟩

theorem XS.io (hf : VG.Proof.MlDsa.X86_64.Sign.fChk p = true) {σ x₀ x : State} (h : VG.Proof.MlDsa.X86_64.Sign.XS p D σ x₀) (h15 : x₀.gpr .r15 = 1)
    (hP : VG.Proof.MlDsa.X86_64.Sign.PPostB D x₀ x []) (hcs : ∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) : VG.Proof.MlDsa.X86_64.Sign.IOi p D σ x := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.fChk, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf
  have L := h.k.d.im.st.lay
  obtain ⟨t, _, _, _, hpass, hct, hz, hh⟩ := h.pass h15
  exact ⟨p.ℓ * t, h.k.step hP ik, by rw [L.keepBytes hP kct, hct], Fam.keep L hP fy hz, HFam.keep L hP f5 hh, hpass,
    by rw [hcs _ (by decide), h15]⟩

theorem rest_tr {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.X86_64.Sign.Ok3 p) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p 0) (VG.Proof.MlDsa.X86_64.Sign.IM p D)) (rest P p) (VG.Proof.MlDsa.X86_64.Sign.RS p D (VG.Proof.MlDsa.X86_64.Sign.LeakEq p 0) (VG.Proof.MlDsa.X86_64.Sign.FS p D)) := by
  refine VG.Proof.MlDsa.X86_64.Sign.liftR (fun σ s _ h => VG.Proof.MlDsa.X86_64.Sign.rest_ok hP h3 h) ?_
  have hc := VG.Proof.MlDsa.X86_64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.X86_64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.X86_64.Sign.fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, f5⟩, -⟩, -⟩, -⟩ := hf'
  have hp := VG.Proof.MlDsa.X86_64.Sign.paramsOk h3
  unfold rest
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.decode_tr hP hd) (RelCT.seq (VG.Proof.MlDsa.X86_64.Sign.signLoop_tr hP hp hc1 hb hks hl) ?_)
  unfold ifOk
  refine VG.Proof.MlDsa.X86_64.Sign.ifOkElse_tr (D := D) (fun x y h => by rw [h.2.1]) (RelCT.mono (VG.Proof.MlDsa.X86_64.Sign.output_tr hP ho (E := fun _ _ => True))
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, _, s₁, s₂⟩, h15, hj⟩, ⟨hPx, hcx, _⟩, ⟨hPy, hcy, _⟩, hne⟩ => ?_)
    fun _ _ h => h) (RelCT.mono VG.Proof.MlDsa.X86_64.Sign.nil_tr (fun _ _ h => h) fun _ _ _ => trivial)
  have e₁ := VG.Proof.MlDsa.X86_64.Sign.r15_one s₁.r01 hne
  have e₂ : y₀.gpr .r15 = 1 := h15 ▸ e₁
  obtain ⟨_, f, hx, hy⟩ := hj e₁
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, s₁.io hf e₁ hPx hcx, s₂.io hf e₂ hPy hcy⟩, f,
    HFam.keep s₁.k.d.im.st.lay hPx f5 hx, HFam.keep s₂.k.d.im.st.lay hPy f5 hy⟩

end

end VG.Proof.MlDsa.X86_64.Sign

end
