import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlDsa.Sign.Vals
import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Round.Bits
import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPackCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Lay`. -/
section

/-!
# ML-DSA signing on ARMv7: the buffers of the function

As on x86-64 (`Proof/MlDsa/X86_64/Sign/Lay.lean`): the function keeps the
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

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : VG.Impl.MlDsa.Arm.Sign.Ptr) : Addr := State.addr (s.gpr p.1) + BitVec.ofNat 64 p.2

/-- `s'` keeps the callee-saved registers of `s` (but `lr`). -/
abbrev CS (s s' : State) : Prop := ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r

theorem CS.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.Arm.Sign.CS s₁ s₂) (h₂ : VG.Proof.MlDsa.Arm.Sign.CS s₂ s₃) : VG.Proof.MlDsa.Arm.Sign.CS s₁ s₃ :=
  fun r hr hl => (h₂ r hr hl).trans (h₁ r hr hl)

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.Arm.Sign.Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the function writes (`scratch` and `sig`):
a buffer it only reads may overlap another such buffer, but not one of
these. -/
abbrev wRegs : List Reg := [.r7, .r8]

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.Arm.Sign.Ptr) (l : Nat) (q : VG.Impl.MlDsa.Arm.Sign.Ptr) (k : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB bs p l && VG.Proof.MlDsa.Arm.Sign.inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ VG.Proof.MlDsa.Arm.Sign.wRegs) || decide (q.1 ∈ VG.Proof.MlDsa.Arm.Sign.wRegs))) ||
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
      exact List.mem_cons_of_mem _ (VG.Proof.MlDsa.Arm.Sign.lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold VG.Proof.MlDsa.Arm.Sign.inB at h
  split at h
  · rename_i n hn; exact ⟨n, VG.Proof.MlDsa.Arm.Sign.lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : VG.Impl.MlDsa.Arm.Sign.Ptr} {l k : Nat} (h : VG.Proof.MlDsa.Arm.Sign.sepB bs p l q k = true) :
    VG.Proof.MlDsa.Arm.Sign.inB bs p l = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ VG.Proof.MlDsa.Arm.Sign.wRegs ∨ q.1 ∈ VG.Proof.MlDsa.Arm.Sign.wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1 |> fun h1 => ⟨h1, h.1.2, h.2⟩

/-! ## Regions -/

/-- A range at an offset of a range a region contains. -/
theorem contains_sub {r : Region} {a : Addr} {n off l : Nat} (h : r.Contains a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : r.Contains (a + BitVec.ofNat 64 off) l := by
  simp only [Region.Contains] at h ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, VG.Proof.MlDsa.Arm.Sign.contains_sub hc hl hn⟩

/-! ## Layouts -/

section
variable (D : Nat)

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other and from the `D` bytes of
stack below the stack pointer, not wrapping around, and permitted; and `D`
bytes of stack below the stack pointer that do not wrap around. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ VG.Proof.MlDsa.Arm.Sign.wRegs ∨ b'.1 ∈ VG.Proof.MlDsa.Arm.Sign.wRegs) →
    Region.Disjoint ⟨State.addr (s.gpr b.1), b.2⟩ ⟨State.addr (s.gpr b'.1), b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (belowA s.sp D).Disjoint ⟨State.addr (s.gpr b.1), b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 32
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (State.addr (s.gpr b.1)) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (State.addr (s.gpr b.1)) b.2
  sp : D ≤ s.sp.toNat

end

theorem addr_toNat32 (a : BitVec 32) : (State.addr a).toNat = a.toNat := addr_toNat' a

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
include L

omit L in
theorem sub_of_inB {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩ ⟨State.addr (s.gpr p.1), n⟩ := by
  obtain ⟨n, hm, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec h
  exact ⟨n, hm, Offset.sub_base _ hl⟩

theorem Lay.disj {p q : VG.Impl.MlDsa.Arm.Sign.Ptr} {l k : Nat} (h : VG.Proof.MlDsa.Arm.Sign.sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩ ⟨VG.Proof.MlDsa.Arm.Sign.pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := VG.Proof.MlDsa.Arm.Sign.sepB_spec h
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec hp
  obtain ⟨m, hm, hk⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (Offset.sub_base _ hl)).sub_right (Offset.sub_base _ hk)
  · show Region.Disjoint ⟨State.addr (s.gpr p.1) + _, l⟩ ⟨State.addr (s.gpr q.1) + _, k⟩
    rw [← e]
    exact Offset.disjoint _ hs (by omega) (by omega)

theorem Lay.stkD {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) :
    (belowA s.sp D).Disjoint ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := VG.Proof.MlDsa.Arm.Sign.sub_of_inB (s := s) h
  exact (L.stk _ hn).sub_right hsub

/-- The region does not wrap around the 32-bit address space. -/
theorem Lay.nwp {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) :
    (s.gpr p.1).toNat + p.2 + l ≤ 2 ^ 32 := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec h
  have h1 := L.nw _ hn
  simp only at h1
  omega

/-- The 32-bit sum of a register and an offset, as a 64-bit address. -/
theorem Lay.pa32 {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) (hl : 0 < l) :
    State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2) = VG.Proof.MlDsa.Arm.Sign.pa s p :=
  addr_add (by have := L.nwp h; omega)

/-- `Lay.pa32`, as the contracts state addresses. -/
theorem Lay.w {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) (hl : 0 < l) :
    BitVec.setWidth 64 (s.gpr p.1 + BitVec.ofNat 32 p.2) = VG.Proof.MlDsa.Arm.Sign.pa s p :=
  L.pa32 h hl

theorem Lay.fit {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) (hl : 0 < l) :
    (s.gpr p.1 + BitVec.ofNat 32 p.2).toNat + l ≤ 2 ^ 32 := by
  have := L.nwp h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem Lay.lenlt {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) : l < 2 ^ 32 := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec h
  have := L.small _ hn
  simp only at this; omega

/-- `Lay.pa32`, for a buffer written. -/
theorem Lay.pa32W {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB wbs p l = true) (hl : 0 < l) :
    State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2) = VG.Proof.MlDsa.Arm.Sign.pa s p := by
  obtain ⟨n, hn, hl'⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec h
  have := L.nw _ (List.mem_append_right _ hn)
  exact addr_add (by simp only at this; omega)

theorem Lay.iR {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.Arm.Sign.pa s p) l := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec h
  exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega)

theorem Lay.iW {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB wbs p l = true) : InRegions s.wr (VG.Proof.MlDsa.Arm.Sign.pa s p) l := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec h
  exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega)

theorem Lay.cR {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) : Covers [⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩] (s.rd ++ s.wr) :=
  Covers.one (L.iR h)

theorem Lay.cW {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB wbs p l = true) : Covers [⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩] s.wr :=
  Covers.one (L.iW h)

end

/-! ## What a piece of code leaves -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : VG.Impl.MlDsa.Arm.Sign.Ptr × Nat) : Region := ⟨VG.Proof.MlDsa.Arm.Sign.pa s w.1, w.2⟩

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.r7, .r4, .r5, .r6, .r8]

theorem bases_cs : ∀ r ∈ VG.Proof.MlDsa.Arm.Sign.bases, r ∈ preserved ∧ r ≠ .lr := by decide

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the `D` bytes of stack. -/
structure PostB (D : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ VG.Proof.MlDsa.Arm.Sign.bases, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  frame : Frame (W ++ [belowA s.sp D]) s.mem s'.mem

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (D : Nat) (s s' : State) (ws : List (VG.Impl.MlDsa.Arm.Sign.Ptr × Nat)) : Prop := VG.Proof.MlDsa.Arm.Sign.PostB D s s' (ws.map (VG.Proof.MlDsa.Arm.Sign.toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (VG.Impl.MlDsa.Arm.Sign.Ptr × Nat)) (p : VG.Impl.MlDsa.Arm.Sign.Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && VG.Proof.MlDsa.Arm.Sign.inB bs p l && ws.all fun w => VG.Proof.MlDsa.Arm.Sign.sepB bs p l w.1 w.2

theorem inB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB bs (r, o) L = true)
    (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.Arm.Sign.inB bs (r, o') l = true := by
  unfold VG.Proof.MlDsa.Arm.Sign.inB at h ⊢
  split at h
  · rename_i n hn
    simp only [hn, decide_eq_true_eq] at h ⊢
    omega
  · cases h

theorem sepB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} {q : VG.Impl.MlDsa.Arm.Sign.Ptr} {k : Nat}
    (h : VG.Proof.MlDsa.Arm.Sign.sepB bs (r, o) L q k = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.Arm.Sign.sepB bs (r, o') l q k = true := by
  unfold VG.Proof.MlDsa.Arm.Sign.sepB at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hp, hq⟩, hs⟩ := h
  refine ⟨⟨VG.Proof.MlDsa.Arm.Sign.inB_sub hp h2, hq⟩, ?_⟩
  rcases hs with hs | ⟨he, hs⟩
  · exact .inl hs
  · exact .inr ⟨he, by omega⟩

theorem keepB_sub {bs : List (Reg × Nat)} {ws : List (VG.Impl.MlDsa.Arm.Sign.Ptr × Nat)} {r : Reg} {o L o' l : Nat}
    (h : VG.Proof.MlDsa.Arm.Sign.keepB bs ws (r, o) L = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : VG.Proof.MlDsa.Arm.Sign.keepB bs ws (r, o') l = true := by
  unfold VG.Proof.MlDsa.Arm.Sign.keepB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨h.1.1, VG.Proof.MlDsa.Arm.Sign.inB_sub h.1.2 h2⟩, fun w hw => VG.Proof.MlDsa.Arm.Sign.sepB_sub (h.2 w hw) h1 h2⟩

theorem PostB.pa {D : Nat} {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.Arm.Sign.PostB D s s' W) {p : VG.Impl.MlDsa.Arm.Sign.Ptr} (h : p.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    VG.Proof.MlDsa.Arm.Sign.pa s' p = VG.Proof.MlDsa.Arm.Sign.pa s p := by
  simp only [VG.Proof.MlDsa.Arm.Sign.pa, hP.bs _ h]

theorem PostB.refl (D : Nat) (s : State) (W : List Region) : VG.Proof.MlDsa.Arm.Sign.PostB D s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.of_cs {D : Nat} {s s' : State} (hcs : VG.Proof.MlDsa.Arm.Sign.CS s s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {W : List Region} (hf : Frame W s.mem s'.mem) : VG.Proof.MlDsa.Arm.Sign.PostB D s s' W :=
  ⟨hrd, hwr, fun r hr => hcs r (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).1 (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).2, hsp,
    hf.mono fun _ hr => List.mem_append_left _ hr⟩

theorem PostB.trans {D : Nat} {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : VG.Proof.MlDsa.Arm.Sign.PostB D s s₁ W₁)
    (h₂ : VG.Proof.MlDsa.Arm.Sign.PostB D s₁ s₂ W₂) (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : VG.Proof.MlDsa.Arm.Sign.PostB D s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.sp.trans h₁.sp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.sp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

theorem map_toR_post {D : Nat} {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.Arm.Sign.PostB D s s' W) {ws : List (VG.Impl.MlDsa.Arm.Sign.Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) : ws.map (VG.Proof.MlDsa.Arm.Sign.toR s') = ws.map (VG.Proof.MlDsa.Arm.Sign.toR s) :=
  List.map_congr_left fun w hw => by simp only [VG.Proof.MlDsa.Arm.Sign.toR, hP.pa (h w hw)]

/-- `PostB.trans`, with the regions written given as pointers. -/
theorem PPostB.trans {D : Nat} {s s₁ s₂ : State} {ws₁ ws₂ ws : List (VG.Impl.MlDsa.Arm.Sign.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.Arm.Sign.PPostB D s s₁ ws₁)
    (h₂ : VG.Proof.MlDsa.Arm.Sign.PPostB D s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : VG.Proof.MlDsa.Arm.Sign.PPostB D s s₂ ws := by
  have h₂' : VG.Proof.MlDsa.Arm.Sign.PostB D s₁ s₂ (ws₂.map (VG.Proof.MlDsa.Arm.Sign.toR s)) := by rw [← VG.Proof.MlDsa.Arm.Sign.map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem Lay.post {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} {W : List Region} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    (hP : VG.Proof.MlDsa.Arm.Sign.PostB D s s' W) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s' := by
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
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {ws : List (VG.Impl.MlDsa.Arm.Sign.Ptr × Nat)}
  {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (VG.Proof.MlDsa.Arm.Sign.toR s) ++ [belowA s.sp D], Region.Disjoint ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩ r := by
  simp only [VG.Proof.MlDsa.Arm.Sign.keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

omit L in
theorem keepB_cs (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p l = true) : p.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  simp only [VG.Proof.MlDsa.Arm.Sign.keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

omit L in
theorem keepB_in (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p l = true) : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.keepB, Bool.and_eq_true] at hc; exact hc.1.2

theorem Lay.keepBytes (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p l = true) :
    VG.Spec.Sha3.bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' p) l = VG.Spec.Sha3.bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) l := by
  rw [hP.pa (VG.Proof.MlDsa.Arm.Sign.keepB_cs hc)]
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec (VG.Proof.MlDsa.Arm.Sign.keepB_in hc)
  exact VG.Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : VG.Spec.MlDsa.Poly} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : PolyIs s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) f) : PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' p) f := by
  rw [hP.pa (VG.Proof.MlDsa.Arm.Sign.keepB_cs hc)]
  exact VG.Proof.MlDsa.Sign.polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepRed (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p)) : Reduced s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' p) := by
  rw [hP.pa (VG.Proof.MlDsa.Arm.Sign.keepB_cs hc)]
  exact VG.Proof.MlDsa.Sign.reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p 1024 = true) :
    polyAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' p) = polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) := by
  rw [hP.pa (VG.Proof.MlDsa.Arm.Sign.keepB_cs hc)]
  exact VG.Proof.MlDsa.Sign.polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepW (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p 4 = true) :
    s'.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s' p) 32 = s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s p) 32 := by
  rw [hP.pa (VG.Proof.MlDsa.Arm.Sign.keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-! ## Two runs in the same layout -/

/-- Two states in the same layout, with the same stack pointer. -/
structure LRel (D : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop where
  lx : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs x
  ly : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs y
  regs : ∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1
  sp : x.sp = y.sp

theorem LRel.eq {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y) {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat}
    (hp : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := VG.Proof.MlDsa.Arm.Sign.inB_spec hp
  exact h.regs (p.1, n) hn

theorem LRel.pa {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y) {p : VG.Impl.MlDsa.Arm.Sign.Ptr} {l : Nat}
    (hp : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) : VG.Proof.MlDsa.Arm.Sign.pa x p = VG.Proof.MlDsa.Arm.Sign.pa y p := by
  simp only [VG.Proof.MlDsa.Arm.Sign.pa, h.eq hp]

theorem LRel.post {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hx : VG.Proof.MlDsa.Arm.Sign.PostB D x x' W₁) (hy : VG.Proof.MlDsa.Arm.Sign.PostB D y y' W₂) :
    VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x' y' :=
  ⟨h.lx.post hx hcs, h.ly.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb), h.regs b hb],
    by rw [hx.sp, hy.sp, h.sp]⟩

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call`. -/
section

/-!
# ML-DSA signing on ARMv7: calls of verified code

`setArgs as` moves each argument (a pointer or an immediate) into its register
(`r0`–`r3`, `r12`, `lr`): afterwards each holds the argument's value in the
state before the moves, and nothing else changed but those registers
(`setArgs_ok`). A primitive the function calls is any code verified against
its shared contract (`Spec/MlDsa/Poly.lean`) for some stack of `S` bytes that,
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

theorem Keep.refl (rs : List Reg) (s : State) : VG.Proof.MlDsa.Arm.Sign.Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.Arm.Sign.Keep rs s₁ s₂) (h₂ : VG.Proof.MlDsa.Arm.Sign.Keep rs s₂ s₃) : VG.Proof.MlDsa.Arm.Sign.Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.MlDsa.Arm.Sign.Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.MlDsa.Arm.Sign.Keep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

theorem argRegs_cs : ∀ r ∈ preserved, r ≠ .lr → r ∉ VG.Proof.MlDsa.Arm.Sign.argRegs := by decide

theorem Keep.cs {s s' : State} (h : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s') : VG.Proof.MlDsa.Arm.Sign.CS s s' := fun r hr hl => h.gpr r (VG.Proof.MlDsa.Arm.Sign.argRegs_cs r hr hl)

/-! ## Moves -/

theorem movi_val (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  have e1 : BitVec.ofNat 16 (v / 65536) = (BitVec.ofNat 32 v).extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have e2 : BitVec.ofNat 16 v = (BitVec.ofNat 32 v).extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [e1, e2]; exact movw_movt _

theorem movi_ok (d : Reg) (v : Nat) (s : State) :
    WP isa (.block (movi d v)) s fun s1 => s1.gpr d = BitVec.ofNat 32 v ∧ VG.Proof.MlDsa.Arm.Sign.Keep [d] s s1 := by
  run_block [movi]
  refine ⟨by simp [VG.Proof.MlDsa.Arm.Sign.movi_val], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp [hr]

theorem lea_ok (d : Reg) (p : Ptr) (hd : p.1 ≠ d) (s : State) :
    WP isa (.block (lea d p)) s fun s1 => s1.gpr d = s.gpr p.1 + BitVec.ofNat 32 p.2 ∧ VG.Proof.MlDsa.Arm.Sign.Keep [d] s s1 := by
  run_block [lea, movi, hd]
  refine ⟨by simp [VG.Proof.MlDsa.Arm.Sign.movi_val, BitVec.add_comm], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp [hr]

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.Arm.Sign.Arg.val (s : State) : Arg → BitVec 32
  | .ptr p => s.gpr p.1 + BitVec.ofNat 32 p.2
  | .imm v => BitVec.ofNat 32 v

/-- A pointer in a register of `bases`, or an immediate. -/
def _root_.VG.Impl.MlDsa.Arm.Sign.Arg.ok : Arg → Bool
  | .ptr p => decide (p.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)
  | .imm _ => true

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ VG.Proof.MlDsa.Arm.Sign.argRegs) (s : State) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ VG.Proof.MlDsa.Arm.Sign.Keep [d] s s1 := by
  cases a with
  | ptr p =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact VG.Proof.MlDsa.Arm.Sign.lea_ok d p (fun e => by revert ha hd; rw [e]; cases d <;> decide) s
  | imm v => exact VG.Proof.MlDsa.Arm.Sign.movi_ok d v s

theorem setArgsTo_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ VG.Proof.MlDsa.Arm.Sign.argRegs) →
    as.all Arg.ok = true → ∀ s : State,
    WP isa (.block (setArgsTo ds as)) s fun s1 => (∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ VG.Proof.MlDsa.Arm.Sign.Keep ds s s1
  | [], _, _, _, _, s => WP.block_nil ⟨fun _ h => by simp at h, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s => WP.block_nil ⟨fun _ h => by simp at h, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [setArgsTo, List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha.1 (hd d (List.mem_cons_self ..)) s) fun s1 ⟨h1, k1⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setArgsTo_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1)
      fun s2 ⟨h2, k2⟩ => ⟨fun da hda => ?_, (k1.mono fun r hr => by simp_all).trans (k2.mono fun r hr => by simp [hr])⟩
    -- The values in `s1` are those in `s`: the moves keep the bases.
    have hval : ∀ b : Arg, b.ok = true → b.val s1 = b.val s := fun b hb => by
      cases b with
      | ptr p =>
        simp only [Arg.ok, decide_eq_true_eq] at hb
        simp only [Arg.val]
        have hdb : d ∈ VG.Proof.MlDsa.Arm.Sign.argRegs := hd d (List.mem_cons_self ..)
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
      VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 :=
  VG.Proof.MlDsa.Arm.Sign.setArgsTo_ok argRegs6 as VG.Proof.MlDsa.Arm.Sign.argRegs6_nodup (fun _ h => h) ha s

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
  exact ⟨(VG.Proof.MlDsa.Arm.Sign.execBlock_nomem h e₁).trans (VG.Proof.MlDsa.Arm.Sign.execBlock_nomem h e₂).symm, trivial⟩

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

theorem argsIn2 {a b : Arg} {s s1 : State} (h : VG.Proof.MlDsa.Arm.Sign.ArgsIn [a, b] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6])⟩

theorem argsIn3 {a b c : Arg} {s s1 : State} (h : VG.Proof.MlDsa.Arm.Sign.ArgsIn [a, b, c] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6])⟩

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : VG.Proof.MlDsa.Arm.Sign.ArgsIn [a, b, c, d] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : VG.Proof.MlDsa.Arm.Sign.ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s ∧
      s1.gpr .r12 = e.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6]), h (.r12, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : VG.Proof.MlDsa.Arm.Sign.ArgsIn [a, b, c, d, e, f] s s1) :
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
    (hpre : ∀ s1, VG.Proof.MlDsa.Arm.Sign.ArgsIn as s s1 → VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callR n c as) s fun s' => VG.Proof.MlDsa.Arm.Sign.PostB D s s' wr ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      ∃ s1, VG.Proof.MlDsa.Arm.Sign.ArgsIn as s s1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 ∧ k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.setArgs_ok as ha s) fun s1 ⟨hA, k1⟩ => ?_)
  refine WP.callF hv (hpre s1 hA k1) (by rw [k1.rd, k1.wr]; exact hc) (by rw [k1.wr]; exact hw)
    (by rw [k1.sp]; omega) fun s' hrd hwr hsp' hf hcs hpost => ?_
  have hcs' : VG.Proof.MlDsa.Arm.Sign.CS s s' := CS.trans k1.cs hcs
  rw [k1.mem, k1.sp] at hf
  exact ⟨⟨hrd.trans k1.rd, hwr.trans k1.wr, fun r hr => hcs' r (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).1 (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).2,
    hsp'.trans k1.sp, VG.Proof.MlDsa.Arm.Sign.belowA_mono hsu hf⟩, hcs', s1, hA, k1, hpost⟩

/-! ## Calls with arguments on the stack -/

theorem frame8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩ : Region) =
      belowA s.sp 8 := by
  simp only [belowA, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  rw [VG.Proof.MlKem.Arm.addr_sub hsp]

theorem ne12_pres : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r12 := by decide

theorem argR_contains {s : State} {x : Addr} {m : Nat} (h : (VG.Proof.MlDsa.Arm.Sign.argR s).Contains x m) :
    (belowA s.sp 8).Contains x m := by
  simp only [Region.Contains, belowA] at h ⊢; omega

theorem sp_sub8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : (sp - BitVec.ofNat 32 8).toNat = sp.toNat - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem argR_sub (s : State) : Region.Sub (VG.Proof.MlDsa.Arm.Sign.argR s) (belowA s.sp 8) := fun x hx => by
  simp only [Region.Contains, belowA] at hx ⊢; omega

/-- The moves of the arguments, then a call of verified code in a frame that
pushes its fifth and sixth arguments (`r12`, `lr`). -/
theorem callS_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : 8 + stackUse c ≤ D) {as : List Arg} (ha : as.all Arg.ok = true) {s : State} (hsp : D ≤ s.sp.toNat)
    {rd wr : List Region}
    (hpre : ∀ s1, VG.Proof.MlDsa.Arm.Sign.ArgsIn as s s1 → VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 →
      k.pre ((pushed [.r12, .lr] s1).callEntry.withRegions (rd ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) wr))
    (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callS n c as) s fun s' => VG.Proof.MlDsa.Arm.Sign.PostB D s s' wr ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      ∃ s1, VG.Proof.MlDsa.Arm.Sign.ArgsIn as s s1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .r12 → s₂.gpr r = s'.gpr r) ∧
        k.post ((pushed [.r12, .lr] s1).callEntry.withRegions (rd ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) wr)
          (s₂.withRegions (rd ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) wr) := by
  have h8 : 8 ≤ s.sp.toNat := by omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.setArgs_ok as ha s) fun s1 ⟨hA, k1⟩ => ?_)
  have h8' : 8 ≤ s1.sp.toNat := by rw [k1.sp]; exact h8
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8') (by decide) ?_
  have hwp : (pushed [.r12, .lr] s1).wr = belowA s.sp 8 :: s.wr := by
    rw [VG.Arm.pushed_wr, VG.Proof.MlDsa.Arm.Sign.frame8 h8', k1.wr, k1.sp]
  refine WP.callF hv (hpre s1 hA k1) (fun x m hx => ?_) (fun x m hx => ?_) ?_ fun s₂ hrd hwr hsp₂ hf hcs hpost => ?_
  · rw [VG.Arm.pushed_rd, hwp, k1.rd]
    rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), VG.Proof.MlDsa.Arm.Sign.argR_contains hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · rw [hwp]
    obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [VG.Arm.pushed_sp, k1.sp, show BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 from rfl,
      VG.Proof.MlDsa.Arm.Sign.sp_sub8 h8]; omega
  · have hcs₂ : VG.Proof.MlDsa.Arm.Sign.CS s s₂ := fun r hr hl => by rw [hcs r hr hl, VG.Arm.pushed_gpr]; exact k1.cs r hr hl
    have hsp₂' : s₂.sp = s.sp - BitVec.ofNat 32 8 := by rw [hsp₂, VG.Arm.pushed_sp, k1.sp]; rfl
    have f₁ := push2_frame h8'
    rw [k1.mem] at f₁
    have hsu' : 8 + stackUse c ≤ s.sp.toNat := by omega
    refine ⟨⟨by simp only [popped_rd, hrd, VG.Arm.pushed_rd, k1.rd], by simp only [popped_wr, hwr, hwp, List.tail_cons],
      fun r hr => (popped_gpr (VG.Proof.MlDsa.Arm.Sign.ne12_pres r (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).1 (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).2) _ _).trans
        (hcs₂ r (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).1 (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).2), by rw [popped_sp, hsp₂']; exact BitVec.sub_add_cancel _ _, ?_⟩,
      fun r hr hl => by rw [popped_gpr (VG.Proof.MlDsa.Arm.Sign.ne12_pres r hr hl)]; exact hcs₂ r hr hl,
      s1, hA, k1, s₂, rfl, fun r hr => (popped_gpr hr _ _).symm, hpost⟩
    rw [popped_mem]
    rw [VG.Arm.pushed_sp, k1.sp] at hf
    refine (f₁.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      show ∃ r', r' ∈ wr ++ [belowA s.sp D] ∧ (belowA s1.sp 8).Sub r'
      rw [k1.sp]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun x h => belowA_sub (show 8 + stackUse c ≤ D by omega) x (belowA_push hsu' x h)⟩

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
    (hr : VG.Proof.MlDsa.Arm.Sign.RetPub k c) {P : State → State → Prop}
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
      obtain ⟨n₁, x₁, g₁⟩ := VG.Proof.MlDsa.Arm.Sign.narrow_run hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨n₂, x₂, g₂⟩ := VG.Proof.MlDsa.Arm.Sign.narrow_run hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      rw [ret_eq r₁, ret_eq r₂]
      exact ⟨by simp only [ht], show _ = _ by rw [← g₁, ← g₂]; exact hrax⟩

/-- Constant time, as `RelCT.callEx` needs it. -/
theorem ct_or {k : Contract isa} {c : Prog isa} (hct : ConstantTime isa k.pre k.pub c) :
    RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 ∨ True :=
  fun _ _ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ⟨hct _ _ _ _ _ _ h₁ h₂ hp e₁ e₂, .inr trivial⟩

/-- The moves of the arguments, from two related states. -/
theorem setArgs_rel {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop} :
    RelCT isa P (.block (setArgs as)) fun x1 y1 => ∃ x y, P x y ∧ (VG.Proof.MlDsa.Arm.Sign.ArgsIn as x x1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1) ∧
      (VG.Proof.MlDsa.Arm.Sign.ArgsIn as y y1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs y y1) :=
  RelCT.mono (RelCT.wpDep (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr (VG.Proof.MlDsa.Arm.Sign.setArgsTo_nomem _ _))
    (fun x y _ => ⟨VG.Proof.MlDsa.Arm.Sign.setArgs_ok as ha x, VG.Proof.MlDsa.Arm.Sign.setArgs_ok as ha y⟩)) (fun _ _ h => h)
    fun _ _ ⟨_, x, y, hp, h1, h2⟩ => ⟨x, y, hp, h1, h2⟩

/-- Region lists for the two runs of a call. -/
abbrev Regs2 (k : Contract isa) (x1 y1 : State) : Prop := ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
  k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
  k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
  Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧ Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr

theorem callR_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.Arm.Sign.ArgsIn as x x1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1 → VG.Proof.MlDsa.Arm.Sign.ArgsIn as y y1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs y y1 →
      VG.Proof.MlDsa.Arm.Sign.Regs2 k x1 y1) :
    RelCT isa P (callR n c as) fun _ _ => True :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Sign.setArgs_rel ha) (RelCT.callEx hv (VG.Proof.MlDsa.Arm.Sign.ct_or hct) fun _ _ ⟨x, y, hp, h1, h2⟩ => hP x y _ _ hp h1 h2)

theorem callRRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : VG.Proof.MlDsa.Arm.Sign.RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.Arm.Sign.ArgsIn as x x1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1 → VG.Proof.MlDsa.Arm.Sign.ArgsIn as y y1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs y y1 →
      VG.Proof.MlDsa.Arm.Sign.Regs2 k x1 y1) :
    RelCT isa P (callR n c as) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Sign.setArgs_rel ha) (RelCT.callRet hv hr fun _ _ ⟨x, y, hp, h1, h2⟩ => hP x y _ _ hp h1 h2)

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
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.Arm.Sign.ArgsIn as x x1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1 → VG.Proof.MlDsa.Arm.Sign.ArgsIn as y y1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs y y1 →
      VG.Proof.MlDsa.Arm.Sign.Regs2 k (pushed [.r12, .lr] x1) (pushed [.r12, .lr] y1)) :
    RelCT isa P (callS n c as) fun _ _ => True :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Sign.setArgs_rel ha) (VG.Arm.RelCT.frame
    (fun _ _ ⟨x, y, hp, h1, h2⟩ => by rw [h1.2.sp, h2.2.sp]; exact hsp x y hp)
    (RelCT.callEx hv (VG.Proof.MlDsa.Arm.Sign.ct_or hct) fun _ _ ⟨x1, y1, ⟨x, y, hp, h1, h2⟩, ea, eb⟩ => by
      rw [(VG.Arm.push_pushed' ea).1, (VG.Arm.push_pushed' eb).1]; exact hP x y x1 y1 hp h1 h2))

theorem callSRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : VG.Proof.MlDsa.Arm.Sign.RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.Arm.Sign.ArgsIn as x x1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1 → VG.Proof.MlDsa.Arm.Sign.ArgsIn as y y1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs y y1 →
      VG.Proof.MlDsa.Arm.Sign.Regs2 k (pushed [.r12, .lr] x1) (pushed [.r12, .lr] y1)) :
    RelCT isa P (callS n c as) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Sign.setArgs_rel ha) (RelCT.frame12
    (fun _ _ ⟨x, y, hp, h1, h2⟩ => by rw [h1.2.sp, h2.2.sp]; exact hsp x y hp)
    (RelCT.callRet hv hr fun _ _ ⟨x1, y1, ⟨x, y, hp, h1, h2⟩, ea, eb⟩ => ea ▸ eb ▸ hP x y x1 y1 hp h1 h2))

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr`. -/
section

/-!
# ML-DSA signing on ARMv7: blocks that leak only their pointers

As on x86-64 (`Proof/MlDsa/X86_64/Sign/BlockTr.lean`): a block whose memory
accesses are `[b, #off]` with `b` among registers `rs` that it never writes
leaks the same from two states that agree on `rs` (`block_tr`). Unlike the
taint analysis, which evaluates the code, this holds for code with immediates
and offsets that are variables, such as the pieces of the function indexed by
a polynomial or an entry of `Â`; `blockOk` is checked by `decide`.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm

/-- The registers the address an instruction accesses uses: its base for the
loads and stores of `[b, #off]`, none for the instructions without a memory
access, and `none` for the others (the stack pointer's). -/
def memBase : Instr → Option (List Reg)
  | .ldr _ n _ | .str _ n _ | .ldrb _ n _ | .strb _ n _ => some [n]
  | .ldrSp .. | .push _ | .pop .. => none
  | _ => some []

/-- Every instruction's addresses use only `rs`, which none writes. -/
def blockOk (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (match VG.Proof.MlDsa.Arm.Sign.memBase i with | some l => l.all (rs.contains ·) | none => false) &&
    rs.all fun r => dstOf i != some r

theorem addrs_agree {rs : List Reg} {i : Instr} {l : List Reg} (h : VG.Proof.MlDsa.Arm.Sign.memBase i = some l) (hl : ∀ r ∈ l, r ∈ rs)
    {s s' : State} (hs : ∀ r ∈ rs, s.gpr r = s'.gpr r) : addrs i s = addrs i s' := by
  cases i <;> simp only [VG.Proof.MlDsa.Arm.Sign.memBase, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    first | rfl | simp only [addrs, hs _ (hl _ (List.mem_singleton_self _))]

theorem blockOk_cons {rs : List Reg} {i : Instr} {is : List Instr} (h : VG.Proof.MlDsa.Arm.Sign.blockOk rs (i :: is) = true) :
    (∃ l, VG.Proof.MlDsa.Arm.Sign.memBase i = some l ∧ ∀ r ∈ l, r ∈ rs) ∧ (∀ r ∈ rs, dstOf i ≠ some r) ∧ VG.Proof.MlDsa.Arm.Sign.blockOk rs is = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.blockOk, List.all_cons, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hm, hc⟩, hr⟩ := h
  refine ⟨?_, hc, by simpa [VG.Proof.MlDsa.Arm.Sign.blockOk] using hr⟩
  revert hm
  cases VG.Proof.MlDsa.Arm.Sign.memBase i with
  | some l => intro hm; simp only [List.all_eq_true, List.contains_iff_mem] at hm; exact ⟨l, rfl, hm⟩
  | none => intro hm; cases hm

theorem execBlock_tr {rs : List Reg} : ∀ {is : List Instr}, VG.Proof.MlDsa.Arm.Sign.blockOk rs is = true →
    ∀ {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}, (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) →
      execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) → t₁ = t₂
  | [], _, _, _, _, _, _, _, _, e₁, e₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | i :: is, h, s₁, s₂, s₁', s₂', t₁, t₂, hs, e₁, e₂ => by
    obtain ⟨⟨l, hl, hin⟩, hc, hrest⟩ := VG.Proof.MlDsa.Arm.Sign.blockOk_cons h
    simp only [execBlock] at e₁ e₂
    split at e₁
    · cases e₁
    · rename_i a₁ ha₁
      split at e₂
      · cases e₂
      · rename_i a₂ ha₂
        obtain ⟨⟨u₁, v₁⟩, f₁, g₁⟩ := Option.map_eq_some_iff.mp e₁
        obtain ⟨⟨u₂, v₂⟩, f₂, g₂⟩ := Option.map_eq_some_iff.mp e₂
        simp only [Prod.mk.injEq] at g₁ g₂
        rw [← g₁.2, ← g₂.2, VG.Proof.MlDsa.Arm.Sign.addrs_agree hl hin hs,
          VG.Proof.MlDsa.Arm.Sign.execBlock_tr hrest (fun r hr => by rw [exec_gpr (hc r hr) ha₁, exec_gpr (hc r hr) ha₂, hs r hr]) f₁ f₂]

/-- A block that leaks only addresses from the registers `rs`, which it never writes. -/
theorem block_tr {rs : List Reg} {is : List Instr} (h : VG.Proof.MlDsa.Arm.Sign.blockOk rs is = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨VG.Proof.MlDsa.Arm.Sign.execBlock_tr h (hP _ _ hp) e₁ e₂, trivial⟩

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Keccak`. -/
section

/-!
# ML-DSA signing on ARMv7: SHAKE256 through the sponge functions

As on x86-64: zeroing the Keccak state at `scratch` (`kzero_ok`, from ML-KEM's
`zeroWords_ok`), and the calls of `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` on it, with the working space at `scratch + 200`
(`kabs_ok`, `kpad_ok`, `ksqz_ok`, from ML-KEM's call lemmas of the sponge
functions in their frames, `Proof/MlKem/Arm/Keccak.lean`), and that two runs
in the same layout leak the same (`kabs_tr`, …).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ok pad_ok squeeze_ok absorb_ct pad_ct squeeze_ct
  regA below Kept)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-! ## Checks -/

/-- The Keccak state and the sponge functions' working space. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs (sc 0) 200 && VG.Proof.MlDsa.Arm.Sign.inB wbs (sc 200) 640 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc 0) 200 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc 200) 640 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs (sc 0) 200 (sc 200) 640

/-- A piece of `len` bytes at `src` that `vg_keccak_absorb` reads. -/
def kabsChk (bs : List (Reg × Nat)) (src : Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB bs src len && decide (src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && decide (0 < len) && VG.Proof.MlDsa.Arm.Sign.sepB bs src len (sc 0) 200 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs src len (sc 200) 640

/-- The `len` bytes at `dst` that `vg_keccak_squeeze` writes. -/
def ksqzChk (bs wbs : List (Reg × Nat)) (dst : Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs dst len && VG.Proof.MlDsa.Arm.Sign.inB bs dst len && decide (dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && decide (0 < len) && VG.Proof.MlDsa.Arm.Sign.sepB bs (sc 0) 200 dst len &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs dst len (sc 200) 640

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem kChk_spec {bs wbs : List (Reg × Nat)} (h : VG.Proof.MlDsa.Arm.Sign.kChk bs wbs = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs (sc 0) 200 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB wbs (sc 200) 640 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs (sc 0) 200 = true ∧
      VG.Proof.MlDsa.Arm.Sign.inB bs (sc 200) 640 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc 0) 200 (sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.kChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem kabsChk_spec {bs : List (Reg × Nat)} {src : Ptr} {len : Nat} (h : VG.Proof.MlDsa.Arm.Sign.kabsChk bs src len = true) :
    VG.Proof.MlDsa.Arm.Sign.inB bs src len = true ∧ src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases ∧ 0 < len ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs src len (sc 0) 200 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs src len (sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ksqzChk_spec {bs wbs : List (Reg × Nat)} {dst : Ptr} {len : Nat} (h : VG.Proof.MlDsa.Arm.Sign.ksqzChk bs wbs dst len = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs dst len = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs dst len = true ∧ dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases ∧ 0 < len ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs (sc 0) 200 dst len = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs dst len (sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rate_small {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 31 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- The 8 bytes of stack of a call of a sponge function, apart from the layout. -/
theorem k8 {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) {p : Ptr} {l : Nat}
    (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) (hsp : s1.sp = s.sp) : (below s1 8).Disjoint ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩ := by
  show (belowA s1.sp 8).Disjoint _
  rw [hsp]; exact (L.stkD h).sub_left (belowA_sub hD)

/-- What the sponge functions leave, as `PostB`. -/
theorem postB_kept {s s1 s' : State} (hD : 8 ≤ D) (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) {rs : List Region} {W : List Region}
    (hk : Kept (rs ++ [below s1 8]) s1 s') (hW : ∀ r ∈ rs, r ∈ W) : VG.Proof.MlDsa.Arm.Sign.PostB D s s' W ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' := by
  have hcs : VG.Proof.MlDsa.Arm.Sign.CS s s' := fun r hr hl => (hk.cs r hr hl).trans (k.cs r hr hl)
  refine ⟨⟨hk.rd.trans k.rd, hk.wr.trans k.wr, fun r hr => hcs r (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).1 (VG.Proof.MlDsa.Arm.Sign.bases_cs r hr).2,
    hk.sp.trans k.sp, ?_⟩, hcs⟩
  rw [← k.mem]
  refine hk.frame.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ (hW r hr), fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    show Region.Sub (belowA s1.sp 8) _
    rw [k.sp]; exact belowA_sub hD

/-! ## Zeroing the state -/

theorem kzero_ok {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true) :
    WP isa (.block kzero) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc 0, 200)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      stateAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) = Spec.Sha3.zero := by
  obtain ⟨w0, _, i0, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  rw [kzero, VG.Impl.MlKem.Arm.zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = s.gpr .r7 := by rw [g]; simp [State.setReg]
  have ep : State.addr (s.gpr .r7) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := by simp [VG.Proof.MlDsa.Arm.Sign.pa]
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; have := L.nwp i0; simpa using this) fun k hk => by
      rw [e7, wr, ep]
      exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub (L.iW w0) (by omega) (by decide))
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7, ep] at hf hz
  have hcs : VG.Proof.MlDsa.Arm.Sign.CS s s₂ := fun r hr hl => by
    rw [h₂.gpr, g]
    simp [State.setReg, VG.Proof.MlDsa.Arm.Sign.ne12_pres r hr hl]
  refine ⟨PostB.of_cs hcs (by rw [h₂.rd, rd]) (by rw [h₂.wr, wr]) (by rw [h₂.sp, sp]) (by rw [← m]; exact hf),
    hcs, VG.Proof.MlKem.Arm.Sample.stateAt_zero hz⟩

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .r7 = y.gpr .r7) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.block_tr (rs := [.r7]) (by decide) fun x y hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h x y hp

/-! ## Absorbing -/

theorem kabsOk {src : Ptr} {len rate pos : Nat} (b1 : src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem kabsArgs {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) (hA : VG.Proof.MlDsa.Arm.Sign.ArgsIn [.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)] s s1)
    (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) :
    AbsorbArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200)
      (s.gpr src.1 + BitVec.ofNat 32 src.2) rate pos len := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  obtain ⟨is, _, l0, d0, d1⟩ := VG.Proof.MlDsa.Arm.Sign.kabsChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn6 hA
  have hl : len < 2 ^ 32 := L.lenlt is
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have as : State.addr (s.gpr src.1 + BitVec.ofNat 32 src.2) = VG.Proof.MlDsa.Arm.Sign.pa s src := L.pa32 is l0
  refine ⟨e1, e2, e3, e4, e5, e6, hrate, hpos, hl, by rw [k.sp]; have := L.sp; omega,
    L.fit (p := sc 0) i0 (by decide), L.fit is l0, L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.MlKem.Arm.regA, a0, a1]; exact L.disj d01
  · simp only [VG.Proof.MlKem.Arm.regA, a0, as]; exact L.disj d0
  · simp only [VG.Proof.MlKem.Arm.regA, a1, as]; exact L.disj d1
  · simp only [VG.Proof.MlKem.Arm.regA, a0]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD i0 k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, a1]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD i1 k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, as]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD is k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, a0, a1]; rw [k.wr]; exact Covers.cons (L.cW w0) (L.cW w1)
  · simp only [VG.Proof.MlKem.Arm.regA, as]; rw [k.rd, k.wr]; exact L.cR is

theorem kabs_ok {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    WP isa (kabs src len rate pos) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      ∀ msg, Repr s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) rate msg → pos = msg.length % rate →
        Repr s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) rate (msg ++ bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s src) len) := by
  obtain ⟨w0, w1, i0, i1, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  obtain ⟨is, b1, l0, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.kabsChk_spec hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.setArgs_ok _ (VG.Proof.MlDsa.Arm.Sign.kabsOk b1) s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have as : State.addr (s.gpr src.1 + BitVec.ofNat 32 src.2) = VG.Proof.MlDsa.Arm.Sign.pa s src := L.pa32 is l0
  refine absorb_ok (VG.Proof.MlDsa.Arm.Sign.kabsArgs L hD hk hc hrate hpos hA k) fun s' hkept hR _ => ?_
  simp only [VG.Proof.MlKem.Arm.regA, a0, a1] at hkept
  obtain ⟨hP, hcs⟩ := VG.Proof.MlDsa.Arm.Sign.postB_kept (W := [VG.Proof.MlDsa.Arm.Sign.toR s (sc 0, 200), VG.Proof.MlDsa.Arm.Sign.toR s (sc 200, 640)]) hD k
    (rs := [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc 0), 200⟩, ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, fun msg hmsg hpos' => ?_⟩
  rw [k.mem, a0, as] at hR
  exact hR msg hmsg hpos'

theorem kabs_tr (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true) {src : Ptr} {len rate pos : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (kabs src len rate pos) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  obtain ⟨is, b1, _, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.kabsChk_spec hc
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.setArgs_rel (VG.Proof.MlDsa.Arm.Sign.kabsOk b1)) (absorb_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, _, VG.Proof.MlDsa.Arm.Sign.kabsArgs R.lx hD hk hc hrate hpos hAx kx, ?_⟩
  rw [R.eq i0, R.eq is]
  exact VG.Proof.MlDsa.Arm.Sign.kabsArgs R.ly hD hk hc hrate hpos hAy ky

/-! ## Padding -/

theorem kpadOk {rate pos suffix : Nat} :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok]

/-- The moves of `pad`'s arguments. -/
theorem kpadMoves_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr] as)) s fun s1 =>
      (∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip as, s1.gpr da.1 = da.2.val s) ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 :=
  WP.mono (VG.Proof.MlDsa.Arm.Sign.setArgsTo_ok _ as (by decide) (by decide) ha s) fun _ ⟨h, k⟩ => ⟨h, k.mono (by decide)⟩

theorem kpadArgs {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate)
    (hA : ∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
      s1.gpr da.1 = da.2.val s)
    (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) :
    PadArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200) rate pos (BitVec.ofNat 32 suffix) := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  refine ⟨hA (.r0, .ptr (sc 0)) (by simp), hA (.r1, .imm rate) (by simp), hA (.r2, .imm pos) (by simp),
    hA (.r3, .imm suffix) (by simp), hA (.lr, .ptr (sc 200)) (by simp), hrate, hpos, by rw [k.sp]; have := L.sp; omega,
    L.fit (p := sc 0) i0 (by decide), L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.MlKem.Arm.regA, a0, a1]; exact L.disj d01
  · simp only [VG.Proof.MlKem.Arm.regA, a0]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD i0 k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, a1]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD i1 k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, a0, a1]; rw [k.wr]; exact Covers.cons (L.cW w0) (L.cW w1)

theorem b8_ofNat32 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 32 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem kpad_ok {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    WP isa (kpad rate pos suffix) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      ∀ msg, Repr s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  obtain ⟨w0, w1, i0, i1, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.kpadMoves_ok _ VG.Proof.MlDsa.Arm.Sign.kpadOk s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  refine pad_ok (VG.Proof.MlDsa.Arm.Sign.kpadArgs L hD hk hrate hpos hA k) fun s' hkept hR => ?_
  simp only [VG.Proof.MlKem.Arm.regA, a0, a1] at hkept
  obtain ⟨hP, hcs⟩ := VG.Proof.MlDsa.Arm.Sign.postB_kept (W := [VG.Proof.MlDsa.Arm.Sign.toR s (sc 0, 200), VG.Proof.MlDsa.Arm.Sign.toR s (sc 200, 640)]) hD k
    (rs := [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc 0), 200⟩, ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, fun msg hmsg hpos' => ?_⟩
  rw [k.mem, a0] at hR
  rw [hR msg hmsg hpos', VG.Proof.MlDsa.Arm.Sign.b8_ofNat32 hs]

theorem kpad_tr (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true) {rate pos suffix : Nat} (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (kpad rate pos suffix) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  have hm : RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr]
      [.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)])) fun x1 y1 => ∃ x y, VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧
      ((∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
        x1.gpr da.1 = da.2.val x) ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1) ∧
      ((∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
        y1.gpr da.1 = da.2.val y) ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs y y1) :=
    RelCT.mono (RelCT.wpDep (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr (VG.Proof.MlDsa.Arm.Sign.setArgsTo_nomem _ _))
      (fun x y _ => ⟨VG.Proof.MlDsa.Arm.Sign.kpadMoves_ok _ VG.Proof.MlDsa.Arm.Sign.kpadOk x, VG.Proof.MlDsa.Arm.Sign.kpadMoves_ok _ VG.Proof.MlDsa.Arm.Sign.kpadOk y⟩)) (fun _ _ h => h)
      fun _ _ ⟨_, x, y, hp, h1, h2⟩ => ⟨x, y, hp, h1, h2⟩
  refine RelCT.seq hm (pad_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, VG.Proof.MlDsa.Arm.Sign.kpadArgs R.lx hD hk hrate hpos hAx kx, ?_⟩
  rw [R.eq i0]
  exact VG.Proof.MlDsa.Arm.Sign.kpadArgs R.ly hD hk hrate hpos hAy ky

/-! ## Squeezing -/

theorem ksqzOk {dst : Ptr} {len rate : Nat} (b1 : dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem ksqzArgs {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates)
    (hA : VG.Proof.MlDsa.Arm.Sign.ArgsIn [.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)] s s1)
    (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) :
    SqueezeArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200)
      (s.gpr dst.1 + BitVec.ofNat 32 dst.2) rate 0 len := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  obtain ⟨wd, id, _, l0, d0, d1⟩ := VG.Proof.MlDsa.Arm.Sign.ksqzChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn6 hA
  have hl : len < 2 ^ 32 := L.lenlt id
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have ad : State.addr (s.gpr dst.1 + BitVec.ofNat 32 dst.2) = VG.Proof.MlDsa.Arm.Sign.pa s dst := L.pa32 id l0
  refine ⟨e1, e2, e3, e4, e5, e6, hrate, Nat.zero_le _, hl, by rw [k.sp]; have := L.sp; omega,
    L.fit (p := sc 0) i0 (by decide), L.fit id l0, L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.MlKem.Arm.regA, a0, ad]; exact L.disj d0
  · simp only [VG.Proof.MlKem.Arm.regA, a0, a1]; exact L.disj d01
  · simp only [VG.Proof.MlKem.Arm.regA, a1, ad]; exact L.disj d1
  · simp only [VG.Proof.MlKem.Arm.regA, a0]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD i0 k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, ad]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD id k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, a1]; exact VG.Proof.MlDsa.Arm.Sign.k8 L hD i1 k.sp
  · simp only [VG.Proof.MlKem.Arm.regA, a0, a1, ad]; rw [k.wr]; exact Covers.cons (L.cW w0) (Covers.cons (L.cW wd) (L.cW w1))

theorem ksqz_ok {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    WP isa (ksqz rate dst len) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc 0, 200), (dst, len), (sc 200, 640)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s dst) len = squeezeFrom rate (stateAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0))) 0 len := by
  obtain ⟨w0, w1, i0, i1, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  obtain ⟨wd, id, b1, l0, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.ksqzChk_spec hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.setArgs_ok _ (VG.Proof.MlDsa.Arm.Sign.ksqzOk b1) s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have ad : State.addr (s.gpr dst.1 + BitVec.ofNat 32 dst.2) = VG.Proof.MlDsa.Arm.Sign.pa s dst := L.pa32 id l0
  refine squeeze_ok (VG.Proof.MlDsa.Arm.Sign.ksqzArgs L hD hk hc hrate hA k) fun s' hkept ho _ _ => ?_
  simp only [VG.Proof.MlKem.Arm.regA, a0, a1, ad] at hkept
  obtain ⟨hP, hcs⟩ := VG.Proof.MlDsa.Arm.Sign.postB_kept (W := [VG.Proof.MlDsa.Arm.Sign.toR s (sc 0, 200), VG.Proof.MlDsa.Arm.Sign.toR s (dst, len), VG.Proof.MlDsa.Arm.Sign.toR s (sc 200, 640)]) hD k
    (rs := [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc 0), 200⟩, ⟨VG.Proof.MlDsa.Arm.Sign.pa s dst, len⟩, ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, ?_⟩
  rw [ad, a0, k.mem] at ho
  exact ho

theorem ksqz_tr (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true) {dst : Ptr} {len rate : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (ksqz rate dst len) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.kChk_spec hk
  obtain ⟨_, id, b1, _, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.ksqzChk_spec hc
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.setArgs_rel (VG.Proof.MlDsa.Arm.Sign.ksqzOk b1)) (squeeze_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, _, VG.Proof.MlDsa.Arm.Sign.ksqzArgs R.lx hD hk hc hrate hAx kx, ?_⟩
  rw [R.eq i0, R.eq id]
  exact VG.Proof.MlDsa.Arm.Sign.ksqzArgs R.ly hD hk hc hrate hAy ky

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Hash`. -/
section

/-!
# ML-DSA signing on ARMv7: `H` of pieces of memory

`shakeAt ps out len` zeroes the Keccak state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: `H` of their concatenation (`shake_ok`),
leaking only the addresses (`shake_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : Spec.Sha3.State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d) = SHAKE256(s, 8d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (m : List Byte) (d : Nat) : VG.Spec.MlDsa.H m d = squeezeFrom 136 (VG.Proof.MlDsa.Arm.Sign.padded 136 (BitVec.ofNat 8 0x1f) m) 0 d := by
  rw [VG.Proof.MlDsa.Arm.Sign.squeezeFrom_zero]; rfl

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs : List (Reg × Nat)) (p : Ptr × Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.kabsChk bs p.1 p.2 && decide (p.1.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (Ptr × Nat)) : (VG.Proof.MlDsa.Arm.Sign.pieces s ps).length = totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [VG.Proof.MlDsa.Arm.Sign.pieces, List.flatMap_cons, List.length_append, VG.Proof.MlKem.bytesAt_length] at ih ⊢
    rw [ih]; simp [totLen]

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem pieceChk_keep {p : Ptr × Nat} (h : VG.Proof.MlDsa.Arm.Sign.pieceChk (rbs ++ wbs) p = true) :
    VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) [(sc 0, 200), (sc 200, 640)] p.1 p.2 = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.pieceChk, VG.Proof.MlDsa.Arm.Sign.kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hin, _⟩, _⟩, s1⟩, s2⟩, hcs⟩ := h
  simp only [VG.Proof.MlDsa.Arm.Sign.keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

theorem pieces_keep {s s' : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) :
    ∀ {ps : List (Ptr × Nat)}, (∀ p ∈ ps, VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws p.1 p.2 = true) → VG.Proof.MlDsa.Arm.Sign.pieces s' ps = VG.Proof.MlDsa.Arm.Sign.pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [VG.Proof.MlDsa.Arm.Sign.pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (VG.Proof.MlDsa.Arm.Sign.pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hcs_trans {s s₁ s₂ : State} (h₁ : VG.Proof.MlDsa.Arm.Sign.CS s s₁) (h₂ : VG.Proof.MlDsa.Arm.Sign.CS s₁ s₂) : VG.Proof.MlDsa.Arm.Sign.CS s s₂ := CS.trans h₁ h₂

theorem bases_all : ∀ w ∈ [((sc 0 : Ptr), 200), ((sc 200 : Ptr), 640)], w.1.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  decide

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (D : Nat) (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (Ptr × Nat)) : Prop :=
  ∀ (s : State) (_ : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (VG.Proof.MlDsa.Arm.Sign.pieceChk (rbs ++ wbs)) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) rate msg →
    WP isa (absAll rate ps pos) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧
      VG.Proof.MlDsa.Arm.Sign.CS s s' ∧ Repr s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc 0)) rate (msg ++ VG.Proof.MlDsa.Arm.Sign.pieces s ps)

theorem absAll_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) : ∀ (ps : List (Ptr × Nat)), VG.Proof.MlDsa.Arm.Sign.AbsOk D rbs wbs rate ps
  | [] => fun _ _ _ _ _ _ _ hR => WP.block_nil ⟨PostB.refl _ _ _, fun _ _ _ => rfl, by simpa using hR⟩
  | (p, l) :: ps => by
    intro s L pos msg hps hpos hm hR
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : VG.Proof.MlDsa.Arm.Sign.kabsChk (rbs ++ wbs) p l = true := by
      simp only [VG.Proof.MlDsa.Arm.Sign.pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.kabs_ok L hD hk hkc hrate hpos) fun s₁ ⟨hP₁, hc₁, hR₁⟩ => ?_)
    have L₁ := L.post hP₁ hcs
    have e0 : VG.Proof.MlDsa.Arm.Sign.pa s₁ (sc 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := hP₁.pa (by decide)
    have hR₁' := hR₁ msg hR hm
    rw [← e0] at hR₁'
    have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) l).length % rate := by
      rw [List.length_append, VG.Proof.MlKem.bytesAt_length, hm, Nat.mod_add_mod]
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.absAll_ok hcs hD hk hrate ps s₁ L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) l) hps.2
      (Nat.mod_lt _ hr0) h3 hR₁') fun s₂ ⟨hP₂, hc₂, hR₂⟩ =>
        ⟨PPostB.trans hP₁ hP₂ VG.Proof.MlDsa.Arm.Sign.bases_all (fun w hw => hw) (fun w hw => hw), VG.Proof.MlDsa.Arm.Sign.hcs_trans hc₁ hc₂, ?_⟩
    rw [e0, VG.Proof.MlDsa.Arm.Sign.pieces_keep L hP₁ fun q hq => VG.Proof.MlDsa.Arm.Sign.pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
    simpa only [VG.Proof.MlDsa.Arm.Sign.pieces, List.flatMap_cons, List.append_assoc] using hR₂

/-- The output: `len` bytes to `out`. -/
def shakeChk (bs wbs : List (Reg × Nat)) (ps : List (Ptr × Nat)) (out : Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.kChk bs wbs && ps.all (VG.Proof.MlDsa.Arm.Sign.pieceChk bs) && VG.Proof.MlDsa.Arm.Sign.ksqzChk bs wbs out len

theorem shakeChk_spec {bs wbs : List (Reg × Nat)} {ps : List (Ptr × Nat)} {out : Ptr} {len : Nat}
    (h : VG.Proof.MlDsa.Arm.Sign.shakeChk bs wbs ps out len = true) :
    VG.Proof.MlDsa.Arm.Sign.kChk bs wbs = true ∧ ps.all (VG.Proof.MlDsa.Arm.Sign.pieceChk bs) = true ∧ VG.Proof.MlDsa.Arm.Sign.ksqzChk bs wbs out len = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.shakeChk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem shake_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hD : 8 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.shakeChk (rbs ++ wbs) wbs ps out len = true) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) :
    WP isa (shakeAt ps out len) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      VG.Proof.MlDsa.Arm.Sign.CS s s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s out) len = VG.Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Sign.pieces s ps) len := by
  obtain ⟨hk, hps, hsq⟩ := VG.Proof.MlDsa.Arm.Sign.shakeChk_spec hc
  have hocs : out.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := (VG.Proof.MlDsa.Arm.Sign.ksqzChk_spec hsq).2.2.1
  have hrate : (136 : Nat) ∈ rates := by decide
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.kzero_ok L hk) fun s₁ ⟨hP₁, hc₁, hz⟩ => ?_)
  have L₁ := L.post hP₁ hcs
  have e1 : VG.Proof.MlDsa.Arm.Sign.pa s₁ (sc 0) = VG.Proof.MlDsa.Arm.Sign.pa s (sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) [(sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := VG.Proof.MlDsa.Arm.Sign.pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [VG.Proof.MlDsa.Arm.Sign.keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : VG.Proof.MlDsa.Arm.Sign.pieces s₁ ps = VG.Proof.MlDsa.Arm.Sign.pieces s ps := VG.Proof.MlDsa.Arm.Sign.pieces_keep L hP₁ hpk
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.absAll_ok hcs hD hk hrate ps s₁ L₁ 0 [] hps (by decide) rfl
    (by rw [e1]; exact VG.Proof.MlDsa.Arm.Sign.repr_nil hz)) fun s₂ ⟨hP₂, hc₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂ hcs
  have e2 : VG.Proof.MlDsa.Arm.Sign.pa s₂ (sc 0) = VG.Proof.MlDsa.Arm.Sign.pa s₁ (sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.kpad_ok L₂ hD hk hrate (pos := totLen ps % 136) (Nat.mod_lt _ (by decide))
    (show 0x1f < 256 by decide)) fun s₃ ⟨hP₃, hc₃, hS₃⟩ => ?_)
  have L₃ := L₂.post hP₃ hcs
  have e3 : VG.Proof.MlDsa.Arm.Sign.pa s₃ (sc 0) = VG.Proof.MlDsa.Arm.Sign.pa s₂ (sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (VG.Proof.MlDsa.Arm.Sign.pieces s ps) (by rw [e2]; exact hR₂) (by rw [VG.Proof.MlDsa.Arm.Sign.pieces_length])
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.ksqz_ok L₃ hD hk hsq hrate) fun s₄ ⟨hP₄, hc₄, ho⟩ => ?_
  have eo : VG.Proof.MlDsa.Arm.Sign.pa s₃ out = VG.Proof.MlDsa.Arm.Sign.pa s out := by rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  have h12 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s₂ [(sc 0, 200), (sc 200, 640)] :=
    PPostB.trans hP₁ hP₂ VG.Proof.MlDsa.Arm.Sign.bases_all (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..)
      (fun w hw => hw)
  have h123 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s₃ [(sc 0, 200), (sc 200, 640)] := PPostB.trans h12 hP₃ VG.Proof.MlDsa.Arm.Sign.bases_all (fun w hw => hw) (fun w hw => hw)
  have hcs4 : ∀ w ∈ [((sc 0 : Ptr), 200), (out, len), ((sc 200 : Ptr), 640)], w.1.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    exacts [by decide, hocs, by decide]
  refine ⟨PPostB.trans h123 hP₄ hcs4 (fun w hw => ?_) (fun w hw => ?_),
    VG.Proof.MlDsa.Arm.Sign.hcs_trans (VG.Proof.MlDsa.Arm.Sign.hcs_trans (VG.Proof.MlDsa.Arm.Sign.hcs_trans hc₁ hc₂) hc₃) hc₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h <;> simp [h]
  rw [← eo, ho, e3, hS, VG.Proof.MlDsa.Arm.Sign.H_eq]

/-! ## Constant time -/

theorem LRel.step (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) {c : Prog isa}
    (htr : RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) c fun _ _ => True)
    (hok : ∀ x, VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs x → WP isa c x fun x' => ∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x x' W) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) c (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) :=
  VG.Proof.MlDsa.Arm.Sign.postDep htr (F := fun x x' => ∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  VG.Proof.MlDsa.Arm.Sign.postDep (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr fun _ hi => absurd hi List.not_mem_nil)
    (F := fun x x' => x' = x) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem absAll_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hD : 8 ≤ D) (hk : VG.Proof.MlDsa.Arm.Sign.kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) :
    ∀ (ps : List (Ptr × Nat)) (pos : Nat), ps.all (VG.Proof.MlDsa.Arm.Sign.pieceChk (rbs ++ wbs)) = true → pos < rate →
      RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (absAll rate ps pos) (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs)
  | [], _, _, _ => VG.Proof.MlDsa.Arm.Sign.nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : VG.Proof.MlDsa.Arm.Sign.kabsChk (rbs ++ wbs) p l = true := by
      simp only [VG.Proof.MlDsa.Arm.Sign.pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    exact RelCT.seq (LRel.step hcs (VG.Proof.MlDsa.Arm.Sign.kabs_tr hD hk hkc hrate hpos)
      fun x Lx => WP.mono (VG.Proof.MlDsa.Arm.Sign.kabs_ok Lx hD hk hkc hrate hpos) fun _ h => ⟨_, h.1⟩)
      (VG.Proof.MlDsa.Arm.Sign.absAll_tr hcs hD hk hrate ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem shake_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hD : 8 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.shakeChk (rbs ++ wbs) wbs ps out len = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (shakeAt ps out len) (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) := by
  obtain ⟨hk, hps, hsq⟩ := VG.Proof.MlDsa.Arm.Sign.shakeChk_spec hc
  have hrate : (136 : Nat) ∈ rates := by decide
  have i0 : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) (sc 0) 200 = true := (VG.Proof.MlDsa.Arm.Sign.kChk_spec hk).2.2.1
  refine RelCT.seq (LRel.step hcs (VG.Proof.MlDsa.Arm.Sign.kzero_tr fun x y h => h.eq i0)
    fun x Lx => WP.mono (VG.Proof.MlDsa.Arm.Sign.kzero_ok Lx hk) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (VG.Proof.MlDsa.Arm.Sign.absAll_tr hcs hD hk hrate ps 0 hps (by decide)) (RelCT.seq (LRel.step hcs
      (VG.Proof.MlDsa.Arm.Sign.kpad_tr hD hk hrate (Nat.mod_lt _ (by decide)))
      fun x Lx => WP.mono (VG.Proof.MlDsa.Arm.Sign.kpad_ok Lx hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
        fun _ h => ⟨_, h.1⟩)
      (LRel.step hcs (VG.Proof.MlDsa.Arm.Sign.ksqz_tr hD hk hsq hrate) fun x Lx => WP.mono (VG.Proof.MlDsa.Arm.Sign.ksqz_ok Lx hD hk hsq hrate) fun _ h => ⟨_, h.1⟩)))

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top`. -/
section

/-!
# ML-DSA signing on ARMv7: the function's contract, layout, entry and exit

As on x86-64: the contract the proof is written against (`signK`, which the
shared contract implies), the layout of the function's buffers (`sk`, `mu`,
`rnd` read, in `r4`, `r5`, `r6`; `scratch` and `sig` written, in `r7` and
`r8`), what holds of the state throughout (`Top`: the permissions and the
stack pointer of entry, the pointers in their registers, and the caller's
`r4`–`r11` and `lr` saved in `scratch`), the prologue (`pro_ok`), the return
(`topEnd_ok`), branches on `r11` (`ifOkElse_ok`, `ifOkElse_tr`) and sequences
of pieces indexed by a number (`seqR_ok`, `seqR_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (Saved SaveInv RestoreInv saveRegs_ok restoreRegs_ok)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_sign(sk = r0, mu = r1, rnd = r2, sig = r3, scratch = [sp]) -> r0`, with
`D` bytes of stack, and the leakage `signLeakT`. -/
def signK (p : Params) (D : Nat) : Contract isa where
  pre s :=
    let sk : Region := ⟨State.addr (s.gpr .r0), p.skLen⟩
    let mu : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let rnd : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r3), p.sigLen⟩
    let scr : Region := ⟨State.addr (stackArg s 0), VG.Proof.MlDsa.Arm.Sign.scrLen p⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sk, mu, rnd, args] ∧ s.wr = [sig, scr] ∧
    sk.Disjoint sig ∧ sk.Disjoint scr ∧ mu.Disjoint sig ∧ mu.Disjoint scr ∧ rnd.Disjoint sig ∧
    rnd.Disjoint scr ∧ sig.Disjoint scr ∧ sig.Disjoint args ∧ scr.Disjoint args ∧
    (belowA s.sp D).Disjoint sk ∧ (belowA s.sp D).Disjoint mu ∧ (belowA s.sp D).Disjoint rnd ∧
    (belowA s.sp D).Disjoint sig ∧ (belowA s.sp D).Disjoint scr ∧
    (s.gpr .r0).toNat + p.skLen ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + VG.Proof.MlDsa.Arm.Sign.scrLen p ≤ 2 ^ 32 ∧ D ≤ s.sp.toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen)
      (bytesAt s.mem (State.addr (s.gpr .r1)) 64) (bytesAt s.mem (State.addr (s.gpr .r2)) 32)) (s'.gpr .r0)
      (bytesAt s'.mem (State.addr (s.gpr .r3)) p.sigLen)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ s₁.sp = s₂.sp ∧
    signLeakT p (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.skLen) (bytesAt s₁.mem (State.addr (s₁.gpr .r1)) 64)
        (bytesAt s₁.mem (State.addr (s₁.gpr .r2)) 32) =
      signLeakT p (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.skLen) (bytesAt s₂.mem (State.addr (s₂.gpr .r1)) 64)
        (bytesAt s₂.mem (State.addr (s₂.gpr .r2)) 32)

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.r4, p.skLen), (.r5, 64), (.r6, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.r7, VG.Proof.MlDsa.Arm.Sign.scrLen p), (.r8, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := VG.Proof.MlDsa.Arm.Sign.sgR p ++ VG.Proof.MlDsa.Arm.Sign.sgW p

/-- The pointer the function keeps in each register of `bases`, from its entry state. -/
def ptrOf (σ : State) : Reg → BitVec 32
  | .r7 => stackArg σ 0
  | .r4 => σ.gpr .r0
  | .r5 => σ.gpr .r1
  | .r6 => σ.gpr .r2
  | _ => σ.gpr .r3

theorem sgB_bases (p : Params) : ∀ b ∈ VG.Proof.MlDsa.Arm.Sign.sgB p, b.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  intro b hb; simp only [VG.Proof.MlDsa.Arm.Sign.sgB, VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  regs : ∀ r ∈ VG.Proof.MlDsa.Arm.Sign.bases, s.gpr r = VG.Proof.MlDsa.Arm.Sign.ptrOf σ r
  saved : VG.Proof.MlKem.Arm.Saved s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oSV)) σ.gpr
  savlr : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oSV + 32))) 32 = σ.gpr .lr

section
variable {p : Params} {D : Nat} {σ : State} (hp : (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ)
include hp

theorem sgLay (hsz : VG.Proof.MlDsa.Arm.Sign.scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.Top σ s) : VG.Proof.MlDsa.Arm.Sign.Lay D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, -, -, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp
  have e7 : s.gpr .r7 = stackArg σ 0 := h.regs .r7 (by decide)
  have e4 : s.gpr .r4 = σ.gpr .r0 := h.regs .r4 (by decide)
  have e5 : s.gpr .r5 = σ.gpr .r1 := h.regs .r5 (by decide)
  have e6 : s.gpr .r6 = σ.gpr .r2 := h.regs .r6 (by decide)
  have e8 : s.gpr .r8 = σ.gpr .r3 := h.regs .r8 (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    by rw [h.sp]; exact hsp⟩
  · intro b hb
    simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlDsa.Arm.Sign.wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e4, e5, e6, e7, e8]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8, h.sp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8]
    exacts [n1, n2, n3, n5, n4]
  · simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8]
    · exact mem ⟨State.addr (σ.gpr .r0), p.skLen⟩ (List.mem_append_left _ (hrd ▸ List.mem_cons_self ..))
    · exact mem ⟨State.addr (σ.gpr .r1), 64⟩
        (List.mem_append_left _ (hrd ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact mem ⟨State.addr (σ.gpr .r2), 32⟩
        (List.mem_append_left _ (hrd ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    · exact mem ⟨State.addr (stackArg σ 0), VG.Proof.MlDsa.Arm.Sign.scrLen p⟩
        (List.mem_append_right _ (hwr ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact mem ⟨State.addr (σ.gpr .r3), p.sigLen⟩ (List.mem_append_right _ (hwr ▸ List.mem_cons_self ..))
  · simp only [VG.Proof.MlDsa.Arm.Sign.sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e7, e8]
    · exact memw ⟨State.addr (stackArg σ 0), VG.Proof.MlDsa.Arm.Sign.scrLen p⟩ (hwr ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact memw ⟨State.addr (σ.gpr .r3), p.sigLen⟩ (hwr ▸ List.mem_cons_self ..)

end

theorem pa_add (s : State) (r : Reg) (a b : Nat) : VG.Proof.MlDsa.Arm.Sign.pa s (r, a + b) = VG.Proof.MlDsa.Arm.Sign.pa s (r, a) + BitVec.ofNat 64 b := by
  simp only [VG.Proof.MlDsa.Arm.Sign.pa]; rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- The saved registers are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool := VG.Proof.MlDsa.Arm.Sign.keepB bs ws (sc oSV) 36

theorem Top.step {D : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : VG.Proof.MlDsa.Arm.Sign.Top σ s)
    (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws)
    (hc : VG.Proof.MlDsa.Arm.Sign.topChk (rbs ++ wbs) ws = true) : VG.Proof.MlDsa.Arm.Sign.Top σ s' := by
  have hs : ∀ k < 9, s'.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s' (sc (oSV + 4 * k))) 32 = s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oSV + 4 * k))) 32 :=
    fun k hk => L.keepW hP (VG.Proof.MlDsa.Arm.Sign.keepB_sub hc (by simp [oSV]) (by simp [oSV]; omega))
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp,
    fun r hr => (hP.bs _ hr).trans (h.regs r hr), fun i hi => ?_, ?_⟩
  · have e := hs i (by omega)
    rw [VG.Proof.MlDsa.Arm.Sign.pa_add, VG.Proof.MlDsa.Arm.Sign.pa_add] at e
    rw [e]; exact h.saved i hi
  · have e := hs 8 (by omega)
    rw [e]; exact h.savlr

/-! ## The prologue -/

theorem pro_eq : VG.Impl.MlDsa.Arm.Sign.pro = ([.ldrSp .r12 0] : List Instr) ++ Impl.MlKem.Arm.saveRegs .r12 oSV ++
    ([.str .lr .r12 (oSV + 32), .mov .r7 (.reg .r12), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r6 (.reg .r2), .mov .r8 (.reg .r3), .mov .r11 (.imm 1)] : List Instr) := rfl

theorem scrLen_ge (p : Params) : 5120 ≤ VG.Proof.MlDsa.Arm.Sign.scrLen p := by
  unfold VG.Proof.MlDsa.Arm.Sign.scrLen scratchWords; omega

theorem pro_ok {p : Params} {D : Nat} {σ : State} (hp : (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ) :
    WP isa (.block VG.Impl.MlDsa.Arm.Sign.pro) σ fun s => VG.Proof.MlDsa.Arm.Sign.Top σ s ∧ Frame [⟨State.addr (stackArg σ 0), VG.Proof.MlDsa.Arm.Sign.scrLen p⟩] σ.mem s.mem ∧
      s.gpr .r11 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n5, -⟩ := hp'
  have hge := VG.Proof.MlDsa.Arm.Sign.scrLen_ge p
  have hS : (⟨State.addr (stackArg σ 0), VG.Proof.MlDsa.Arm.Sign.scrLen p⟩ : Region) ∈ σ.wr := by rw [hwr]; simp
  have hA : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), by simp [stackArgAddr, Region.Contains]⟩
  rw [VG.Proof.MlDsa.Arm.Sign.pro_eq, List.append_assoc, WP.block_append_iff]
  have hl : WP isa (.block [.ldrSp .r12 0]) σ fun s₁ => s₁.gpr .r12 = stackArg σ 0 ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = σ.gpr r) ∧ s₁.mem = σ.mem ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr ∧ s₁.sp = σ.sp := by
    run_block [hA, show (0 : Nat) < 4096 by decide]
    exact ⟨by simp [stackArg, stackArgAddr], fun r hr => by simp [hr], trivial⟩
  refine WP.mono hl fun s₁ ⟨h12, hr, hm, hrd₁, hwr₁, hsp₁⟩ => ?_
  rw [WP.block_append_iff]
  have wS : ∀ o n, o + n ≤ VG.Proof.MlDsa.Arm.Sign.scrLen p → InRegions s₁.wr (State.addr (stackArg σ 0) + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr₁]; exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub ⟨_, hS, Region.contains_self _ _⟩ h (by omega)
  refine WP.mono (saveRegs_ok .r12 (off := 840) (by decide) (by rw [h12]; omega) fun i hi => by
    rw [h12, BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS _ _ (by omega)) fun s₂ h₂ => ?_
  have g12 : s₂.gpr .r12 = stackArg σ 0 := by rw [h₂.gpr, h12]
  have e872 : State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSV + 32)) =
      State.addr (stackArg σ 0) + BitVec.ofNat 64 872 := by
    rw [g12]; exact addr_add (by simp only [oSV]; omega)
  have i872 : InRegions s₂.wr (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSV + 32))) 4 := by
    rw [e872, h₂.wr]; exact wS _ _ (by omega)
  have o1 : oSV + 32 < 4096 := by decide
  run_block [i872, o1]
  have g : ∀ r, r ≠ .r12 → s₂.gpr r = σ.gpr r := fun r hr' => by rw [h₂.gpr, hr r hr']
  have hne : ∀ i < 8, Impl.MlKem.Arm.savedRegs.getD i Reg.r4 ≠ Reg.r12 := by decide
  rw [e872]
  refine ⟨⟨by simp [h₂.rd, hrd₁], by simp [h₂.wr, hwr₁], by simp [h₂.sp, hsp₁], fun r hr => ?_, fun i hi => ?_, ?_⟩,
    ?_, trivial⟩
  · simp only [VG.Proof.MlDsa.Arm.Sign.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [VG.Proof.MlDsa.Arm.Sign.ptrOf, g12, g]
  · simp only [VG.Proof.MlDsa.Arm.Sign.pa, ite_true, ite_false, reduceCtorEq, g12]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Mem.readW_writeW_sep (Offset.sep _ (by simp only [oSV]; omega)
      (by omega) (by omega)) (by decide)]
    have := h₂.saved i hi
    rw [h12, BitVec.add_assoc, ← BitVec.ofNat_add] at this
    rw [show oSV = 840 from rfl, this, hr _ (hne i hi)]
  · simp only [VG.Proof.MlDsa.Arm.Sign.pa, ite_true, ite_false, reduceCtorEq, g12]
    rw [show oSV + 32 = 872 from rfl, Mem.readW_writeW_self32, g _ (by decide)]
  · have f₁ := h₂.frame
    rw [h12, hm] at f₁
    refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base _ (by omega)

/-! ## The return -/

theorem topEnd_ok {σ s : State} (h : VG.Proof.MlDsa.Arm.Sign.Top σ s) (hin : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.Arm.Sign.pa s (sc oSV)) 36)
    (hfit : (s.gpr .r7).toNat + 876 ≤ 2 ^ 32) :
    WP isa (.block Impl.MlKem.Arm.topEnd) s fun s' => s'.gpr .r0 = s.gpr .r11 ∧
      (∀ r ∈ preserved, s'.gpr r = σ.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  rw [Impl.MlKem.Arm.topEnd, List.append_assoc, WP.block_append_iff]
  have hk : WP isa (.block [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r11 ∧ s'.gpr .r3 = s.gpr .r7 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    run_block []
  refine WP.mono hk fun s₁ ⟨r0, r3, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have e3 : State.addr (s₁.gpr .r3) + BitVec.ofNat 64 840 = VG.Proof.MlDsa.Arm.Sign.pa s (sc oSV) := by rw [r3]; rfl
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 840) (by decide)
    (by rw [r3]; omega) (g := σ.gpr) (by rw [e3, m₁]; exact h.saved)
    fun i hi => by
      rw [e3, rd₁, wr₁]
      exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub hin (by omega) (by decide))
    fun s₂ h₂ => ?_
  have g3 : s₂.gpr .r3 = s.gpr .r7 := by rw [h₂.other .r3 (by decide), r3]
  have e872 : State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oSV + 32)) := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega)
  have i12 : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₂.rd, h₂.wr, rd₁, wr₁, VG.Proof.MlDsa.Arm.Sign.pa_add]
    exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub hin (by omega) (by decide)
  have ho : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have hl : WP isa (.block [.ldr .lr .r3 (Impl.MlKem.Arm.oSave + 32)]) s₂ fun s' =>
      s'.gpr .lr = s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 32 ∧
      (∀ r, r ≠ .lr → s'.gpr r = s₂.gpr r) ∧ s'.mem = s₂.mem ∧ s'.sp = s₂.sp := by
    run_block [i12, ho, and_self, and_true]
    exact ⟨trivial, fun r hr => by simp [hr]⟩
  refine WP.mono hl fun s' ⟨lr, rr, m, sp⟩ => ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · rw [rr .r0 (by decide), h₂.other .r0 (by decide), r0]
  · by_cases e : r = .lr
    · subst e
      rw [lr, e872, h₂.mem, m₁]; exact h.savlr
    · have hs : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, Impl.MlKem.Arm.savedRegs.getD i .r4 = r := by decide
      obtain ⟨i, hi, rfl⟩ := hs r hr e
      rw [rr _ e]; exact h₂.loaded i hi
  · rw [m, h₂.mem, m₁]
  · rw [sp, h₂.sp, sp₁]

/-! ## Branches on `r11` -/

/-- The comparison of `r11` with 0 writes only the flags. -/
theorem cmp11_ok (s : State) (D : Nat) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun s₁ => VG.Proof.MlDsa.Arm.Sign.PPostB D s s₁ [] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s₁ ∧ s₁.mem = s.mem ∧
      s₁.z = (s.gpr .r11 == 0) := by
  have h : WP isa (.block [.cmp .r11 (.imm 0)]) s fun s₁ => s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r11 == 0) := by
    run_block []
    simp
  refine WP.mono h fun s₁ ⟨g, m, rd, wr, sp, z⟩ => ?_
  have hcs : VG.Proof.MlDsa.Arm.Sign.CS s s₁ := fun r _ _ => by rw [g]
  exact ⟨PostB.of_cs hcs rd wr sp (by rw [m]; exact Frame.refl _ _), hcs, m, z⟩

theorem ifOkElse_ok {D : Nat} {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, VG.Proof.MlDsa.Arm.Sign.PPostB D s s₁ [] → VG.Proof.MlDsa.Arm.Sign.CS s s₁ → s₁.mem = s.mem → s.gpr .r11 ≠ 0 → WP isa t s₁ Q)
    (he : ∀ s₁, VG.Proof.MlDsa.Arm.Sign.PPostB D s s₁ [] → VG.Proof.MlDsa.Arm.Sign.CS s s₁ → s₁.mem = s.mem → s.gpr .r11 = 0 → WP isa e s₁ Q) :
    WP isa (ifOkElse t e) s Q := by
  unfold ifOkElse
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.cmp11_ok s D) fun s₁ ⟨hP, hcs, hm, hz⟩ => ?_)
  refine WP.ite (M := isa) (!(s.gpr .r11 == 0)) (show some (!s₁.z) = _ by rw [hz]) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP hcs hm (by simpa using hb)
  · exact he s₁ hP hcs hm (by simpa using hb)

theorem ifOkElse_tr {D : Nat} {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → x.gpr .r11 = y.gpr .r11)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (VG.Proof.MlDsa.Arm.Sign.PPostB D x₀ x [] ∧ VG.Proof.MlDsa.Arm.Sign.CS x₀ x ∧ x.mem = x₀.mem) ∧
      (VG.Proof.MlDsa.Arm.Sign.PPostB D y₀ y [] ∧ VG.Proof.MlDsa.Arm.Sign.CS y₀ y ∧ y.mem = y₀.mem) ∧ x₀.gpr .r11 ≠ 0) t Q)
    (he : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (VG.Proof.MlDsa.Arm.Sign.PPostB D x₀ x [] ∧ VG.Proof.MlDsa.Arm.Sign.CS x₀ x ∧ x.mem = x₀.mem) ∧
      (VG.Proof.MlDsa.Arm.Sign.PPostB D y₀ y [] ∧ VG.Proof.MlDsa.Arm.Sign.CS y₀ y ∧ y.mem = y₀.mem) ∧ x₀.gpr .r11 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q := by
  unfold ifOkElse
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.postDep (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => (VG.Proof.MlDsa.Arm.Sign.PPostB D x x₁ [] ∧ VG.Proof.MlDsa.Arm.Sign.CS x x₁ ∧ x₁.mem = x.mem) ∧ x₁.z = (x.gpr .r11 == 0))
    (fun x y _ => ⟨WP.mono (VG.Proof.MlDsa.Arm.Sign.cmp11_ok x D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
      WP.mono (VG.Proof.MlDsa.Arm.Sign.cmp11_ok y D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
    (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      ((VG.Proof.MlDsa.Arm.Sign.PPostB D x₀ x₁ [] ∧ VG.Proof.MlDsa.Arm.Sign.CS x₀ x₁ ∧ x₁.mem = x₀.mem) ∧ x₁.z = (x₀.gpr .r11 == 0)) ∧
      ((VG.Proof.MlDsa.Arm.Sign.PPostB D y₀ y₁ [] ∧ VG.Proof.MlDsa.Arm.Sign.CS y₀ y₁ ∧ y₁.mem = y₀.mem) ∧ y₁.z = (y₀.gpr .r11 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show some (!x₁.z) = some (!y₁.z)
    rw [hx, hy, hq x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : some (!x₁.z) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono he (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : some (!x₁.z) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact VG.Proof.MlDsa.Arm.Sign.seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => VG.Proof.MlDsa.Arm.Sign.nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (VG.Proof.MlDsa.Arm.Sign.seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks`. -/
section

/-!
# ML-DSA signing on ARMv7: the blocks between the calls

As on x86-64: what the function's own instructions do, in its layout: copies
(`copy_okB`, with ML-KEM's `copy_loop`), stores of a byte or of a word
(`setB_okB`, `setW_okB`), the AND of a result into `r11` (`and11_ok`), and the
counters in `scratch` (`addW_ok`, `decW_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Spec.MlDsa (integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- What a block that writes only registers other than the callee-saved
ones, and memory within `W`, leaves. -/
theorem postB_of_keep {D : Nat} {rs : List Reg} {s s' : State} (k : VG.Proof.MlDsa.Arm.Sign.Keep rs s s')
    (hcs : ∀ r ∈ preserved, r ≠ .lr → r ∉ rs) {W : List Region} (hf : Frame W s.mem s'.mem) :
    VG.Proof.MlDsa.Arm.Sign.PostB D s s' W ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' :=
  have c : VG.Proof.MlDsa.Arm.Sign.CS s s' := fun r hr hl => k.gpr r (hcs r hr hl)
  ⟨PostB.of_cs c k.rd k.wr k.sp hf, c⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
include L

/-! ## Copies -/

/-- What a copy of `n` bytes from `src` to `dst` needs of the layout. -/
def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs dst n && VG.Proof.MlDsa.Arm.Sign.inB bs src n && VG.Proof.MlDsa.Arm.Sign.sepB bs src n dst n && decide (0 < n) && decide (src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) &&
    decide (dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

omit L in
theorem copyChk_spec {bs wbs : List (Reg × Nat)} {dst src : Ptr} {n : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.copyChk bs wbs dst src n = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs dst n = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs src n = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs src n dst n = true ∧ 0 < n ∧ src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases ∧
      dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  simp only [VG.Proof.MlDsa.Arm.Sign.copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

omit L in
theorem copySetup_ok {dst src : Ptr} {n : Nat} (b1 : src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (s : State) :
    WP isa (.block (lea .r0 src ++ lea .r1 dst ++ movi .r2 n)) s fun s1 =>
      s1.gpr .r0 = s.gpr src.1 + BitVec.ofNat 32 src.2 ∧ s1.gpr .r1 = s.gpr dst.1 + BitVec.ofNat 32 dst.2 ∧
        s1.gpr .r2 = BitVec.ofNat 32 n ∧ VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1 := by
  have h := VG.Proof.MlDsa.Arm.Sign.setArgsTo_ok [.r0, .r1, .r2] [.ptr src, .ptr dst, .imm n] (by decide) (by decide)
    (by simp [Arg.ok, b1, b2]) s
  simp only [setArgsTo, List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Arg.mov] at h
  rw [List.append_assoc]
  refine WP.mono h fun s1 ⟨hA, k⟩ => ⟨hA (.r0, .ptr src) (by simp), hA (.r1, .ptr dst) (by simp), hA (.r2, .imm n) (by simp),
    k.mono (by decide)⟩

theorem copy_okB {dst src : Ptr} {n : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(dst, n)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s dst) n = bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s src) n := by
  obtain ⟨w, i, d, h0, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.copyChk_spec hc
  have id : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) dst n = true := (VG.Proof.MlDsa.Arm.Sign.sepB_spec d).2.1
  unfold copy
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.copySetup_ok b1 b2 s) fun s1 ⟨g0, g1, g2, k⟩ => ?_)
  have as := L.pa32 i h0
  have ad := L.pa32 id h0
  refine WP.mono (VG.Proof.MlKem.Arm.copy_loop (L.fit i h0) (L.fit id h0) (L.lenlt i) h0
    (by rw [as, ad]; exact L.disj d) (by rw [as, k.rd, k.wr]; exact L.cR i) (by rw [ad, k.wr]; exact L.cW w)
    g0 g1 g2) fun s' ⟨hcs, rd, wr, sp, hf, hb⟩ => ?_
  rw [ad] at hf
  rw [ad, as, k.mem] at hb
  rw [k.mem] at hf
  have c : VG.Proof.MlDsa.Arm.Sign.CS s s' := fun r hr hl => (hcs r hr).trans (k.cs r hr hl)
  exact ⟨PostB.of_cs c (rd.trans k.rd) (wr.trans k.wr) (sp.trans k.sp) hf, c, hb⟩

/-! ## Stores -/

omit L in
theorem encodable_small {v : Nat} (hv : v < 256) : encodable (BitVec.ofNat 32 v) = true := by
  unfold encodable; rw [List.any_eq_true]
  refine ⟨0, by simp, ?_⟩
  have : (BitVec.ofNat 32 v).rotateLeft 0 = BitVec.ofNat 32 v := by
    rw [BitVec.rotateLeft_def]; simp [BitVec.ushiftRight_eq_zero]
  rw [this]; simp; omega

omit L in
/-- What a store of the block through `r0` leaves. -/
theorem postB_store {s' : State} {p : Ptr} {l : Nat}
    (hg : ∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩] s.mem s'.mem) : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(p, l)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' :=
  have c : VG.Proof.MlDsa.Arm.Sign.CS s s' := fun r hr _ => hg r fun h => by subst h; exact absurd hr (by decide)
  ⟨PostB.of_cs c hrd hwr hsp hf, c⟩

theorem setB_okB {p : Ptr} {v : Nat} (hv : v < 256) (ho : p.2 < 4096) (hb : p.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)
    (hc : VG.Proof.MlDsa.Arm.Sign.inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(p, 1)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.Arm.Sign.pa s p) (BitVec.ofNat 8 v) := by
  have e := L.pa32W hc (by decide)
  have hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 1 := by rw [e]; exact L.iW hc
  have h0 : p.1 ≠ .r0 := fun h => by revert hb; rw [h]; decide
  have enc := VG.Proof.MlDsa.Arm.Sign.encodable_small hv
  have hr : WP isa (.block (setB p v)) s fun s' => s'.mem = s.mem.writeW (VG.Proof.MlDsa.Arm.Sign.pa s p) (BitVec.ofNat 8 v) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    unfold setB
    run_block [hw, ho, enc, h0]
    refine ⟨by rw [e]; congr 1; apply BitVec.eq_of_toNat_eq; simp, fun r hr => by simp [hr], trivial⟩
  refine WP.mono hr fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s p, 1⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg hrd hwr hsp hf).1, (VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg hrd hwr hsp hf).2, hm⟩

theorem setW_okB {p : Ptr} {v : Nat} (ho : p.2 < 4096) (hb : p.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (hc : VG.Proof.MlDsa.Arm.Sign.inB wbs p 4 = true) :
    WP isa (.block (setW p v)) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(p, 4)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.Arm.Sign.pa s p) (BitVec.ofNat 32 v) := by
  have e := L.pa32W hc (by decide)
  have hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4 := by rw [e]; exact L.iW hc
  have h0 : p.1 ≠ .r0 := fun h => by revert hb; rw [h]; decide
  have hr : WP isa (.block (setW p v)) s fun s' => s'.mem = s.mem.writeW (VG.Proof.MlDsa.Arm.Sign.pa s p) (BitVec.ofNat 32 v) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    unfold setW movi
    run_block [hw, ho, h0]
    refine ⟨by rw [e, VG.Proof.MlDsa.Arm.Sign.movi_val], fun r hr => by simp [hr], trivial⟩
  refine WP.mono hr fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s p, 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg hrd hwr hsp hf).1, (VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg hrd hwr hsp hf).2, hm⟩

end

/-! ## Results in `r11` -/

/-- A result (1 or 0) as a register. -/
abbrev bit (b : Prop) [Decidable b] : BitVec 32 := if b then 1 else 0

theorem and11_ok (s : State) :
    WP isa (.block [.dp .and .r11 .r11 (.reg .r0)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 &&& s.gpr .r0 ∧ VG.Proof.MlDsa.Arm.Sign.Keep [.r11] s s' := by
  run_block []
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x y : BitVec 32} (hx : x = VG.Proof.MlDsa.Arm.Sign.bit a)
    (hy : y = if b then 1 else 0) : x &&& y = VG.Proof.MlDsa.Arm.Sign.bit (a ∧ b) := by
  subst hx hy
  by_cases ha : a <;> by_cases hb : b <;> simp [VG.Proof.MlDsa.Arm.Sign.bit, ha, hb]

/-- A block that writes `r11` alone, and flags, leaves `PostB` but for `r11`. -/
theorem postB11 {D : Nat} {s s' : State} (k : VG.Proof.MlDsa.Arm.Sign.Keep [.r11] s s') (W : List Region) :
    VG.Proof.MlDsa.Arm.Sign.PostB D s s' W ∧ ∀ r ∈ preserved, r ≠ .lr → r ≠ .r11 → s'.gpr r = s.gpr r :=
  ⟨⟨k.rd, k.wr, fun r hr => k.gpr r (by revert hr; decide +revert), k.sp, by rw [k.mem]; exact Frame.refl _ _⟩,
    fun r _ _ hne => k.gpr r (by simpa using hne)⟩

/-! ## Counters -/

/-- A block writing registers `rs` and memory only. -/
def KeepM (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- `[p] ← [p] + v`, through `r0` (`v` encodable). -/
theorem addW_ok (p : Ptr) (v : Nat) (ho : p.2 < 4096) (h0 : p.1 ≠ .r0) (hv : encodable (BitVec.ofNat 32 v) = true)
    (s : State) (hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4) :
    WP isa (.block [.ldr .r0 p.1 p.2, .dp .add .r0 .r0 (.imm (BitVec.ofNat 32 v)), .str .r0 p.1 p.2]) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2))
        (s.mem.readW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 32 + BitVec.ofNat 32 v) ∧ VG.Proof.MlDsa.Arm.Sign.KeepM [.r0] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4 := Covers.right (Covers.one hw) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  run_block [hw, hr, ho, h0, hv]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

/-- `[p] ← [p] - 1`, through `r0`, and `Z` set when it is 0. -/
theorem decW_ok (p : Ptr) (ho : p.2 < 4096) (h0 : p.1 ≠ .r0) (s : State)
    (hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4) :
    WP isa (.block [.ldr .r0 p.1 p.2, .subs .r0 .r0 (.imm 1), .str .r0 p.1 p.2]) s fun s' =>
      (s'.mem = s.mem.writeW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2))
        (s.mem.readW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 32 - 1) ∧
        s'.z = (s.mem.readW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 32 - 1 == 0)) ∧ VG.Proof.MlDsa.Arm.Sign.KeepM [.r0] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4 := Covers.right (Covers.one hw) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  run_block [hw, hr, ho, h0]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.CopyTr`. -/
section

/-!
# ML-DSA signing on ARMv7: copies leak only their addresses

The setup of a copy accesses no memory, and its loop leaks only the pointers
and the count in `r0`–`r2` (by the taint analysis), so two runs of a copy
between the same addresses leak the same (`copy_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign

theorem copySetup_nomem (dst src : Ptr) (n : Nat) :
    ∀ i ∈ lea .r0 src ++ lea .r1 dst ++ movi .r2 n, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, movi, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Two runs of a copy from the same addresses leak the same. -/
theorem copy_tr {dst src : Ptr} {n : Nat} (b1 : src.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : dst.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr src.1 = y.gpr src.1) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  unfold copy
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ [Reg.r0, .r1, .r2], x.gpr r = y.gpr r)
    (VG.Proof.MlDsa.Arm.Sign.postDep (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr (VG.Proof.MlDsa.Arm.Sign.copySetup_nomem dst src n))
      (fun x y _ => ⟨VG.Proof.MlDsa.Arm.Sign.copySetup_ok b1 b2 x, VG.Proof.MlDsa.Arm.Sign.copySetup_ok b1 b2 y⟩)
      fun x y x' y' hp ⟨a0, a1, a2, _⟩ ⟨c0, c1, c2, _⟩ => ?_)
    (VG.Proof.MlKem.Arm.taint_prog [.r0, .r1, .r2] (fun _ _ h => h) (by taint_decide))
  obtain ⟨e1, e2⟩ := hP x y hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0, c0, e2]
  · rw [a1, c1, e1]
  · rw [a2, c2]

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inv`. -/
section

/-!
# ML-DSA signing on ARMv7: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r1)) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r2)) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (D : Nat) (σ s : State) : Prop where
  top : VG.Proof.MlDsa.Arm.Sign.Top σ s
  lay : VG.Proof.MlDsa.Arm.Sign.Lay D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) s
  sk : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (.r4, 0)) p.skLen = VG.Proof.MlDsa.Arm.Sign.skOf p σ
  mu : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (.r5, 0)) 64 = VG.Proof.MlDsa.Arm.Sign.muOf σ
  rnd : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (.r6, 0)) 32 = VG.Proof.MlDsa.Arm.Sign.rndOf σ

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.topChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (.r4, 0) p.skLen && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (.r5, 0) 64 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (.r6, 0) 32

theorem St.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Sign.St p D σ s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.stChk p ws = true) : VG.Proof.MlDsa.Arm.Sign.St p D σ s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.stChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP (VG.Proof.MlDsa.Arm.Sign.sgB_bases p), (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : VG.Spec.MlDsa.Poly) : Prop := PolyIs s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → VG.Spec.MlDsa.Poly) : Prop := ∀ j < m, VG.Proof.MlDsa.Arm.Sign.Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool := m == 0 || keepB bs ws (pS b) (1024 * m)

theorem famChk_one {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : VG.Proof.MlDsa.Arm.Sign.famChk bs ws b m = true) (hj : j < m) :
    VG.Proof.MlDsa.Arm.Sign.keepB bs ws (pS (b + j)) 1024 = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine VG.Proof.MlDsa.Arm.Sign.keepB_sub h ?_ ?_ <;> simp only [oP] <;> omega

theorem Fam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly}
    (hc : VG.Proof.MlDsa.Arm.Sign.famChk (rbs ++ wbs) ws b m = true) (h : VG.Proof.MlDsa.Arm.Sign.Fam s b m f) : VG.Proof.MlDsa.Arm.Sign.Fam s' b m f :=
  fun j hj => L.keepPoly hP (VG.Proof.MlDsa.Arm.Sign.famChk_one hc hj) (h j hj)

theorem Pl.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) {j : Nat} {f : VG.Spec.MlDsa.Poly}
    (hc : VG.Proof.MlDsa.Arm.Sign.keepB (rbs ++ wbs) ws (pS j) 1024 = true) (h : VG.Proof.MlDsa.Arm.Sign.Pl s j f) : VG.Proof.MlDsa.Arm.Sign.Pl s' j f :=
  L.keepPoly hP hc h

theorem Fam.congr {s : State} {b m : Nat} {f g : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s b m f) (e : ∀ j < m, f j = g j) :
    VG.Proof.MlDsa.Arm.Sign.Fam s b m g := fun j hj => e j hj ▸ h j hj

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.split {s : State} {b m r : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (hr : r ≤ m) :
    VG.Proof.MlDsa.Arm.Sign.Fam s b m f ↔ VG.Proof.MlDsa.Arm.Sign.Fam s b r f ∧ VG.Proof.MlDsa.Arm.Sign.Fam s (b + r) (m - r) fun j => f (r + j) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), fun j hj => by rw [Nat.add_assoc]; exact h (r + j) (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases e : j < r
    · exact h1 j e
    · have := h2 (j - r) (by omega)
      simp only [show b + r + (j - r) = b + j by omega, show r + (j - r) = j by omega] at this
      exact this

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Prims`. -/
section

/-!
# ML-DSA signing on ARMv7: the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is verified against its shared contract (`Spec/MlDsa/Poly.lean`) for a
stack that, with the frame of its stack arguments, fits in the `D` bytes the
function gives its calls (`Callee`); and, of the two samplers whose result the
function branches on, that the result is public in their own runs (`RetPub`)
and that they succeed only when the algorithm finishes within `maxBounds`, the
bounds the leakage of signing is stated for.

A callee's precondition is stated of its entry state `E` (`Ent`): its stack
pointer leaves `S` bytes below it, apart from the buffers of the layout, and
its memory agrees with the caller's on those buffers; the entry state of a
call with its arguments in registers is one (`ent_R`), and so is that of a
call with a frame of stack arguments (`ent_S`). For each call of an
arithmetic primitive: what it does (`…At_ok`), and that two runs in the
same layout leak the same (`…At_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (push2_frame push2_arg addr_sub setWidth_append32)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs need of the implementations `P` of the primitives, with
`D` bytes of stack for each call. -/
structure PrimsOk (P : Prims) (D : Nat) where
  ntt : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => nttContract Arm.abi S) 0 D P.ntt
  invNtt : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => nttInvContract Arm.abi S) 0 D P.invNtt
  mul : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => mulContract Arm.abi S) 0 D P.mul
  mulAdd : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => mulAddContract Arm.abi S) 0 D P.mulAdd
  add : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => addContract Arm.abi S) 0 D P.add
  sub : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => subContract Arm.abi S) 0 D P.sub
  rejNTT : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => rejNTTContract Arm.abi S) 0 D P.rejNTT
  expandMask : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => expandMaskContract Arm.abi S) 0 D P.expandMask
  ball : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => sampleInBallContract Arm.abi S) 8 D P.ball
  highBits : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => highBitsContract Arm.abi S) 0 D P.highBits
  lowBits : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => lowBitsContract Arm.abi S) 0 D P.lowBits
  normLt : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => normLtContract Arm.abi S) 0 D P.normLt
  makeHint : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => makeHintContract Arm.abi S) 0 D P.makeHint
  simpleBitPack : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => simpleBitPackContract Arm.abi S) 0 D P.simpleBitPack
  bitPack : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => bitPackContract Arm.abi S) 8 D P.bitPack
  bitUnpack : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => bitUnpackContract Arm.abi S) 8 D P.bitUnpack
  hintBitPack : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => hintBitPackContract Arm.abi S) 8 D P.hintBitPack
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : VG.Proof.MlDsa.Arm.Sign.RetPub (rejNTTContract Arm.abi rejNTT.S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract Arm.abi rejNTT.S).pre s → Exec isa P.rejNTT s t s' →
    s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (State.addr (s.gpr .r0)) 34)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : VG.Proof.MlDsa.Arm.Sign.RetPub (sampleInBallContract Arm.abi ball.S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract Arm.abi ball.S).pre s → Exec isa P.ball s t s' →
    s'.gpr .r0 = 1 →
    (VG.Spec.MlDsa.sampleInBall (s.gpr .r2).toNat maxBounds.ball (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)).isSome
  /-- `D` leaves room for the frames of the calls of the sponge functions. -/
  hD : 8 ≤ D
  hD' : D < 2 ^ 32

/-- `k` with the fact `X` of each run added to its postcondition. -/
def withPost (k : Contract isa) (X : State → State → Prop) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ X s s' }

theorem hv_with {c : Prog isa} {k : Contract isa} {X : State → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hx : ∀ s t s', k.pre s → Exec isa c s t s' → X s s') :
    ∀ s, (VG.Proof.MlDsa.Arm.Sign.withPost k X).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlDsa.Arm.Sign.withPost k X).post s s' :=
  fun s hs => let ⟨t, s', e, a, p⟩ := hv s hs; ⟨t, s', e, a, p, hx s t s' hs e⟩

/-! ## Values of arguments -/

theorem toNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; omega

/-! ## The entry state of a callee -/

/-- The entry state `E` of a callee called from `s` in a layout, for a
callee with a stack of `S` bytes: the `S` bytes below its stack pointer
lie apart from the buffers, and its memory agrees with `s`'s on them. -/
structure Ent (D : Nat) (rbs wbs : List (Reg × Nat)) (s : State) (S : Nat) (E : State) : Prop where
  L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s
  stk : ∀ p l, VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true → (belowA E.sp S).Disjoint ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩
  wf : S ≤ E.sp.toNat
  mem : ∀ p l, VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true → ∀ i < l, E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p + BitVec.ofNat 64 i) = s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p + BitVec.ofNat 64 i)

section
variable {D S : Nat} {rbs wbs : List (Reg × Nat)} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E)
include En

theorem Ent.poly {p : Ptr} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p 1024 = true) : polyAt E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) = polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) :=
  VG.Proof.MlDsa.Sign.polyAt_congr fun k hk => En.mem p 1024 h k hk

theorem Ent.natPoly {p : Ptr} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p 1024 = true) :
    natPolyAt E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) = natPolyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) :=
  VG.Proof.MlDsa.Sign.natPolyAt_congr fun k hk => En.mem p 1024 h k hk

theorem Ent.red {p : Ptr} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p)) :
    Reduced E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) :=
  VG.Proof.MlDsa.Sign.reduced_congr (fun k hk => En.mem p 1024 h k hk) hr

theorem Ent.bytes {p : Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) :
    bytesAt E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) l = bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) l :=
  VG.Proof.MlKem.bytesAt_congr fun k hk => En.mem p l h k hk

theorem Ent.coeff {p : Ptr} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p 1024 = true) {i : Nat} (hi : i < 256) :
    coeffAt E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) i = coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) i :=
  coeffAt_congr₂ (fun k hk => En.mem p 1024 h k hk) hi

theorem Ent.hint {p : Ptr} {k : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p (1024 * k) = true) :
    hintAt E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) k = hintAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) k :=
  VG.Proof.MlDsa.Sign.hintAt_congr fun x hx => En.mem p _ h x hx

theorem Ent.coeffs {p : Ptr} {len : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p (len * 4) = true) :
    (List.range len).map (fun i => (coeffAt E.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) i).toNat) =
      (List.range len).map (fun i => (coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s p) i).toNat) :=
  coeffs_congr fun x hx => En.mem p _ h x (by omega)

/-- The stack of the callee, apart from buffers of the layout. -/
theorem Ent.conj {bs : List (Ptr × Nat)} (h : ∀ b ∈ bs, VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) b.1 b.2 = true) :
    Sig.conj ((List.map (fun r => (bs.map fun b => (⟨VG.Proof.MlDsa.Arm.Sign.pa s b.1, b.2⟩ : Region)).map fun B => r.Disjoint B)
      (stackBelow (State.addr E.sp) S)).flatten) := by
  cases S with
  | zero => exact trivial
  | succ S =>
    simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Sig.conj_map]
    intro B hB
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    exact En.stk b.1 b.2 (h b hb)

end

/-- The stack of a callee, apart from the regions `bs`. -/
theorem conj_stk {sp : BitVec 32} {S : Nat} (bs : List Region) (h : ∀ B ∈ bs, (belowA sp S).Disjoint B) :
    Sig.conj ((List.map (fun r => bs.map fun B => r.Disjoint B) (stackBelow (State.addr sp) S)).flatten) := by
  cases S with
  | zero => exact trivial
  | succ S =>
    simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Sig.conj_map]
    exact h

theorem wf0 {S : Nat} {sp : BitVec 32} (h : S ≤ sp.toNat) :
    (match (generalizing := false) S with | 0 => sp.toNat ≤ 2 ^ 32 | n => n ≤ sp.toNat ∧ sp.toNat ≤ 2 ^ 32) := by
  have := sp.isLt
  cases S <;> simp only <;> omega

theorem wf4 {S : Nat} {sp : BitVec 32} (h : S ≤ sp.toNat) (h' : sp.toNat + 4 ≤ 2 ^ 32) :
    (match (generalizing := false) S with
      | 0 => sp.toNat + 4 ≤ 2 ^ 32 | n => n ≤ sp.toNat ∧ sp.toNat + 4 ≤ 2 ^ 32) := by
  cases S <;> simp only <;> omega

/-- The entry state of a call with its arguments in registers. -/
theorem ent_R {D S : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) (hS : S ≤ D) (rd wr : List Region) :
    VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S (s1.callEntry.withRegions rd wr) := by
  refine ⟨L, fun p l h => ?_, ?_, fun p l h i hi => ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, k.sp]
    exact (L.stkD h).sub_left (belowA_sub hS)
  · simp only [State.withRegions_sp, State.callEntry_sp, k.sp]; have := L.sp; omega
  · simp only [State.withRegions_mem, State.callEntry_mem, k.mem]

theorem pushed_sp8 (s : State) : (pushed [.r12, .lr] s).sp = s.sp - BitVec.ofNat 32 8 := rfl

/-- The entry state of a call with a frame of stack arguments. -/
theorem ent_S {D S : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) (hS : S + 8 ≤ D) (rd wr : List Region) :
    VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) := by
  have h8 : 8 ≤ s.sp.toNat := by have := L.sp; omega
  refine ⟨L, fun p l h => ?_, ?_, fun p l h i hi => ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, k.sp]
    exact (L.stkD h).sub_left fun x hx => belowA_sub (show 8 + S ≤ D by omega) x
      (belowA_push (by have := L.sp; omega) x hx)
  · simp only [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, k.sp, VG.Proof.MlDsa.Arm.Sign.sp_sub8 h8]; have := L.sp; omega
  · simp only [State.withRegions_mem, State.callEntry_mem]
    have f := push2_frame (s := s1) (by rw [k.sp]; exact h8)
    rw [k.mem] at f
    refine f _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hd := (L.stkD h).sub_left (belowA_sub (show 8 ≤ D by omega))
    intro hc
    refine hd _ (by rw [← k.sp]; exact hc) (Offset.contains_base _ (by omega) (by have := L.nwp h; omega))

/-! ## The stack argument of a call with a frame -/

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1)
include L k

/-- The address and value of the stack argument, in the callee's entry state. -/
theorem stk_arg (hD : 8 ≤ D) (rd wr : List Region) :
    stackArgAddr ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) 0 = State.addr s.sp - BitVec.ofNat 64 8 ∧
      stackArg ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) 0 = s1.gpr .r12 := by
  have h8 : 8 ≤ s1.sp.toNat := by rw [k.sp]; have := L.sp; omega
  obtain ⟨a0, a1, -⟩ := push2_arg (t := (pushed [.r12, .lr] s1).callEntry.withRegions rd wr) h8 rfl rfl
  rw [← k.sp]; exact ⟨a0, a1⟩

/-- The regions a callee with a frame of stack arguments is given, in the
state after the push. -/
theorem cov_S (hD : 8 ≤ D) {rd wr : List Region} (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers ((rd ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) ++ wr) ((pushed [.r12, .lr] s1).rd ++ (pushed [.r12, .lr] s1).wr) ∧
      Covers wr (pushed [.r12, .lr] s1).wr := by
  have h8 : 8 ≤ s1.sp.toNat := by rw [k.sp]; have := L.sp; omega
  have hwp : (pushed [.r12, .lr] s1).wr = belowA s.sp 8 :: s.wr := by
    rw [VG.Arm.pushed_wr, VG.Proof.MlDsa.Arm.Sign.frame8 h8, k.wr, k.sp]
  rw [VG.Arm.pushed_rd, hwp, k.rd]
  refine ⟨fun x m hx => ?_, fun x m hx => ?_⟩
  · rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), VG.Proof.MlDsa.Arm.Sign.argR_contains hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

omit k in
/-- The stack argument lies apart from the buffers. -/
theorem argR_disj (hD : 8 ≤ D) {p : Ptr} {l : Nat} (h : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) p l = true) :
    (VG.Proof.MlDsa.Arm.Sign.argR s).Disjoint ⟨VG.Proof.MlDsa.Arm.Sign.pa s p, l⟩ :=
  (L.stkD h).sub_left fun x hx => belowA_sub hD x (VG.Proof.MlDsa.Arm.Sign.argR_sub s x hx)

omit k in
/-- The stack argument lies above the callee's stack. -/
theorem argR_stk {S : Nat} (hS : S + 8 ≤ D) : (belowA (s.sp - BitVec.ofNat 32 8) S).Disjoint (VG.Proof.MlDsa.Arm.Sign.argR s) := by
  have h8 : 8 ≤ s.sp.toNat := by have := L.sp; omega
  have := L.sp; have := s.sp.isLt
  simp only [belowA, VG.Proof.MlDsa.Arm.Sign.argR]
  rw [VG.Proof.MlKem.Arm.addr_sub h8]
  exact (Offset.base_disjoint_below _ (by omega)).symm

end

/-! ## Registers of the entry state -/

theorem vR (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem vS (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, VG.Arm.pushed_gpr]

theorem nl0 : Reg.r0 ∉ linkRegs := by decide
theorem nl1 : Reg.r1 ∉ linkRegs := by decide
theorem nl2 : Reg.r2 ∉ linkRegs := by decide
theorem nl3 : Reg.r3 ∉ linkRegs := by decide

/-- The memory of the entry state of a call with its arguments in registers. -/
theorem vR_mem {s s1 : State} (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) (rd wr : List Region) :
    (s1.callEntry.withRegions rd wr).mem = s.mem := by
  rw [State.withRegions_mem, State.callEntry_mem, k.mem]

/-! ## Addition and subtraction -/

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- The contract of `vg_mldsa_add` (`t = add`) or `vg_mldsa_sub` (`t = sub`). -/
abbrev accC (t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly) (S : Nat) : Contract isa :=
  accSig.contract Arm.abi
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (t (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := S)

/-- What a call of `vg_mldsa_add` or `vg_mldsa_sub` on `f`, `g` needs of the layout. -/
def accChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs f 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs g 1024 && VG.Proof.MlDsa.Arm.Sign.sepB bs f 1024 g 1024 && decide (f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) &&
    decide (g.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem accChk_spec {bs wbs : List (Reg × Nat)} {f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.accChk bs wbs f g = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs f 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs g 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs f 1024 g 1024 = true ∧
      ([Arg.ptr f, .ptr g].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.accChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, by simp [Arg.ok, h5, h6]⟩

theorem accPre {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true) (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (g1 : E.gpr .r1 = s.gpr g.1 + BitVec.ofNat 32 g.2) (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s g)]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)])
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    (VG.Proof.MlDsa.Arm.Sign.accC t S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.accChk_spec hc
  sig_pre [accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, En.L.w i1 (by decide), En.L.w i2 (by decide)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(f, 1024), (g, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.red i1 rf, En.red i2 rg⟩

theorem accAt_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => VG.Proof.MlDsa.Arm.Sign.accC t S) 0 D c)
    {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    WP isa (callR n c [.ptr f, .ptr g]) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g))) := by
  obtain ⟨w1, i1, i2, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.accChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) ok L.sp
    (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s g)]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.accPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := C.hS; omega) _ _) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hA).2) rfl rfl rf rg)
    (Covers.append_left (L.cR i2) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hA
  sig_post [accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem accAt_tr {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => VG.Proof.MlDsa.Arm.Sign.accC t S) 0 D c)
    {f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y g))) (callR n c [.ptr f, .ptr g]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.accChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr C.ver.1 C.ver.2.1 ok fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.accPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx).2) rfl rfl rfx rgx,
      VG.Proof.MlDsa.Arm.Sign.accPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy).2) rfl rfl rfy rgy, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i2) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i2) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy
  sig_pub [accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

theorem addAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    WP isa (addAt P f g) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g))) :=
  VG.Proof.MlDsa.Arm.Sign.accAt_ok (t := VG.Spec.MlDsa.add) hP.add L hc rf rg

theorem subAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    WP isa (subAt P f g) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (VG.Spec.MlDsa.sub (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g))) :=
  VG.Proof.MlDsa.Arm.Sign.accAt_ok (t := VG.Spec.MlDsa.sub) hP.sub L hc rf rg

theorem addAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y g))) (addAt P f g) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.accAt_tr (t := VG.Spec.MlDsa.add) hP.add hc

theorem subAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y g))) (subAt P f g) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.accAt_tr (t := VG.Spec.MlDsa.sub) hP.sub hc

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsS`. -/
section

/-!
# ML-DSA signing on ARMv7: calls of the samplers

As `Prims.lean`, for `vg_mldsa_rej_ntt_poly`, `vg_mldsa_expand_mask_poly` and
`vg_mldsa_sample_in_ball` (whose fifth argument is on the stack). The results
of `RejNTTPoly` and `SampleInBall` are public in two runs whose seeds agree
(`rejCall_tr`, `ballCall_tr`), and they succeed only if the algorithm finishes
within `maxBounds` (`rejCall_ok`, `ballCall_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32 push2_arg)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
def rejChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs a 1024 && VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 2048 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oRS) 34 && VG.Proof.MlDsa.Arm.Sign.inB bs a 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 2048 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oRS) 34 a 1024 && VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oRS) 34 (sc oPS) 2048 && VG.Proof.MlDsa.Arm.Sign.sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem rejChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.rejChk bs wbs a = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs a 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 2048 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs (sc oRS) 34 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs a 1024 = true ∧
      VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 2048 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oRS) 34 a 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oRS) 34 (sc oPS) 2048 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs a 1024 (sc oPS) 2048 = true ∧ ([Arg.ptr (sc oRS), .ptr a, .ptr (sc oPS)].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.rejChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by simp [Arg.ok, h9]⟩

theorem rejPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {a : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.rejChk (rbs ++ wbs) wbs a = true) (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oRS)
    (g1 : E.gpr .r1 = s.gpr a.1 + BitVec.ofNat 32 a.2) (g2 : E.gpr .r2 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (hrd : E.rd = [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS), 34⟩]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s a), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩]) :
    (rejNTTContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.Arm.Sign.rejChk_spec hc
  sig_pre [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w (p := sc oRS) i1 (by decide), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(sc oRS, 34), (a, 1024), (sc oPS, 2048)]) (by simp [i1, i2, i3]),
    En.L.fit (p := sc oRS) i1 (by decide), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide)⟩

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {a : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)]) s fun s' =>
      VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      (s'.gpr .r0 = 1 → Reduced s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS)) 34)) (s'.gpr .r0)
        (polyAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s a)) ∧
      (s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS)) 34)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.rejChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok (VG.Proof.MlDsa.Arm.Sign.hv_with hP.rejNTT.ver.1 hP.rejMax) (by have := hP.rejNTT.su; have := hP.rejNTT.hS; omega)
    ok L.sp (rd := [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS), 34⟩]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s a), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.rejPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.rejNTT.hS; omega) _ _) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.2) rfl rfl)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hA
  sig_post [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, setWidth_append32,
    L.w (p := sc oRS) i1 (by decide), L.w i2 (by decide)] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, State.callEntry_mem, e1, Arg.val, k.mem,
    State.addr, L.w (p := sc oRS) i1 (by decide)] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCall_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {a : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.rejChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x (sc oRS)) 34 = bytesAt y.mem (VG.Proof.MlDsa.Arm.Sign.pa y (sc oRS)) 34)
      (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)])
      fun x y => x.gpr .r0 = y.gpr .r0 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.rejChk_spec hc
  have hS : hP.rejNTT.S ≤ D := by have := hP.rejNTT.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callRRet_tr hP.rejNTT.ver.1 hP.rejRet ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.rejPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [⟨VG.Proof.MlDsa.Arm.Sign.pa x (sc oRS), 34⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x a), ⟨VG.Proof.MlDsa.Arm.Sign.pa x (sc oPS), 2048⟩]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.2) rfl rfl,
      VG.Proof.MlDsa.Arm.Sign.rejPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [⟨VG.Proof.MlDsa.Arm.Sign.pa y (sc oRS), 34⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y a), ⟨VG.Proof.MlDsa.Arm.Sign.pa y (sc oPS), 2048⟩]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy
  sig_pub [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, kx.mem, ky.mem, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val,
    R.lx.w (p := sc oRS) i1 (by decide), R.ly.w (p := sc oRS) i1 (by decide), hb]
  simp only [R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
def maskChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs a 1024 && VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 2048 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oMS) 66 && VG.Proof.MlDsa.Arm.Sign.inB bs a 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 2048 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oMS) 66 a 1024 && VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oMS) 66 (sc oPS) 2048 && VG.Proof.MlDsa.Arm.Sign.sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem maskChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.maskChk bs wbs a = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs a 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 2048 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs (sc oMS) 66 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs a 1024 = true ∧
      VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 2048 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oMS) 66 a 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oMS) 66 (sc oPS) 2048 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs a 1024 (sc oPS) 2048 = true ∧ a.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  simp only [VG.Proof.MlDsa.Arm.Sign.maskChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem maskPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.Arm.Sign.maskChk (rbs ++ wbs) wbs a = true)
    (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oMS) (g1 : E.gpr .r1 = BitVec.ofNat 32 γ)
    (g2 : E.gpr .r2 = s.gpr a.1 + BitVec.ofNat 32 a.2) (g3 : E.gpr .r3 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (hrd : E.rd = [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oMS), 66⟩]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s a), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩]) :
    (expandMaskContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.Arm.Sign.maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  sig_pre [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w (p := sc oMS) i1 (by decide), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide), VG.Proof.MlDsa.Arm.Sign.toNat32 hγ']
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(sc oMS, 66), (a, 1024), (sc oPS, 2048)]) (by simp [i1, i2, i3]),
    En.L.fit (p := sc oMS) i1 (by decide), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide), hγ⟩

theorem maskArgs_ok {a : Ptr} {γ : Nat} (b1 : a.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr (sc oMS), .imm γ, .ptr a, .ptr (sc oPS)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem maskAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.Arm.Sign.maskChk (rbs ++ wbs) wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s a) (toRq (VG.Spec.MlDsa.bitUnpack (VG.Spec.MlDsa.H (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := VG.Proof.MlDsa.Arm.Sign.maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok hP.expandMask.ver.1 (by have := hP.expandMask.su; have := hP.expandMask.hS; omega)
    (VG.Proof.MlDsa.Arm.Sign.maskArgs_ok b1) L.sp (rd := [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oMS), 66⟩]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s a), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.maskPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.expandMask.hS; omega) _ _) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.2.2) rfl rfl)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, _⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hA
  sig_post [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, VG.Proof.MlDsa.Arm.Sign.toNat32 hγ', L.w (p := sc oMS) i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem maskAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : VG.Proof.MlDsa.Arm.Sign.maskChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (maskAt P γ a) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := VG.Proof.MlDsa.Arm.Sign.maskChk_spec hc
  have hS : hP.expandMask.S ≤ D := by have := hP.expandMask.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr hP.expandMask.ver.1 hP.expandMask.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.maskArgs_ok b1)
    fun x y x1 y1 R ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.maskPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [⟨VG.Proof.MlDsa.Arm.Sign.pa x (sc oMS), 66⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x a), ⟨VG.Proof.MlDsa.Arm.Sign.pa x (sc oPS), 2048⟩]) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.2.2) rfl rfl,
      VG.Proof.MlDsa.Arm.Sign.maskPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [⟨VG.Proof.MlDsa.Arm.Sign.pa y (sc oMS), 66⟩] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y a), ⟨VG.Proof.MlDsa.Arm.Sign.pa y (sc oPS), 2048⟩]) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.2.2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy
  sig_pub [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
def ballChk (bs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs c 1024 && VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 2048 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oCT) len && VG.Proof.MlDsa.Arm.Sign.inB bs c 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 2048 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oCT) len c 1024 && VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oCT) len (sc oPS) 2048 && VG.Proof.MlDsa.Arm.Sign.sepB bs c 1024 (sc oPS) 2048 &&
    decide (c.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem ballChk_spec {bs wbs : List (Reg × Nat)} {len : Nat} {c : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.ballChk bs wbs len c = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs c 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 2048 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs (sc oCT) len = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs c 1024 = true ∧
      VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 2048 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oCT) len c 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs (sc oCT) len (sc oPS) 2048 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs c 1024 (sc oPS) 2048 = true ∧ c.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  simp only [VG.Proof.MlDsa.Arm.Sign.ballChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem ballArgs_ok {len tau : Nat} {c : Ptr} (b1 : c.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem ballParams_lt {len tau : Nat} (hp : (len, tau) ∈ ballParams) : 0 < len ∧ len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega

theorem ballPre {S : Nat} (hS : S + 8 ≤ D) {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.Arm.Sign.ballChk (rbs ++ wbs) wbs len c = true)
    (hsp : E.sp = s.sp - BitVec.ofNat 32 8) (ha : stackArgAddr E 0 = State.addr s.sp - BitVec.ofNat 64 8)
    (hv : stackArg E 0 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oCT) (g1 : E.gpr .r1 = BitVec.ofNat 32 len)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 tau) (g3 : E.gpr .r3 = s.gpr c.1 + BitVec.ofNat 32 c.2)
    (hrd : E.rd = [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT), len⟩, VG.Proof.MlDsa.Arm.Sign.argR s]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s c), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩]) :
    (sampleInBallContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := VG.Proof.MlDsa.Arm.Sign.ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := VG.Proof.MlDsa.Arm.Sign.ballParams_lt hp
  have h8 : 8 ≤ s.sp.toNat := by have := En.L.sp; omega
  have e8 : E.sp.toNat = s.sp.toNat - 8 := by rw [hsp, VG.Proof.MlDsa.Arm.Sign.sp_sub8 h8]
  sig_pre [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ha, hv, En.L.w (p := sc oCT) i1 (by omega), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide), VG.Proof.MlDsa.Arm.Sign.toNat32 l1, VG.Proof.MlDsa.Arm.Sign.toNat32 l2]
  have hD : 8 ≤ D := by omega
  refine ⟨VG.Proof.MlDsa.Arm.Sign.wf4 En.wf (by have := s.sp.isLt; omega), hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    (VG.Proof.MlDsa.Arm.Sign.argR_disj En.L hD i2).symm, (VG.Proof.MlDsa.Arm.Sign.argR_disj (p := sc oPS) En.L hD i3).symm,
    VG.Proof.MlDsa.Arm.Sign.conj_stk [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT), len⟩, VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s c), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩, VG.Proof.MlDsa.Arm.Sign.argR s] ?_,
    En.L.fit (p := sc oCT) i1 (by omega), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide), hp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.stk _ _ i1, En.stk _ _ i2, En.stk _ _ i3, hsp ▸ VG.Proof.MlDsa.Arm.Sign.argR_stk En.L hS⟩

/-- The regions `SampleInBall` is given. -/
abbrev ballRd (s : State) (len : Nat) : List Region := [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT), len⟩]
abbrev ballWr (s : State) (c : Ptr) : List Region := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s c), ⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS), 2048⟩]

theorem ballPre' {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s s1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1)
    {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.Arm.Sign.ballChk (rbs ++ wbs) wbs len c = true)
    (hA : VG.Proof.MlDsa.Arm.Sign.ArgsIn [.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)] s s1) :
    (sampleInBallContract Arm.abi hP.ball.S).pre
      ((pushed [.r12, .lr] s1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Sign.ballRd s len ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) (VG.Proof.MlDsa.Arm.Sign.ballWr s c)) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
  have hS := hP.ball.hS
  obtain ⟨ha, hv⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg L k (by omega) (VG.Proof.MlDsa.Arm.Sign.ballRd s len ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) (VG.Proof.MlDsa.Arm.Sign.ballWr s c)
  exact VG.Proof.MlDsa.Arm.Sign.ballPre hS (VG.Proof.MlDsa.Arm.Sign.ent_S L k hS _ _) hp hc (by rw [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, k.sp]) ha
    (by rw [hv, e4]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
    (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.Arm.Sign.ballChk (rbs ++ wbs) wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      (s'.gpr .r0 = 1 → Reduced s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s c)) ∧
      Outcome (fun b => (VG.Spec.MlDsa.sampleInBall tau b.ball (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) len)).map toRq)
        (s'.gpr .r0) (polyAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s c)) ∧
      (s'.gpr .r0 = 1 → (VG.Spec.MlDsa.sampleInBall tau maxBounds.ball (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) len)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := VG.Proof.MlDsa.Arm.Sign.ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := VG.Proof.MlDsa.Arm.Sign.ballParams_lt hp
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callS_ok (VG.Proof.MlDsa.Arm.Sign.hv_with hP.ball.ver.1 hP.ballMax) (by have := hP.ball.su; have := hP.ball.hS; omega)
    (VG.Proof.MlDsa.Arm.Sign.ballArgs_ok b1) L.sp (rd := VG.Proof.MlDsa.Arm.Sign.ballRd s len) (wr := VG.Proof.MlDsa.Arm.Sign.ballWr s c)
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.ballPre' hP L k hp hc hA) (L.cR i1) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, _⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
  have En := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.ball.S) L k hP.ball.hS (VG.Proof.MlDsa.Arm.Sign.ballRd s len ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) (VG.Proof.MlDsa.Arm.Sign.ballWr s c)
  have er : s₂.gpr .r0 = s'.gpr .r0 := hg₂ .r0 (by decide)
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Sign.ballRd s len ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) (VG.Proof.MlDsa.Arm.Sign.ballWr s c) with hE
  have g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oCT := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 len := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 tau := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr c.1 + BitVec.ofNat 32 c.2 := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl
  have eb := En.bytes (p := sc oCT) i1
  clear_value E
  sig_post [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, hm₂, er, setWidth_append32, VG.Proof.MlDsa.Arm.Sign.toNat32 l1, VG.Proof.MlDsa.Arm.Sign.toNat32 l2,
    L.w (p := sc oCT) i1 (by omega), L.w i2 (by decide), eb] at hq
  simp only [State.withRegions_gpr, g0, g1, g2, er, VG.Proof.MlDsa.Arm.Sign.toNat32 l1, VG.Proof.MlDsa.Arm.Sign.toNat32 l2, State.addr,
    L.w (p := sc oCT) i1 (by omega), eb] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : VG.Proof.MlDsa.Arm.Sign.ballChk (rbs ++ wbs) wbs len c = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x (sc oCT)) len = bytesAt y.mem (VG.Proof.MlDsa.Arm.Sign.pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => x.gpr .r0 = y.gpr .r0 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := VG.Proof.MlDsa.Arm.Sign.ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := VG.Proof.MlDsa.Arm.Sign.ballParams_lt hp
  have hS := hP.ball.hS
  refine VG.Proof.MlDsa.Arm.Sign.callSRet_tr hP.ball.ver.1 hP.ballRet (VG.Proof.MlDsa.Arm.Sign.ballArgs_ok b1) (fun x y h => h.1.sp)
    fun x y x1 y1 ⟨R, hb⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.ballPre' hP R.lx kx hp hc hAx, VG.Proof.MlDsa.Arm.Sign.ballPre' hP R.ly ky hp hc hAy, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAx
    obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAy
    have Ex := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.ball.S) R.lx kx hS (VG.Proof.MlDsa.Arm.Sign.ballRd x len ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) (VG.Proof.MlDsa.Arm.Sign.ballWr x c)
    have Ey := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.ball.S) R.ly ky hS (VG.Proof.MlDsa.Arm.Sign.ballRd y len ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) (VG.Proof.MlDsa.Arm.Sign.ballWr y c)
    obtain ⟨-, vx⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.lx kx (by omega) (VG.Proof.MlDsa.Arm.Sign.ballRd x len ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) (VG.Proof.MlDsa.Arm.Sign.ballWr x c)
    obtain ⟨-, vy⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.ly ky (by omega) (VG.Proof.MlDsa.Arm.Sign.ballRd y len ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) (VG.Proof.MlDsa.Arm.Sign.ballWr y c)
    set X := (pushed [.r12, .lr] x1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Sign.ballRd x len ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) (VG.Proof.MlDsa.Arm.Sign.ballWr x c) with hX
    set Y := (pushed [.r12, .lr] y1).callEntry.withRegions (VG.Proof.MlDsa.Arm.Sign.ballRd y len ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) (VG.Proof.MlDsa.Arm.Sign.ballWr y c) with hY
    have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
      intro r hr; rw [hX, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
    have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
      intro r hr; rw [hY, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
    have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, kx.sp]
    have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, ky.sp]
    have bx := Ex.bytes (p := sc oCT) i1
    have bY := Ey.bytes (p := sc oCT) i1
    clear_value X Y
    sig_pub [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
      gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
      hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, VG.Proof.MlDsa.Arm.Sign.toNat32 l1]
    rw [R.lx.w (p := sc oCT) i1 (by omega), R.ly.w (p := sc oCT) i1 (by omega), bx, bY, hb]
    simp only [R.eq i1, R.eq i2, R.sp, and_self]
  · exact (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (Covers.cons (R.lx.cW w1) (R.lx.cW w2))).1
  · exact (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (Covers.cons (R.lx.cW w1) (R.lx.cW w2))).2
  · exact (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly ky (by omega) (R.ly.cR i1) (Covers.cons (R.ly.cW w1) (R.ly.cW w2))).1
  · exact (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly ky (by omega) (R.ly.cR i1) (Covers.cons (R.ly.cW w1) (R.ly.cW w2))).2

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseA`. -/
section

/-!
# ML-DSA signing on ARMv7: `ExpandA`

`ρ` to `RS`, then entry `e = ℓi + j` of `Â` by `vg_mldsa_rej_ntt_poly` from
the seed `ρ ‖ j ‖ i`, with `r11` the AND of the results (`IA`): if it is 1,
every entry so far is `RejNTTPoly`'s within `maxBounds`; if it is 0, one
entry's `RejNTTPoly` does not finish within `minBounds` (`expandA_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slot of `Â[0, 0]`; entry `e = ℓi + j` is in slot `aBase + e`. -/
abbrev aBase : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (VG.Proof.MlDsa.Arm.Sign.skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : VG.Spec.MlDsa.Poly := aF maxBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : aP p (e / p.ℓ) (e % p.ℓ) = pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ) = pS (5 + 4 * p.k + 3 * p.ℓ + e)
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

theorem Fam.snoc {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s b m f) (h' : VG.Proof.MlDsa.Arm.Sign.Pl s (b + m) (f m)) :
    VG.Proof.MlDsa.Arm.Sign.Fam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  st : VG.Proof.MlDsa.Arm.Sign.St p D σ s
  rs : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS)) 32 = VG.Proof.MlDsa.Arm.Sign.rhoOf p σ
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  ok : s.gpr .r11 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.seedE p σ e')).isSome) ∧
    VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.aBase p) e (VG.Proof.MlDsa.Arm.Sign.aVal p σ)
  bad : s.gpr .r11 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.seedE p σ e') = none

/-! ## The seed -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem seed34 {m : Mem} {a : Addr} {ρ : List Byte} (hρ : bytesAt m a 32 = ρ) {j i : Nat}
    (hj : bytesAt m (a + BitVec.ofNat 64 32) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (a + BitVec.ofNat 64 33) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m a 34 = aSeed ρ i j := by
  rw [VG.Proof.MlKem.bytesAt_add m a 33 1, VG.Proof.MlKem.bytesAt_add m a 32 1, hρ, hj, hi, aSeed,
    VG.Proof.MlDsa.Arm.Sign.integerToBytes_one, VG.Proof.MlDsa.Arm.Sign.integerToBytes_one]

theorem pa_sc_add (s : State) (a b : Nat) : VG.Proof.MlDsa.Arm.Sign.pa s (sc a) + BitVec.ofNat 64 b = VG.Proof.MlDsa.Arm.Sign.pa s (sc (a + b)) :=
  (VG.Proof.MlDsa.Arm.Sign.pa_add s .r7 a b).symm

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

/-! ## An entry -/

/-- What entry `e` needs of the layout. -/
def eChk (p : Params) (e : Nat) : Bool :=
  let a := pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)
  let w1 : List (Ptr × Nat) := [(sc (oRS + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS + 33), 1)]
  let w3 : List (Ptr × Nat) := [(a, 1024), (sc oPS, 2048)]
  VG.Proof.MlDsa.Arm.Sign.stChk p w1 && VG.Proof.MlDsa.Arm.Sign.stChk p w2 && VG.Proof.MlDsa.Arm.Sign.stChk p w3 && VG.Proof.MlDsa.Arm.Sign.stChk p [] && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc (oRS + 32)) 1 &&
    VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc (oRS + 33)) 1 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (sc oRS) 32 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w2 (sc oRS) 32 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w3 (sc oRS) 32 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w2 (sc (oRS + 32)) 1 && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (VG.Proof.MlDsa.Arm.Sign.aBase p) e &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w2 (VG.Proof.MlDsa.Arm.Sign.aBase p) e && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w3 (VG.Proof.MlDsa.Arm.Sign.aBase p) e && VG.Proof.MlDsa.Arm.Sign.rejChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) a &&
    decide (e % p.ℓ < 256) && decide (e / p.ℓ < 256)

theorem eChk_spec {p : Params} {e : Nat} (h : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) :
    VG.Proof.MlDsa.Arm.Sign.stChk p [(sc (oRS + 32), 1)] = true ∧ VG.Proof.MlDsa.Arm.Sign.stChk p [(sc (oRS + 33), 1)] = true ∧
      VG.Proof.MlDsa.Arm.Sign.stChk p [(pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e), 1024), (sc oPS, 2048)] = true ∧ VG.Proof.MlDsa.Arm.Sign.stChk p [] = true ∧
      VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc (oRS + 32)) 1 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc (oRS + 33)) 1 = true ∧
      VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc (oRS + 32), 1)] (sc oRS) 32 = true ∧ VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc (oRS + 33), 1)] (sc oRS) 32 = true ∧
      VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e), 1024), (sc oPS, 2048)] (sc oRS) 32 = true ∧
      VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc (oRS + 33), 1)] (sc (oRS + 32)) 1 = true ∧
      VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc (oRS + 32), 1)] (VG.Proof.MlDsa.Arm.Sign.aBase p) e = true ∧ VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc (oRS + 33), 1)] (VG.Proof.MlDsa.Arm.Sign.aBase p) e = true ∧
      VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e), 1024), (sc oPS, 2048)] (VG.Proof.MlDsa.Arm.Sign.aBase p) e = true ∧
      VG.Proof.MlDsa.Arm.Sign.rejChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)) = true ∧ e % p.ℓ < 256 ∧ e / p.ℓ < 256 := by
  simp only [VG.Proof.MlDsa.Arm.Sign.eChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : VG.Spec.MlDsa.Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD VG.Spec.MlDsa.zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := VG.Proof.MlDsa.Sign.rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := VG.Proof.MlDsa.Sign.rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem outcome01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α} (h : Outcome f r out) :
    r = 1 ∨ r = 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem Fam.of_eq {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr .r7 = s.gpr .r7) {b m : Nat}
    {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s b m f) : VG.Proof.MlDsa.Arm.Sign.Fam s' b m f := fun j hj => by
  simp only [VG.Proof.MlDsa.Arm.Sign.Pl, VG.Proof.MlDsa.Arm.Sign.pa, hm, hb]; exact h j hj

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

theorem blkE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.IA p D σ e s) : WP isa (.block (VG.Proof.MlDsa.Arm.Sign.blkE p e)) s fun s' =>
      (VG.Proof.MlDsa.Arm.Sign.IA p D σ e s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' (sc oRS)) 34 = VG.Proof.MlDsa.Arm.Sign.seedE p σ e) ∧ s'.gpr .r11 = s.gpr .r11 := by
  obtain ⟨c1, c2, _, _, w1, w2, k1, k2, _, k12, f1, f2, _, _, hj, hi⟩ := VG.Proof.MlDsa.Arm.Sign.eChk_spec he
  have L := h.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setB_okB L hj (by decide) (by decide) w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have S1 := h.st.step hP1 c1
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setB_okB S1.lay hi (by decide) (by decide) w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have S2 := S1.step hP2 c2
  have e15 : s2.gpr .r11 = s.gpr .r11 := by rw [hcs2 _ (by decide) (by decide), hcs1 _ (by decide) (by decide)]
  have hrs : bytesAt s2.mem (VG.Proof.MlDsa.Arm.Sign.pa s2 (sc oRS)) 32 = VG.Proof.MlDsa.Arm.Sign.rhoOf p σ :=
    (S1.lay.keepBytes hP2 k2).trans ((L.keepBytes hP1 k1).trans h.rs)
  refine ⟨⟨⟨S2, hrs, e15 ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (e15 ▸ h0)⟩, VG.Proof.MlDsa.Arm.Sign.seed34 hrs ?_ ?_⟩, e15⟩
  · obtain ⟨ok, fam⟩ := h.ok (e15 ▸ h1)
    exact ⟨ok, Fam.keep S1.lay hP2 f2 (Fam.keep L hP1 f1 fam)⟩
  · rw [VG.Proof.MlDsa.Arm.Sign.pa_sc_add, S1.lay.keepBytes hP2 k12, hm1, hP1.pa (by decide)]; exact VG.Proof.MlDsa.Arm.Sign.bytes1_write _ _ _
  · rw [VG.Proof.MlDsa.Arm.Sign.pa_sc_add, hm2, hP2.pa (by decide)]; exact VG.Proof.MlDsa.Arm.Sign.bytes1_write _ _ _

/-- What the call of entry `e` leaves. -/
def CallE (D : Nat) (a : Ptr) (x : List Byte) (s s' : State) : Prop :=
  VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
    (s'.gpr .r0 = 1 → Reduced s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s a)) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT x) (s'.gpr .r0) (polyAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s a)) ∧
    (s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT x).isSome)

/-- Entry `e`'s call is done. -/
def JE (p : Params) (D : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, VG.Proof.MlDsa.Arm.Sign.IA p D σ e s₀ ∧ VG.Proof.MlDsa.Arm.Sign.CallE D (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)) (VG.Proof.MlDsa.Arm.Sign.seedE p σ e) s₀ s

theorem callE_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IA p D σ e s) (hs : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS)) 34 = VG.Proof.MlDsa.Arm.Sign.seedE p σ e) :
    WP isa (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)), .ptr (sc oPS)]) s
      (VG.Proof.MlDsa.Arm.Sign.JE p D e σ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.eChk_spec he
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ => ⟨s, h, hP3, hcs3, hred, ?_, ?_⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem andE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.JE p D e σ s) : WP isa (.block [.dp .and .r11 .r11 (.reg .r0)]) s (VG.Proof.MlDsa.Arm.Sign.IA p D σ (e + 1)) := by
  obtain ⟨_, _, c3, c0, _, _, _, _, k3, _, _, _, f3, _, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.eChk_spec he
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := h
  have S3 := h.st.step hP3 c3
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.and11_ok s) fun s4 ⟨h15, k4⟩ => ?_
  have hP4 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s4 [] := (VG.Proof.MlDsa.Arm.Sign.postB11 k4 _).1
  rw [hcs3 _ (by decide) (by decide)] at h15
  have hr := VG.Proof.MlDsa.Arm.Sign.outcome01 hout
  have hb4 : s4.gpr .r7 = s₀.gpr .r7 := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  refine ⟨S3.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rw [k4.mem, hP4.pa (by decide), h.st.lay.keepBytes hP3 k3, h.rs]
  · rw [h15]
    rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .r11 = 1 ∧ s.gpr .r0 = 1 := by
      rw [h15] at h1
      rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := h.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, Fam.snoc ?_ ?_⟩
    · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · exact Fam.of_eq k4.mem (hP4.bs _ (by decide)) (Fam.keep h.st.lay hP3 f3 fam)
    · show PolyIs s4.mem (VG.Proof.MlDsa.Arm.Sign.pa s4 (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e))) (VG.Proof.MlDsa.Arm.Sign.aVal p σ e)
      rw [k4.mem, show VG.Proof.MlDsa.Arm.Sign.pa s4 (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)) = VG.Proof.MlDsa.Arm.Sign.pa s₀ (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)) by simp only [VG.Proof.MlDsa.Arm.Sign.pa, hb4]]
      exact ⟨hred hs.2, VG.Proof.MlDsa.Arm.Sign.rej_val hout hs.2 hm⟩
  · rw [h15] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega, hn⟩

theorem sampleE_eq (P : Prims) (p : Params) (e : Nat) : sampleE P p e = .seq (.block (VG.Proof.MlDsa.Arm.Sign.blkE p e))
    (.seq (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)), .ptr (sc oPS)])
      (.block [.dp .and .r11 .r11 (.reg .r0)])) := by
  unfold sampleE rejAt; rw [VG.Proof.MlDsa.Arm.Sign.aP_eq]

theorem sampleE_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IA p D σ e s) : WP isa (sampleE P p e) s (VG.Proof.MlDsa.Arm.Sign.IA p D σ (e + 1)) := by
  rw [VG.Proof.MlDsa.Arm.Sign.sampleE_eq]
  exact WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.blkE_ok he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.callE_ok hP he h1 hs1) fun s2 h2 => VG.Proof.MlDsa.Arm.Sign.andE_ok he h2))

/-! ## The matrix -/

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (VG.Proof.MlDsa.Arm.Sign.eChk p) && VG.Proof.MlDsa.Arm.Sign.copyChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oRS) (.r4, 0) 32 &&
    VG.Proof.MlDsa.Arm.Sign.stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen)

theorem aChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem expandA_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.aChk p = true) {σ s : State}
    (hs : VG.Proof.MlDsa.Arm.Sign.St p D σ s) (h15 : s.gpr .r11 = 1) : WP isa (Impl.MlDsa.Arm.Sign.expandA P p) s (VG.Proof.MlDsa.Arm.Sign.IA p D σ (p.k * p.ℓ)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.Arm.Sign.expandA
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB hs.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .r11 = 1 := by rw [hcs1 _ (by decide) (by decide), h15]
  have I0 : VG.Proof.MlDsa.Arm.Sign.IA p D σ 0 s1 := ⟨S1, by rw [hP1.pa (by decide), hb, VG.Proof.MlDsa.Arm.Sign.rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  have := VG.Proof.MlDsa.Arm.Sign.seqR_ok (f := sampleE P p) (I := VG.Proof.MlDsa.Arm.Sign.IA p D σ) (p.k * p.ℓ) 0
    (fun k _ hk s h => VG.Proof.MlDsa.Arm.Sign.sampleE_ok hP (he k (by omega)) h) s1 I0
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsC`. -/
section

/-!
# ML-DSA signing on ARMv7: calls of the rounding functions, the norm check and `SimpleBitPack`

As `Prims.lean`, for `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_simple_bit_pack`.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call with a buffer `f` of `lf` bytes read and a buffer `out` of
`l` bytes written needs of the layout. -/
def rwChk (bs wbs : List (Reg × Nat)) (f : Ptr) (lf : Nat) (out : Ptr) (l : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs out l && VG.Proof.MlDsa.Arm.Sign.inB bs f lf && VG.Proof.MlDsa.Arm.Sign.inB bs out l && VG.Proof.MlDsa.Arm.Sign.sepB bs f lf out l && decide (f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) &&
    decide (out.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem rwChk_spec {bs wbs : List (Reg × Nat)} {f out : Ptr} {lf l : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.rwChk bs wbs f lf out l = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs out l = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs f lf = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs out l = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs f lf out l = true ∧
      f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases ∧ out.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  simp only [VG.Proof.MlDsa.Arm.Sign.rwChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem gamma2_lt {γ : Nat} (h : γ ∈ gamma2s) : γ < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

/-! ## `HighBits` and `LowBits` -/

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q`. -/
abbrev bitsC (Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract Arm.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

theorem bitsPre {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E)
    {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true)
    (g0 : E.gpr .r0 = s.gpr r.1 + BitVec.ofNat 32 r.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 γ)
    (g2 : E.gpr .r2 = s.gpr out.1 + BitVec.ofNat 32 out.2) (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s r)])
    (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s out)]) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) :
    (VG.Proof.MlDsa.Arm.Sign.bitsC Q S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  sig_pre [bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w i1 (by decide), En.L.w i2 (by decide), VG.Proof.MlDsa.Arm.Sign.toNat32 (VG.Proof.MlDsa.Arm.Sign.gamma2_lt hγ)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(r, 1024), (out, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), hγ, En.red i1 hr⟩

theorem bitsArgs_ok {r out : Ptr} {γ : Nat} (b1 : r.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : out.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr r, .imm γ, .ptr out].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem bitsAt_ok {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => VG.Proof.MlDsa.Arm.Sign.bitsC Q S) 0 D c) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) :
    WP isa (callR n c [.ptr r, .imm γ, .ptr out]) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(out, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      Q γ (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s out) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) (VG.Proof.MlDsa.Arm.Sign.bitsArgs_ok b1 b2) L.sp
    (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s r)]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s out)])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.bitsPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := C.hS; omega) _ _) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.2) rfl rfl hr)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hA
  sig_post [bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, VG.Proof.MlDsa.Arm.Sign.toNat32 (VG.Proof.MlDsa.Arm.Sign.gamma2_lt hγ), L.w i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem bitsAt_tr {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => VG.Proof.MlDsa.Arm.Sign.bitsC Q S) 0 D c) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y r))
      (callR n c [.ptr r, .imm γ, .ptr out]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr C.ver.1 C.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.bitsArgs_ok b1 b2) fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.bitsPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x out)]) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.2) rfl rfl rx,
      VG.Proof.MlDsa.Arm.Sign.bitsPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y out)]) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.2) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy
  sig_pub [bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

theorem highBitsAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(out, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      NatPolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s out) ((polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)).map fun c => (VG.Spec.MlDsa.highBits γ c).toNat) :=
  VG.Proof.MlDsa.Arm.Sign.bitsAt_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (VG.Spec.MlDsa.highBits γ c).toNat)) hP.highBits L hγ hc hr

theorem highBitsAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.bitsAt_tr (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (VG.Spec.MlDsa.highBits γ c).toNat)) hP.highBits hγ hc

theorem lowBitsAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(out, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s out) ((polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)).map fun c => ofInt (VG.Spec.MlDsa.lowBits γ c)) :=
  VG.Proof.MlDsa.Arm.Sign.bitsAt_ok (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (VG.Spec.MlDsa.lowBits γ c))) hP.lowBits L hγ hc hr

theorem lowBitsAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y r))
      (lowBitsAt P r γ out) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.bitsAt_tr (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (VG.Spec.MlDsa.lowBits γ c))) hP.lowBits hγ hc

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
def normChk (bs : List (Reg × Nat)) (f : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 && decide (f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem normPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {f : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.normChk (rbs ++ wbs) f = true) (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]) (hwr : E.wr = []) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    (normLtContract Arm.abi S).pre E := by
  simp only [VG.Proof.MlDsa.Arm.Sign.normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨i1, _⟩ := hc
  sig_pre [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, En.L.w i1 (by decide)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.conj (bs := [(f, 1024)]) (by simp [i1]), En.L.fit i1 (by decide), En.red i1 hr⟩

theorem normArgs_ok {bs : List (Reg × Nat)} {f : Ptr} {B : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.normChk bs f = true) : [Arg.ptr f, .imm B].all Arg.ok = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp [Arg.ok, hc.2]

theorem normCall_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f : Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.Arm.Sign.normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    WP isa (callR "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm B]) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      s'.gpr .r0 = if normRq [polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)] < B then 1 else 0 := by
  have i1 : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) f 1024 = true := by
    simp only [VG.Proof.MlDsa.Arm.Sign.normChk, Bool.and_eq_true] at hc; exact hc.1
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok hP.normLt.ver.1 (by have := hP.normLt.su; have := hP.normLt.hS; omega)
    (VG.Proof.MlDsa.Arm.Sign.normArgs_ok hc) L.sp (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]) (wr := [])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.normPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.normLt.hS; omega) _ _) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hA).1) rfl rfl hr)
    (Covers.append_left (L.cR i1) Covers.nil) Covers.nil)
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hA
  sig_post [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, setWidth_append32, VG.Proof.MlDsa.Arm.Sign.toNat32 hB, L.w i1 (by decide)] at hq
  exact hq

theorem normCall_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f : Ptr} {B : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f))
      (callR "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm B]) fun _ _ => True := by
  have i1 : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) f 1024 = true := by
    simp only [VG.Proof.MlDsa.Arm.Sign.normChk, Bool.and_eq_true] at hc; exact hc.1
  have hS : hP.normLt.S ≤ D := by have := hP.normLt.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr hP.normLt.ver.1 hP.normLt.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.normArgs_ok hc) fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.normPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] []) hc (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx).1)
      rfl rfl rx,
      VG.Proof.MlDsa.Arm.Sign.normPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)] []) hc (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy).1) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) Covers.nil, Covers.nil,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) Covers.nil, Covers.nil⟩
  obtain ⟨hx1, hx2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy
  sig_pub [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.sp, and_self]

/-! ## `MakeHint` -/

/-- What a call of `vg_mldsa_make_hint` on `z`, `r` to `h` needs of the layout. -/
def hintChk (bs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs h 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs z 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs r 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs h 1024 && VG.Proof.MlDsa.Arm.Sign.sepB bs z 1024 h 1024 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs r 1024 h 1024 && decide (z.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && decide (r.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && decide (h.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem hintChk_spec {bs wbs : List (Reg × Nat)} {z r h : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.hintChk bs wbs z r h = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs h 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs z 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs r 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs h 1024 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs z 1024 h 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs r 1024 h 1024 = true ∧ z.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases ∧ r.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases ∧ h.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  simp only [VG.Proof.MlDsa.Arm.Sign.hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem hintArgs_ok {z r h : Ptr} {γ : Nat} (b1 : z.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : r.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b3 : h.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr z, .ptr r, .imm γ, .ptr h].all Arg.ok = true := by
  simp [Arg.ok, b1, b2, b3]

theorem hintPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.Arm.Sign.hintChk (rbs ++ wbs) wbs z r h = true)
    (g0 : E.gpr .r0 = s.gpr z.1 + BitVec.ofNat 32 z.2) (g1 : E.gpr .r1 = s.gpr r.1 + BitVec.ofNat 32 r.2)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 γ) (g3 : E.gpr .r3 = s.gpr h.1 + BitVec.ofNat 32 h.2)
    (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s r)]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s h)])
    (rz : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s z)) (rr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) :
    (makeHintContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, i3, d13, d23, _⟩ := VG.Proof.MlDsa.Arm.Sign.hintChk_spec hc
  sig_pre [makeHintContract, makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w i1 (by decide), En.L.w i2 (by decide), En.L.w i3 (by decide),
    VG.Proof.MlDsa.Arm.Sign.toNat32 (VG.Proof.MlDsa.Arm.Sign.gamma2_lt hγ)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(z, 1024), (r, 1024), (h, 1024)]) (by simp [i1, i2, i3]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.L.fit i3 (by decide), hγ, En.red i1 rz, En.red i2 rr⟩

theorem hintCall_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.Arm.Sign.hintChk (rbs ++ wbs) wbs z r h = true) (rz : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s z))
    (rr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r)) :
    WP isa (callR "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) s fun s' =>
      VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(h, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      HintIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s h) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint γ) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r))] ∧
      (s'.gpr .r0).toNat =
        hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint γ) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s r))] := by
  obtain ⟨w1, i1, i2, i3, _, _, b1, b2, b3⟩ := VG.Proof.MlDsa.Arm.Sign.hintChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok hP.makeHint.ver.1 (by have := hP.makeHint.su; have := hP.makeHint.hS; omega)
    (VG.Proof.MlDsa.Arm.Sign.hintArgs_ok b1 b2 b3) L.sp (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s r)]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s h)])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.hintPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.makeHint.hS; omega) _ _) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.2.2) rfl rfl rz rr)
    (Covers.append_left (Covers.cons (L.cR i1) (L.cR i2)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hA
  sig_post [makeHintContract, makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, e4, Arg.val, k.mem, setWidth_append32, VG.Proof.MlDsa.Arm.Sign.toNat32 (VG.Proof.MlDsa.Arm.Sign.gamma2_lt hγ), L.w i1 (by decide),
    L.w i2 (by decide), L.w i3 (by decide)] at hq
  exact hq

theorem hintCall_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.Arm.Sign.hintChk (rbs ++ wbs) wbs z r h = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x z) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x r)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y z) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y r)))
      (callR "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, b1, b2, b3⟩ := VG.Proof.MlDsa.Arm.Sign.hintChk_spec hc
  have hS : hP.makeHint.S ≤ D := by have := hP.makeHint.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr hP.makeHint.ver.1 hP.makeHint.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.hintArgs_ok b1 b2 b3)
    fun x y x1 y1 ⟨R, ⟨rzx, rrx⟩, ⟨rzy, rry⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.hintPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x h)]) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.2.2) rfl rfl
      rzx rrx,
      VG.Proof.MlDsa.Arm.Sign.hintPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y z), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y r)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y h)]) hγ hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.2.2) rfl rfl
      rzy rry, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (Covers.cons (R.lx.cR i1) (R.lx.cR i2)) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (Covers.cons (R.ly.cR i1) (R.ly.cR i2)) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy
  sig_pub [makeHintContract, makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.eq i3, R.sp,
    and_self]

/-! ## `SimpleBitPack` -/

theorem sbpArgs_ok {f out : Ptr} {b len : Nat} (b1 : f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : out.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr f, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem sbp_lt {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) :
    b < 2 ^ 32 ∧ len < 2 ^ 32 ∧ 0 < len := by
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> subst hl <;> decide

theorem sbpPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 b)
    (g2 : E.gpr .r2 = s.gpr out.1 + BitVec.ofNat 32 out.2) (g3 : E.gpr .r3 = BitVec.ofNat 32 len)
    (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]) (hwr : E.wr = [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩])
    (hle : ∀ i < 256, (coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) i).toNat ≤ b) :
    (simpleBitPackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.sbp_lt hb hl
  sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w i1 (by decide), En.L.w i2 hl0, VG.Proof.MlDsa.Arm.Sign.toNat32 hb', VG.Proof.MlDsa.Arm.Sign.toNat32 hl']
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(f, 1024), (out, len)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 hl0, hb, hl, fun i hi => by rw [En.coeff i1 hi]; exact hle i hi⟩

theorem sbpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(out, len)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s out) len = VG.Spec.MlDsa.simpleBitPack (natPolyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) b := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.sbp_lt hb hl
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok hP.simpleBitPack.ver.1 (by have := hP.simpleBitPack.su; have := hP.simpleBitPack.hS; omega)
    (VG.Proof.MlDsa.Arm.Sign.sbpArgs_ok b1 b2) L.sp (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]) (wr := [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.sbpPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.simpleBitPack.hS; omega) _ _) hb hl hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hA).2.2.2) rfl rfl hle)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hA
  sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, e4, Arg.val, k.mem, VG.Proof.MlDsa.Arm.Sign.toNat32 hb', VG.Proof.MlDsa.Arm.Sign.toNat32 hl', L.w i1 (by decide), L.w i2 hl0] at hq
  exact hq

theorem sbpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  have hS : hP.simpleBitPack.S ≤ D := by have := hP.simpleBitPack.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr hP.simpleBitPack.ver.1 hP.simpleBitPack.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.sbpArgs_ok b1 b2)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.sbpPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] [⟨VG.Proof.MlDsa.Arm.Sign.pa x out, len⟩]) hb hl hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx).2.2.2) rfl rfl rx,
      VG.Proof.MlDsa.Arm.Sign.sbpPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)] [⟨VG.Proof.MlDsa.Arm.Sign.pa y out, len⟩]) hb hl hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.2.1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy).2.2.2) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn4 hAy
  sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsD`. -/
section

/-!
# ML-DSA signing on ARMv7: calls of the encodings with a stack argument

As `Prims.lean`, for `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and
`vg_mldsa_hint_bit_pack`, whose fifth argument is on the stack (`callS`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem sp8 {s E : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (hD : 8 ≤ D) (hsp : E.sp = s.sp - BitVec.ofNat 32 8) :
    E.sp.toNat + 4 ≤ 2 ^ 32 := by
  have := L.sp; have := s.sp.isLt
  rw [hsp, VG.Proof.MlDsa.Arm.Sign.sp_sub8 (by omega)]; omega

/-- The entry state of a stack call, as its preconditions below need it. -/
structure EntS (D : Nat) (rbs wbs : List (Reg × Nat)) (s : State) (S : Nat) (E : State) (v : BitVec 32) : Prop where
  en : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E
  hS : S + 8 ≤ D
  sp : E.sp = s.sp - BitVec.ofNat 32 8
  aa : stackArgAddr E 0 = State.addr s.sp - BitVec.ofNat 64 8
  av : stackArg E 0 = v

theorem entS {s s1 : State} {S : Nat} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs s s1) (hS : S + 8 ≤ D)
    (rd wr : List Region) :
    VG.Proof.MlDsa.Arm.Sign.EntS D rbs wbs s S ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) (s1.gpr .r12) :=
  ⟨VG.Proof.MlDsa.Arm.Sign.ent_S L k hS rd wr, hS, by rw [State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, k.sp],
    (VG.Proof.MlDsa.Arm.Sign.stk_arg L k (by omega) rd wr).1, (VG.Proof.MlDsa.Arm.Sign.stk_arg L k (by omega) rd wr).2⟩

/-! ## `BitPack` -/

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 ∧ 0 < 32 * bitlen (a + b) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
def InRange (m : Mem) (p : Addr) (a b : Nat) : Prop :=
  ∀ i < 256, -(a : Int) ≤ modPm (coeffAt m p i).toNat VG.Spec.MlDsa.q ∧ modPm (coeffAt m p i).toNat VG.Spec.MlDsa.q ≤ b

theorem bpArgs_ok {f out : Ptr} {a b len : Nat} (b1 : f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : out.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr f, .imm a, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem bpPre {S len : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.EntS D rbs wbs s S E (BitVec.ofNat 32 len)) {f out : Ptr} {a b : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 a)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 b) (g3 : E.gpr .r3 = s.gpr out.1 + BitVec.ofNat 32 out.2)
    (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Arm.Sign.argR s]) (hwr : E.wr = [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩])
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (hrg : VG.Proof.MlDsa.Arm.Sign.InRange s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) a b) :
    (bitPackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hD : 8 ≤ D := by have := En.hS; omega
  sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.aa, En.av, En.en.L.w i1 (by decide), En.en.L.w i2 hl0, VG.Proof.MlDsa.Arm.Sign.toNat32 ha', VG.Proof.MlDsa.Arm.Sign.toNat32 hb',
    VG.Proof.MlDsa.Arm.Sign.toNat32 hl']
  refine ⟨VG.Proof.MlDsa.Arm.Sign.wf4 En.en.wf (VG.Proof.MlDsa.Arm.Sign.sp8 En.en.L hD En.sp), hrd, hwr, En.en.L.disj d12, (VG.Proof.MlDsa.Arm.Sign.argR_disj En.en.L hD i2).symm,
    VG.Proof.MlDsa.Arm.Sign.conj_stk [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), ⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩, VG.Proof.MlDsa.Arm.Sign.argR s] ?_, En.en.L.fit i1 (by decide), En.en.L.fit i2 hl0, hp, hl,
    En.en.red i1 hr, fun i hi => by rw [En.en.coeff i1 hi]; exact hrg i hi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.en.stk _ _ i1, En.en.stk _ _ i2, En.sp ▸ VG.Proof.MlDsa.Arm.Sign.argR_stk En.en.L En.hS⟩

theorem bpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (hrg : VG.Proof.MlDsa.Arm.Sign.InRange s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(out, len)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s out) len = VG.Spec.MlDsa.bitPack ((polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)).map fun c => modPm c.val VG.Spec.MlDsa.q) a b := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitPack.hS
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callS_ok hP.bitPack.ver.1 (by have := hP.bitPack.su; omega) (VG.Proof.MlDsa.Arm.Sign.bpArgs_ok b1 b2) L.sp
    (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]) (wr := [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩])
    (fun s1 hA k => by
      obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
      have En := VG.Proof.MlDsa.Arm.Sign.entS (S := hP.bitPack.S) L k hS ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩]
      rw [e4] at En
      exact VG.Proof.MlDsa.Arm.Sign.bpPre En hp hl hc (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
        (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl hr hrg)
    (L.cR i1) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
  have En := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.bitPack.S) L k hS ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩]
  obtain ⟨-, av⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg L k (by omega) ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩]
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s out, len⟩] with hE
  have g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2 := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 a := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 b := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr out.1 + BitVec.ofNat 32 out.2 := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl
  rw [e4] at av
  have ep := En.poly i1
  clear_value E
  sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, av, hm₂, VG.Proof.MlDsa.Arm.Sign.toNat32 ha', VG.Proof.MlDsa.Arm.Sign.toNat32 hb', VG.Proof.MlDsa.Arm.Sign.toNat32 hl', L.w i1 (by decide), L.w i2 hl0,
    Arg.val, ep] at hq
  exact hq

theorem bpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ VG.Proof.MlDsa.Arm.Sign.InRange x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) a b) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) ∧ VG.Proof.MlDsa.Arm.Sign.InRange y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitPack.hS
  have pre : ∀ {x x1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs x) (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1)
      (hA : VG.Proof.MlDsa.Arm.Sign.ArgsIn [.ptr f, .imm a, .imm b, .ptr out, .imm len] x x1) (hr : Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f))
      (hrg : VG.Proof.MlDsa.Arm.Sign.InRange x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) a b),
      (bitPackContract Arm.abi hP.bitPack.S).pre
        ((pushed [.r12, .lr] x1).callEntry.withRegions ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x out, len⟩]) := by
    intro x x1 L k hA hr hrg
    obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
    have En := VG.Proof.MlDsa.Arm.Sign.entS (S := hP.bitPack.S) L k hS ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x out, len⟩]
    rw [e4] at En
    exact VG.Proof.MlDsa.Arm.Sign.bpPre En hp hl hc (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl hr hrg
  refine VG.Proof.MlDsa.Arm.Sign.callS_tr hP.bitPack.ver.1 hP.bitPack.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.bpArgs_ok b1 b2) (fun x y h => h.1.sp)
    fun x y x1 y1 ⟨R, ⟨rx, gx⟩, ⟨ry, gy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, pre R.lx kx hAx rx gx, pre R.ly ky hAy ry gy, ?_,
      (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).1, (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).2,
      (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).1, (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).2⟩
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAx
  obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAy
  obtain ⟨-, vx⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.lx kx (by omega) ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x out, len⟩]
  obtain ⟨-, vy⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.ly ky (by omega) ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) [⟨VG.Proof.MlDsa.Arm.Sign.pa y out, len⟩]
  set X := (pushed [.r12, .lr] x1).callEntry.withRegions ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x out, len⟩] with hX
  set Y := (pushed [.r12, .lr] y1).callEntry.withRegions ([VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)] ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) [⟨VG.Proof.MlDsa.Arm.Sign.pa y out, len⟩] with hY
  have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
    intro r hr; rw [hX, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
  have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
    intro r hr; rw [hY, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
  have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, kx.sp]
  have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, ky.sp]
  clear_value X Y
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
    gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
    hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `BitUnpack` -/

theorem bupArgs_ok {v f : Ptr} {a b len : Nat} (b1 : v.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr v, .imm len, .imm a, .imm b, .ptr f].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem bupPre {S : Nat} {s E : State} {v f : Ptr} (En : VG.Proof.MlDsa.Arm.Sign.EntS D rbs wbs s S E (s.gpr f.1 + BitVec.ofNat 32 f.2))
    {a b len : Nat} (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs v len f 1024 = true)
    (g0 : E.gpr .r0 = s.gpr v.1 + BitVec.ofNat 32 v.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 len)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 a) (g3 : E.gpr .r3 = BitVec.ofNat 32 b)
    (hrd : E.rd = [⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩, VG.Proof.MlDsa.Arm.Sign.argR s]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]) :
    (bitUnpackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hD : 8 ≤ D := by have := En.hS; omega
  sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.aa, En.av, En.en.L.w i1 hl0, En.en.L.w i2 (by decide), VG.Proof.MlDsa.Arm.Sign.toNat32 ha', VG.Proof.MlDsa.Arm.Sign.toNat32 hb',
    VG.Proof.MlDsa.Arm.Sign.toNat32 hl']
  refine ⟨VG.Proof.MlDsa.Arm.Sign.wf4 En.en.wf (VG.Proof.MlDsa.Arm.Sign.sp8 En.en.L hD En.sp), hrd, hwr, En.en.L.disj d12, (VG.Proof.MlDsa.Arm.Sign.argR_disj En.en.L hD i2).symm,
    VG.Proof.MlDsa.Arm.Sign.conj_stk [⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩, VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Arm.Sign.argR s] ?_, En.en.L.fit i1 hl0, En.en.L.fit i2 (by decide), hp, hl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.en.stk _ _ i1, En.en.stk _ _ i2, En.sp ▸ VG.Proof.MlDsa.Arm.Sign.argR_stk En.en.L En.hS⟩

theorem bupAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s v) len) a b)) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitUnpack.hS
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callS_ok hP.bitUnpack.ver.1 (by have := hP.bitUnpack.su; omega) (VG.Proof.MlDsa.Arm.Sign.bupArgs_ok b1 b2) L.sp
    (rd := [⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)])
    (fun s1 hA k => by
      obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
      have En := VG.Proof.MlDsa.Arm.Sign.entS (S := hP.bitUnpack.S) L k hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]
      rw [e4] at En
      exact VG.Proof.MlDsa.Arm.Sign.bupPre En hp hl hc (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
        (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl)
    (L.cR i1) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
  have En := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.bitUnpack.S) L k hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]
  obtain ⟨-, av⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg L k (by omega) ([⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)]
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa s v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f)] with hE
  have g0 : E.gpr .r0 = s.gpr v.1 + BitVec.ofNat 32 v.2 := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 len := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 a := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl
  have g3 : E.gpr .r3 = BitVec.ofNat 32 b := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl
  rw [e4] at av
  have eb := En.bytes i1
  clear_value E
  sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, av, hm₂, VG.Proof.MlDsa.Arm.Sign.toNat32 ha', VG.Proof.MlDsa.Arm.Sign.toNat32 hb', VG.Proof.MlDsa.Arm.Sign.toNat32 hl', L.w i1 hl0, L.w i2 (by decide),
    Arg.val, eb] at hq
  exact hq

theorem bupAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := VG.Proof.MlDsa.Arm.Sign.bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitUnpack.hS
  have pre : ∀ {x x1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs x) (k : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1)
      (hA : VG.Proof.MlDsa.Arm.Sign.ArgsIn [.ptr v, .imm len, .imm a, .imm b, .ptr f] x x1),
      (bitUnpackContract Arm.abi hP.bitUnpack.S).pre
        ((pushed [.r12, .lr] x1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa x v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)]) := by
    intro x x1 L k hA
    obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
    have En := VG.Proof.MlDsa.Arm.Sign.entS (S := hP.bitUnpack.S) L k hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa x v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)]
    rw [e4] at En
    exact VG.Proof.MlDsa.Arm.Sign.bupPre En hp hl hc (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl
  refine VG.Proof.MlDsa.Arm.Sign.callS_tr hP.bitUnpack.ver.1 hP.bitUnpack.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.bupArgs_ok b1 b2) (fun x y h => h.sp)
    fun x y x1 y1 R ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, pre R.lx kx hAx, pre R.ly ky hAy, ?_,
      (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).1, (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).2,
      (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).1, (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).2⟩
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAx
  obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAy
  obtain ⟨-, vx⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.lx kx (by omega) ([⟨VG.Proof.MlDsa.Arm.Sign.pa x v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)]
  obtain ⟨-, vy⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.ly ky (by omega) ([⟨VG.Proof.MlDsa.Arm.Sign.pa y v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)]
  set X := (pushed [.r12, .lr] x1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa x v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f)] with hX
  set Y := (pushed [.r12, .lr] y1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa y v, len⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR y]) [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f)] with hY
  have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
    intro r hr; rw [hX, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
  have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
    intro r hr; rw [hY, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
  have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, kx.sp]
  have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, ky.sp]
  clear_value X Y
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
    gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
    hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `HintBitPack` -/

theorem hbpArgs_ok {h y : Ptr} {hlen ω len : Nat} (b1 : h.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) (b2 : y.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) :
    [Arg.ptr h, .imm hlen, .imm ω, .ptr y, .imm len].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hintParams_pos {ω k : Nat} (h : (ω, k) ∈ hintParams) : 0 < k := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpPre {S : Nat} {s E : State} {ω k : Nat} (En : VG.Proof.MlDsa.Arm.Sign.EntS D rbs wbs s S E (BitVec.ofNat 32 (ω + k))) {h y : Ptr}
    (hp : (ω, k) ∈ hintParams) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 (256 * k))
    (g2 : E.gpr .r2 = BitVec.ofNat 32 ω) (g3 : E.gpr .r3 = s.gpr y.1 + BitVec.ofNat 32 y.2)
    (hrd : E.rd = [⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩, VG.Proof.MlDsa.Arm.Sign.argR s]) (hwr : E.wr = [⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩])
    (hones : hintOnes (hintAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s h) k) ≤ ω) :
    (hintBitPackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.Arm.Sign.hintParams_lt hp
  have k0 := VG.Proof.MlDsa.Arm.Sign.hintParams_pos hp
  have hD : 8 ≤ D := by have := En.hS; omega
  have ek : ω + k - ω = k := by omega
  have i1' : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  sig_pre [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.aa, En.av, En.en.L.w i1 (by omega), En.en.L.w i2 (by omega), VG.Proof.MlDsa.Arm.Sign.toNat32 h1,
    VG.Proof.MlDsa.Arm.Sign.toNat32 h2, VG.Proof.MlDsa.Arm.Sign.toNat32 h3, ek]
  refine ⟨VG.Proof.MlDsa.Arm.Sign.wf4 En.en.wf (VG.Proof.MlDsa.Arm.Sign.sp8 En.en.L hD En.sp), hrd, hwr, En.en.L.disj d12, (VG.Proof.MlDsa.Arm.Sign.argR_disj En.en.L hD i2).symm,
    VG.Proof.MlDsa.Arm.Sign.conj_stk [⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩, ⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩, VG.Proof.MlDsa.Arm.Sign.argR s] ?_, En.en.L.fit i1 (by omega), En.en.L.fit i2 (by omega),
    hp, by omega, trivial, by rw [En.en.hint i1']; exact hones⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.en.stk _ _ i1, En.en.stk _ _ i2, En.sp ▸ VG.Proof.MlDsa.Arm.Sign.argR_stk En.en.L En.hS⟩

theorem hbpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(y, ω + k)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s y) (ω + k) = VG.Spec.MlDsa.hintBitPack ω k (hintAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s h) k) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.Arm.Sign.hintParams_lt hp
  have k0 := VG.Proof.MlDsa.Arm.Sign.hintParams_pos hp
  have ek : ω + k - ω = k := by omega
  have i1' : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  have hS := hP.hintBitPack.hS
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callS_ok hP.hintBitPack.ver.1 (by have := hP.hintBitPack.su; omega) (VG.Proof.MlDsa.Arm.Sign.hbpArgs_ok b1 b2) L.sp
    (rd := [⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩]) (wr := [⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩])
    (fun s1 hA k' => by
      obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
      have En := VG.Proof.MlDsa.Arm.Sign.entS (S := hP.hintBitPack.S) L k' hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩]
      rw [e4] at En
      exact VG.Proof.MlDsa.Arm.Sign.hbpPre En hp hc (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
        (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl hones)
    (L.cR i1) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k', s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
  have En := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.hintBitPack.S) L k' hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩]
  obtain ⟨-, av⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg L k' (by omega) ([⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩]
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa s h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR s]) [⟨VG.Proof.MlDsa.Arm.Sign.pa s y, ω + k⟩]
    with hE
  have g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2 := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 ω := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr y.1 + BitVec.ofNat 32 y.2 := by rw [hE, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl
  rw [e4] at av
  have eh := En.hint i1'
  clear_value E
  sig_post [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g2, g3, av, hm₂, VG.Proof.MlDsa.Arm.Sign.toNat32 h1, VG.Proof.MlDsa.Arm.Sign.toNat32 h2, ek, L.w i1 (by omega), L.w i2 (by omega), Arg.val,
    eh] at hq
  exact hq

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : VG.Proof.MlDsa.Arm.Sign.rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (VG.Proof.MlDsa.Arm.Sign.pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (VG.Proof.MlDsa.Arm.Sign.pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := VG.Proof.MlDsa.Arm.Sign.rwChk_spec hc
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.Arm.Sign.hintParams_lt hp
  have k0 := VG.Proof.MlDsa.Arm.Sign.hintParams_pos hp
  have hS := hP.hintBitPack.hS
  have pre : ∀ {x x1 : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs x) (k' : VG.Proof.MlDsa.Arm.Sign.Keep VG.Proof.MlDsa.Arm.Sign.argRegs x x1)
      (hA : VG.Proof.MlDsa.Arm.Sign.ArgsIn [.ptr h, .imm (256 * k), .imm ω, .ptr y, .imm (ω + k)] x x1)
      (hones : hintOnes (hintAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x h) k) ≤ ω),
      (hintBitPackContract Arm.abi hP.hintBitPack.S).pre
        ((pushed [.r12, .lr] x1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa x h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x y, ω + k⟩]) := by
    intro x x1 L k' hA hones
    obtain ⟨e0, e1, e2, e3, e4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hA
    have En := VG.Proof.MlDsa.Arm.Sign.entS (S := hP.hintBitPack.S) L k' hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa x h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x y, ω + k⟩]
    rw [e4] at En
    exact VG.Proof.MlDsa.Arm.Sign.hbpPre En hp hc (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0, e0]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1, e1]; rfl)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2, e2]; rfl) (by rw [VG.Proof.MlDsa.Arm.Sign.vS _ _ _ VG.Proof.MlDsa.Arm.Sign.nl3, e3]; rfl) rfl rfl hones
  refine VG.Proof.MlDsa.Arm.Sign.callS_tr hP.hintBitPack.ver.1 hP.hintBitPack.ver.2.1 (VG.Proof.MlDsa.Arm.Sign.hbpArgs_ok b1 b2) (fun x z h => h.1.sp)
    fun x z x1 z1 ⟨R, ox, oz, hl⟩ ⟨hAx, kx⟩ ⟨hAz, kz⟩ =>
    ⟨_, _, _, _, pre R.lx kx hAx ox, pre R.ly kz hAz oz, ?_,
      (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).1, (VG.Proof.MlDsa.Arm.Sign.cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).2,
      (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly kz (by omega) (R.ly.cR i1) (R.ly.cW w1)).1, (VG.Proof.MlDsa.Arm.Sign.cov_S R.ly kz (by omega) (R.ly.cR i1) (R.ly.cW w1)).2⟩
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAx
  obtain ⟨hz0, hz1, hz2, hz3, hz4⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn5 hAz
  have Ex := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.hintBitPack.S) R.lx kx hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa x h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x y, ω + k⟩]
  have Ez := VG.Proof.MlDsa.Arm.Sign.ent_S (S := hP.hintBitPack.S) R.ly kz hS ([⟨VG.Proof.MlDsa.Arm.Sign.pa z h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR z]) [⟨VG.Proof.MlDsa.Arm.Sign.pa z y, ω + k⟩]
  obtain ⟨-, vx⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.lx kx (by omega) ([⟨VG.Proof.MlDsa.Arm.Sign.pa x h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x y, ω + k⟩]
  obtain ⟨-, vz⟩ := VG.Proof.MlDsa.Arm.Sign.stk_arg R.ly kz (by omega) ([⟨VG.Proof.MlDsa.Arm.Sign.pa z h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR z]) [⟨VG.Proof.MlDsa.Arm.Sign.pa z y, ω + k⟩]
  set X := (pushed [.r12, .lr] x1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa x h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR x]) [⟨VG.Proof.MlDsa.Arm.Sign.pa x y, ω + k⟩]
    with hX
  set Z := (pushed [.r12, .lr] z1).callEntry.withRegions ([⟨VG.Proof.MlDsa.Arm.Sign.pa z h, 256 * k * 4⟩] ++ [VG.Proof.MlDsa.Arm.Sign.argR z]) [⟨VG.Proof.MlDsa.Arm.Sign.pa z y, ω + k⟩]
    with hZ
  have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
    intro r hr; rw [hX, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
  have gz : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Z.gpr r = z1.gpr r := by
    intro r hr; rw [hZ, VG.Proof.MlDsa.Arm.Sign.vS _ _ _ (by revert hr; decide +revert)]
  have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, kx.sp]
  have sz : Z.sp = z.sp - BitVec.ofNat 32 8 := by rw [hZ, State.withRegions_sp, State.callEntry_sp, VG.Proof.MlDsa.Arm.Sign.pushed_sp8, kz.sp]
  have cx := Ex.coeffs (len := 256 * k) (p := h) (by rw [show 256 * k * 4 = 256 * k * 4 from rfl]; exact i1)
  have cz := Ez.coeffs (len := 256 * k) (p := h) i1
  clear_value X Z
  sig_pub [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
    gz .r0 (by decide), gz .r1 (by decide), gz .r2 (by decide), gz .r3 (by decide), sx, sz,
    hx0, hx1, hx2, hx3, hz0, hz1, hz2, hz3, vx, vz, hx4, hz4, Arg.val, VG.Proof.MlDsa.Arm.Sign.toNat32 h3]
  rw [R.lx.w i1 (by omega), R.ly.w i1 (by omega), cx, cz, hl]
  simp only [R.eq i1, R.eq i2, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsB`. -/
section

/-!
# ML-DSA signing on ARMv7: calls of the NTTs, products and two samplers

As `Prims.lean`, for `vg_mldsa_ntt`, `vg_mldsa_inv_ntt`,
`vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`, `vg_mldsa_rej_ntt_poly`
and `vg_mldsa_expand_mask_poly`. `RejNTTPoly`'s result is public in two runs
whose seeds agree (`rejCall_tr`), and it succeeds only if the algorithm
finishes within `maxBounds` (`rejCall_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of an in-place transformation of `f` needs of the layout. -/
def ipChk (bs wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs f 1024 && VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 1024 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs f 1024 (sc oPS) 1024 && decide (f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem ipChk_spec {bs wbs : List (Reg × Nat)} {f : Ptr} (h : VG.Proof.MlDsa.Arm.Sign.ipChk bs wbs f = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs f 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oPS) 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs (sc oPS) 1024 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs f 1024 (sc oPS) 1024 = true ∧ ([Arg.ptr f, .ptr (sc oPS)].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.ipChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, by simp [Arg.ok, h.2]⟩

theorem ipPre {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {f : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (g1 : E.gpr .r1 = s.gpr .r7 + BitVec.ofNat 32 oPS) (hrd : E.rd = [])
    (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS))]) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    (inPlaceContract Arm.abi t S).pre E := by
  obtain ⟨_, _, i1, i2, d12, _⟩ := VG.Proof.MlDsa.Arm.Sign.ipChk_spec hc
  sig_pre [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, En.L.w i1 (by decide), En.L.w (p := sc oPS) i2 (by decide)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(f, 1024), (sc oPS, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit (p := sc oPS) i2 (by decide), En.red i1 hr⟩

theorem ipAt_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => inPlaceContract Arm.abi t S) 0 D c) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    WP isa (callR n c [.ptr f, .ptr (sc oPS)]) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧
      VG.Proof.MlDsa.Arm.Sign.CS s s' ∧ PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f))) := by
  obtain ⟨w1, w2, i1, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.ipChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) ok L.sp
    (rd := []) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s (sc oPS))])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.ipPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := C.hS; omega) _ _) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hA).2) rfl rfl hr)
    (Covers.append_left Covers.nil (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, _⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hA
  sig_post [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, Arg.val, k.mem, L.w i1 (by decide)] at hq
  exact hq

theorem ipAt_tr {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa}
    (C : VG.Proof.MlDsa.Arm.Sign.Callee (fun S => inPlaceContract Arm.abi t S) 0 D c) {f : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f))
      (callR n c [.ptr f, .ptr (sc oPS)]) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.ipChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr C.ver.1 C.ver.2.1 ok fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.ipPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x (sc oPS))]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx).2) rfl rfl rx,
      VG.Proof.MlDsa.Arm.Sign.ipPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y (sc oPS))]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy).2) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left Covers.nil (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact Covers.append_left Covers.nil (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn2 hAy
  sig_pub [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

theorem nttAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    WP isa (nttAt P f) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (VG.Spec.MlDsa.ntt (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f))) :=
  VG.Proof.MlDsa.Arm.Sign.ipAt_ok hP.ntt L hc hr

theorem invNttAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    WP isa (invNttAt P f) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s f) (VG.Spec.MlDsa.nttInv (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f))) :=
  VG.Proof.MlDsa.Arm.Sign.ipAt_ok hP.invNtt L hc hr

theorem nttAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f))
      (nttAt P f) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.ipAt_tr hP.ntt hc

theorem invNttAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {f : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f))
      (invNttAt P f) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.ipAt_tr hP.invNtt hc

/-! ## Products -/

/-- What a call of `vg_mldsa_multiply_ntt` or `vg_mldsa_multiply_add_ntt` on
`h`, `f`, `g` needs of the layout. -/
def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB wbs h 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs h 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 && VG.Proof.MlDsa.Arm.Sign.inB bs g 1024 && VG.Proof.MlDsa.Arm.Sign.sepB bs h 1024 f 1024 &&
    VG.Proof.MlDsa.Arm.Sign.sepB bs h 1024 g 1024 && decide (h.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && decide (f.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases) && decide (g.1 ∈ VG.Proof.MlDsa.Arm.Sign.bases)

theorem mulChk_spec {bs wbs : List (Reg × Nat)} {h f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.mulChk bs wbs h f g = true) :
    VG.Proof.MlDsa.Arm.Sign.inB wbs h 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs h 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs f 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.inB bs g 1024 = true ∧
      VG.Proof.MlDsa.Arm.Sign.sepB bs h 1024 f 1024 = true ∧ VG.Proof.MlDsa.Arm.Sign.sepB bs h 1024 g 1024 = true ∧
      ([Arg.ptr h, .ptr f, .ptr g].all Arg.ok) = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.mulChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [Arg.ok, h7, h8, h9]⟩

theorem mulPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {h f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.mulChk (rbs ++ wbs) wbs h f g = true) (g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2)
    (g1 : E.gpr .r1 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g2 : E.gpr .r2 = s.gpr g.1 + BitVec.ofNat 32 g.2)
    (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s g)]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s h)])
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    (mulContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := VG.Proof.MlDsa.Arm.Sign.mulChk_spec hc
  sig_pre [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w i1 (by decide), En.L.w i2 (by decide), En.L.w i3 (by decide)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13,
    En.conj (bs := [(h, 1024), (f, 1024), (g, 1024)]) (by simp [i1, i2, i3]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.L.fit i3 (by decide), En.red i2 rf, En.red i3 rg⟩

theorem mulAddPre {S : Nat} {s E : State} (En : VG.Proof.MlDsa.Arm.Sign.Ent D rbs wbs s S E) {h f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.mulChk (rbs ++ wbs) wbs h f g = true) (g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2)
    (g1 : E.gpr .r1 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g2 : E.gpr .r2 = s.gpr g.1 + BitVec.ofNat 32 g.2)
    (hrd : E.rd = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s g)]) (hwr : E.wr = [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s h)])
    (rh : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s h)) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    (mulAddContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := VG.Proof.MlDsa.Arm.Sign.mulChk_spec hc
  sig_pre [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w i1 (by decide), En.L.w i2 (by decide), En.L.w i3 (by decide)]
  exact ⟨VG.Proof.MlDsa.Arm.Sign.wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13,
    En.conj (bs := [(h, 1024), (f, 1024), (g, 1024)]) (by simp [i1, i2, i3]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.L.fit i3 (by decide), En.red i1 rh, En.red i2 rf,
    En.red i3 rg⟩

theorem mulAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {h f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.mulChk (rbs ++ wbs) wbs h f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    WP isa (mulAt P h f g) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(h, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s h) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.mulChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok hP.mul.ver.1 (by have := hP.mul.su; have := hP.mul.hS; omega) ok L.sp
    (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s g)]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s h)])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.mulPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.mul.hS; omega) _ _) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.2) rfl rfl rf rg)
    (Covers.append_left (Covers.cons (L.cR i2) (L.cR i3)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hA
  sig_post [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide), L.w i3 (by decide)] at hq
  exact hq

theorem mulAddAt_ok {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {h f g : Ptr}
    (hc : VG.Proof.MlDsa.Arm.Sign.mulChk (rbs ++ wbs) wbs h f g = true) (rh : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s h)) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f))
    (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(h, 1024)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s h)
        (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s h)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s g)))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.mulChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.callR_ok hP.mulAdd.ver.1 (by have := hP.mulAdd.su; have := hP.mulAdd.hS; omega) ok L.sp
    (rd := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s g)]) (wr := [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa s h)])
    (fun s1 hA k => VG.Proof.MlDsa.Arm.Sign.mulAddPre (VG.Proof.MlDsa.Arm.Sign.ent_R L k (by have := hP.mulAdd.hS; omega) _ _) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hA).2.2) rfl rfl rh rf rg)
    (Covers.append_left (Covers.cons (L.cR i2) (L.cR i3)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hA
  sig_post [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide), L.w i3 (by decide)] at hq
  exact hq

theorem mulAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {h f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y g))) (mulAt P h f g) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.mulChk_spec hc
  have hS : hP.mul.S ≤ D := by have := hP.mul.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr hP.mul.ver.1 hP.mul.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.mulPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x h)]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.2) rfl rfl rfx rgx,
      VG.Proof.MlDsa.Arm.Sign.mulPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y h)]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.2) rfl rfl rfy rgy, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (Covers.cons (R.lx.cR i2) (R.lx.cR i3)) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (Covers.cons (R.ly.cR i2) (R.ly.cR i3)) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy
  sig_pub [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.eq i1, R.eq i2, R.eq i3, R.sp, and_self]

theorem mulAddAt_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {h f g : Ptr} (hc : VG.Proof.MlDsa.Arm.Sign.mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D rbs wbs x y ∧
      (Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x h) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y h) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y g))) (mulAddAt P h f g)
      fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := VG.Proof.MlDsa.Arm.Sign.mulChk_spec hc
  have hS : hP.mulAdd.S ≤ D := by have := hP.mulAdd.hS; omega
  refine VG.Proof.MlDsa.Arm.Sign.callR_tr hP.mulAdd.ver.1 hP.mulAdd.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rhx, rfx, rgx⟩, ⟨rhy, rfy, rgy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, VG.Proof.MlDsa.Arm.Sign.mulAddPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.lx kx hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa x h)]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx).2.2) rfl rfl rhx rfx rgx,
      VG.Proof.MlDsa.Arm.Sign.mulAddPre (VG.Proof.MlDsa.Arm.Sign.ent_R R.ly ky hS [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y f), VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y g)] [VG.Proof.MlDsa.Sign.pR (VG.Proof.MlDsa.Arm.Sign.pa y h)]) hc
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl0]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).1) (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl1]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.1)
      (by rw [VG.Proof.MlDsa.Arm.Sign.vR _ _ _ VG.Proof.MlDsa.Arm.Sign.nl2]; exact (VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy).2.2) rfl rfl rhy rfy rgy, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (Covers.cons (R.lx.cR i2) (R.lx.cR i3)) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (Covers.cons (R.ly.cR i2) (R.ly.cR i3)) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := VG.Proof.MlDsa.Arm.Sign.argsIn3 hAy
  sig_pub [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.eq i1, R.eq i2, R.eq i3, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseD`. -/
section

/-!
# ML-DSA signing on ARMv7: the private key and `ρ″`

Once `Â` is sampled (`IM`), `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`dec_ok`), in their slots (`ID`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` at `MS` (`decode_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
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
abbrev S1v (σ : State) (r : Nat) : VG.Spec.MlDsa.Poly := s1F p (VG.Proof.MlDsa.Arm.Sign.skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : VG.Spec.MlDsa.Poly := s2F p (VG.Proof.MlDsa.Arm.Sign.skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : VG.Spec.MlDsa.Poly := t0F p (VG.Proof.MlDsa.Arm.Sign.skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := VG.Spec.MlDsa.H (((VG.Proof.MlDsa.Arm.Sign.skOf p σ).drop 32).take 32 ++ VG.Proof.MlDsa.Arm.Sign.rndOf σ ++ VG.Proof.MlDsa.Arm.Sign.muOf σ) 64

end

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (D : Nat) (σ s : State) : Prop where
  st : VG.Proof.MlDsa.Arm.Sign.St p D σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.seedE p σ e)).isSome
  A : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.aBase p) (p.k * p.ℓ) (VG.Proof.MlDsa.Arm.Sign.aVal p σ)

def imChk (p : Params) (ws : List (Ptr × Nat)) : Bool := VG.Proof.MlDsa.Arm.Sign.stChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.aBase p) (p.k * p.ℓ)

theorem IM.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Sign.IM p D σ s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.imChk p ws = true) : VG.Proof.MlDsa.Arm.Sign.IM p D σ s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.imChk, Bool.and_eq_true] at hc
  exact ⟨h.st.step hP hc.1, h.ok, Fam.keep h.st.lay hP hc.2 h.A⟩

theorem IA.im {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Sign.IA p D σ (p.k * p.ℓ) s) (h1 : s.gpr .r11 = 1) :
    VG.Proof.MlDsa.Arm.Sign.IM p D σ s := ⟨h.st, (h.ok h1).1, (h.ok h1).2⟩

/-! ## The private key -/

/-- `Â`, the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (D : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  im : VG.Proof.MlDsa.Arm.Sign.IM p D σ s
  s1 : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.s1Base p) a (VG.Proof.MlDsa.Arm.Sign.S1v p σ)
  s2 : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.s2Base p) b (VG.Proof.MlDsa.Arm.Sign.S2v p σ)
  t0 : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.t0Base p) c (VG.Proof.MlDsa.Arm.Sign.T0v p σ)

def idChk (p : Params) (ws : List (Ptr × Nat)) (a b c : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.imChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.s1Base p) a && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.s2Base p) b && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.t0Base p) c

theorem ID.step {p : Params} {D : Nat} {σ s s' : State} {a b c : Nat} (h : VG.Proof.MlDsa.Arm.Sign.ID p D σ a b c s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.idChk p ws a b c = true) : VG.Proof.MlDsa.Arm.Sign.ID p D σ a b c s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.idChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.im.st.lay
  exact ⟨h.im.step hP h1, Fam.keep L hP h2 h.s1, Fam.keep L hP h3 h.s2, Fam.keep L hP h4 h.t0⟩

theorem pS_bases (j : Nat) : (pS j).1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := List.mem_cons_self ..

theorem sc_bases (o : Nat) : (sc o).1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := List.mem_cons_self ..

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Sign.St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (.r4, o)) len = ((VG.Proof.MlDsa.Arm.Sign.skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, ← VG.Proof.MlDsa.Arm.Sign.pa_add, Nat.zero_add]

/-- What decoding a polynomial of `len` bytes at `src` to slot `j` needs of the layout. -/
def decChk (p : Params) (a b c : Nat) (src : Ptr) (len j : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.rwChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) src len (pS j) 1024 && VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (pS j) &&
    VG.Proof.MlDsa.Arm.Sign.idChk p [(pS j, 1024)] a b c && VG.Proof.MlDsa.Arm.Sign.idChk p [(pS j, 1024), (sc oPS, 1024)] a b c

theorem dec_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {a b c : Nat} {src : Ptr}
    {len x y j : Nat} (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y))
    (hc : VG.Proof.MlDsa.Arm.Sign.decChk p a b c src len j = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.ID p D σ a b c s) :
    WP isa (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) s fun s' =>
      VG.Proof.MlDsa.Arm.Sign.ID p D σ a b c s' ∧ VG.Proof.MlDsa.Arm.Sign.Pl s' j (VG.Spec.MlDsa.ntt (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s src) len) x y))) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.bupAt_ok hP h.im.st.lay hp hl h1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 h3
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.ntt I1.im.st.lay h2 (by rw [hP1.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases j)]; exact hq1.1))
    fun s2 ⟨hP2, _, hq2⟩ => ⟨I1.step hP2 h4, ?_⟩
  show PolyIs s2.mem (VG.Proof.MlDsa.Arm.Sign.pa s2 (pS j)) _
  rw [hP2.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases j), hP1.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases j), ← hq1.2]
  rw [hP1.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases j)] at hq2
  exact hq2

/-- What `decode` needs of the layout. -/
def dChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun r => VG.Proof.MlDsa.Arm.Sign.decChk p r 0 0 (.r4, skS1 p r) (sLen p) (VG.Proof.MlDsa.Arm.Sign.s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => VG.Proof.MlDsa.Arm.Sign.decChk p p.ℓ i 0 (.r4, skS2 p i) (sLen p) (VG.Proof.MlDsa.Arm.Sign.s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => VG.Proof.MlDsa.Arm.Sign.decChk p p.ℓ p.k i (.r4, skT0 p i) 416 (VG.Proof.MlDsa.Arm.Sign.t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    VG.Proof.MlDsa.Arm.Sign.shakeChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) [((.r4, 32), 32), ((.r6, 0), 32), ((.r5, 0), 64)] (sc oMS) 64 &&
    VG.Proof.MlDsa.Arm.Sign.idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Decoded: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″` at `MS`. -/
structure IK (p : Params) (D : Nat) (σ s : State) : Prop where
  d : VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oMS)) 64 = VG.Proof.MlDsa.Arm.Sign.rppOf p σ

theorem dChk_spec {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.dChk p = true) :
    (∀ r < p.ℓ, VG.Proof.MlDsa.Arm.Sign.decChk p r 0 0 (.r4, skS1 p r) (sLen p) (VG.Proof.MlDsa.Arm.Sign.s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, VG.Proof.MlDsa.Arm.Sign.decChk p p.ℓ i 0 (.r4, skS2 p i) (sLen p) (VG.Proof.MlDsa.Arm.Sign.s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, VG.Proof.MlDsa.Arm.Sign.decChk p p.ℓ p.k i (.r4, skT0 p i) 416 (VG.Proof.MlDsa.Arm.Sign.t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    VG.Proof.MlDsa.Arm.Sign.shakeChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) [((.r4, 32), 32), ((.r6, 0), 32), ((.r5, 0), 64)] (sc oMS) 64 = true ∧
    VG.Proof.MlDsa.Arm.Sign.idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k = true ∧ VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oMS) 64 = true ∧
    (p.η, p.η) ∈ bitPackParams ∧ 64 ≤ p.skLen := by
  simp only [VG.Proof.MlDsa.Arm.Sign.dChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hη⟩, hsk⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, hη, hsk⟩

theorem sLen_eq (p : Params) : sLen p = 32 * bitlen (p.η + p.η) := by rw [← Nat.two_mul]

section
variable {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.dChk p = true) {σ : State}
include hP hc

theorem decS1_ok {r : Nat} (hr : r < p.ℓ) {s : State} (hs : VG.Proof.MlDsa.Arm.Sign.ID p D σ r 0 0 s) :
    WP isa (decS1 P p r) s (VG.Proof.MlDsa.Arm.Sign.ID p D σ (r + 1) 0 0) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.Arm.Sign.dChk_spec hc).1 r hr
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.dec_ok hP (VG.Proof.MlDsa.Arm.Sign.dChk_spec hc).2.2.2.2.2.2.1 (VG.Proof.MlDsa.Arm.Sign.sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, Fam.snoc I'.s1 ?_, I'.s2, I'.t0⟩
  rw [VG.Proof.MlDsa.Arm.Sign.sk_slice hs.im.st ck] at hq
  exact hq

theorem decS2_ok {i : Nat} (hi : i < p.k) {s : State} (hs : VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ i 0 s) :
    WP isa (decS2 P p i) s (VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ (i + 1) 0) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.Arm.Sign.dChk_spec hc).2.1 i hi
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.dec_ok hP (VG.Proof.MlDsa.Arm.Sign.dChk_spec hc).2.2.2.2.2.2.1 (VG.Proof.MlDsa.Arm.Sign.sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, I'.s1, Fam.snoc I'.s2 ?_, I'.t0⟩
  rw [VG.Proof.MlDsa.Arm.Sign.sk_slice hs.im.st ck] at hq
  exact hq

theorem decT0_ok {i : Nat} (hi : i < p.k) {s : State} (hs : VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k i s) :
    WP isa (decT0 P p i) s (VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k (i + 1)) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.Arm.Sign.dChk_spec hc).2.2.1 i hi
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.dec_ok hP (by decide) (by decide) c hs) fun s' ⟨I', hq⟩ => ⟨I'.im, I'.s1, I'.s2,
    Fam.snoc I'.t0 ?_⟩
  have e : skT0 p i = 128 + lenS p * p.ℓ + lenS p * p.k + 32 * 13 * i := by
    unfold skT0 lenS sLen; rw [Nat.mul_add]; omega
  rw [VG.Proof.MlDsa.Arm.Sign.sk_slice hs.im.st ck, e] at hq
  exact hq

theorem rpp_ok {s : State} (hs : VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k p.k s) :
    WP isa (shakeAt [((.r4, 32), 32), ((.r6, 0), 32), ((.r5, 0), 64)] (sc oMS) 64) s (VG.Proof.MlDsa.Arm.Sign.IK p D σ) := by
  obtain ⟨_, _, _, h4, h5, _, _, hsk⟩ := VG.Proof.MlDsa.Arm.Sign.dChk_spec hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.shake_ok (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hP.hD h4 hs.im.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs.step hP4 h5, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [VG.Proof.MlDsa.Arm.Sign.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [VG.Proof.MlDsa.Arm.Sign.sk_slice hs.im.st (o := 32) (len := 32) (by omega), hs.im.st.rnd, hs.im.st.mu, ← List.append_assoc]

theorem decode_ok {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IM p D σ s) : WP isa (decode P p) s (VG.Proof.MlDsa.Arm.Sign.IK p D σ) := by
  unfold decode
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.Arm.Sign.ID p D σ r 0 0) p.ℓ 0
    (fun r _ hr s hs => VG.Proof.MlDsa.Arm.Sign.decS1_ok hP hc (by omega) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ i 0) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.Arm.Sign.decS2_ok hP hc (by omega) hs) s1
    ⟨hs1.im, hs1.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.Arm.Sign.decT0_ok hP hc (by omega) hs) s2
    ⟨hs2.im, hs2.s1, hs2.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  exact VG.Proof.MlDsa.Arm.Sign.rpp_ok hP hc hs3

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseC`. -/
section

/-!
# ML-DSA signing on ARMv7: the commitment of an iteration

At the head of iteration `t` of the loop (`IL`): what decoding left, `κ = ℓt`
at `KAP`, `814 - t` at `CNT`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`
(`maskR_ok`), `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])` (`rowW_ok`),
`w1Encode(HighBits(w[i]))` at `W1` (`w1R_ok`), and `c̃ = H(μ ‖ w1Encode(w₁),
λ/4)` at `CT` (`commit_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : VG.Spec.MlDsa.Poly := aF maxBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) i j

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := toRq (yF p (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := yhF p (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := wF p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ)) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) maxBounds 0 t

end

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.Arm.Sign.aVal p σ (p.ℓ * i + j) = VG.Proof.MlDsa.Arm.Sign.Am p σ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.Arm.Sign.aVal, e1, e2]

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.Arm.Sign.IK p D σ s
  kap : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oKAP)) 32 = BitVec.ofNat 32 (p.ℓ * t)
  cnt : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 = BitVec.ofNat 32 (814 - t)
  t_lt : t < 814
  rej : VG.Proof.MlDsa.Arm.Sign.RejT p σ t

/-- A piece that writes `ws` keeps what decoding left (but `KAP` and `CNT`). -/
def ikChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.idChk p ws p.ℓ p.k p.k && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oMS) 64

/-- A piece that writes `ws` keeps `IL`. -/
def ilChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.ikChk p ws && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oKAP) 4 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oCNT) 4

theorem IK.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Sign.IK p D σ s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.ikChk p ws = true) : VG.Proof.MlDsa.Arm.Sign.IK p D σ s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.ikChk, Bool.and_eq_true] at hc
  exact ⟨h.d.step hP hc.1, (h.d.im.st.lay.keepBytes hP hc.2).trans h.rpp⟩

theorem IL.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.ilChk p ws = true) : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.ilChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP h1, (L.keepW hP h2).trans h.kap, (L.keepW hP h3).trans h.cnt, h.t_lt, h.rej⟩

theorem IL.st {p : Params} {D : Nat} {σ s : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) : VG.Proof.MlDsa.Arm.Sign.St p D σ s := h.k.d.im.st

/-! ## `κ + r` -/

theorem setKappa_ok (r : Nat) (hr : r < 256) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r7 + BitVec.ofNat 32 oKAP)) 4)
    (h2 : InRegions s.wr (State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 64))) 1)
    (h3 : InRegions s.wr (State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 65))) 1) :
    WP isa (.block (setKappa r)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 64)))
        ((s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 oKAP)) 32 + BitVec.ofNat 32 r).setWidth 8)).writeW
        (State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 65)))
          (((s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 oKAP)) 32 + BitVec.ofNat 32 r) >>> 8).setWidth 8) ∧
        VG.Proof.MlDsa.Arm.Sign.KeepM [.r0] s s' := by
  have enc := VG.Proof.MlDsa.Arm.Sign.encodable_small hr
  unfold setKappa
  run_block [h1, h2, h3, enc]
  exact ⟨trivial, fun r' hr' => by simp only [List.mem_singleton] at hr'; simp [hr'], rfl, rfl, rfl⟩

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 32 x).setWidth 8, (BitVec.ofNat 32 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [VG.Proof.MlDsa.Arm.Sign.integerToBytes_two]
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
  rw [e0, e1, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlDsa.Sign.ifn (VG.Proof.MlDsa.Arm.Sign.add_one_ne a), VG.Proof.MlDsa.Sign.ifp rfl,
    VG.Proof.MlKem.writeW8_apply, VG.Proof.MlDsa.Sign.ifp rfl]

/-- `κ + r` to `MS + 64`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKappa_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {r x : Nat}
    (hr : r < 256) (hx : x + r < 2 ^ 16) (h1 : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) (sc oKAP) 4 = true)
    (h2 : VG.Proof.MlDsa.Arm.Sign.inB wbs (sc (oMS + 64)) 2 = true) (hk : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oKAP)) 32 = BitVec.ofNat 32 x) :
    WP isa (.block (setKappa r)) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc (oMS + 64), 2)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 2 = integerToBytes (x + r) 2 := by
  have e65 : VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)) + 1 := (VG.Proof.MlDsa.Arm.Sign.pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.iW h2
  have ak : State.addr (s.gpr .r7 + BitVec.ofNat 32 oKAP) = VG.Proof.MlDsa.Arm.Sign.pa s (sc oKAP) := L.w (p := sc oKAP) h1 (by decide)
  have a64 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 64)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)) :=
    L.pa32W (p := sc (oMS + 64)) h2 (by decide)
  have a65 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 65)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65)) :=
    L.pa32W (p := sc (oMS + 65)) (VG.Proof.MlDsa.Arm.Sign.inB_sub (l := 1) h2 (by decide)) (by decide)
  have c0 : (⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 1 := by
    have := VG.Proof.MlDsa.Arm.Sign.contains_sub (Region.contains_self (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 2) (off := 0) (l := 1) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.Arm.Sign.contains_sub (Region.contains_self _ 2) (off := 1) (l := 1) (by decide) (by decide)
  have i0 : InRegions s.wr (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 1 := by
    have := VG.Proof.MlDsa.Arm.Sign.inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setKappa_ok r hr s (by rw [ak]; exact L.iR h1) (by rw [a64]; exact i0) (by rw [a65]; exact i1))
    fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  rw [ak, a64, a65] at hm
  have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  have hg' : ∀ r, r ≠ .r0 → s'.gpr r = s.gpr r := fun r h => hg r (by simpa using h)
  refine ⟨(VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg' hrd hwr hsp hf).1, (VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg' hrd hwr hsp hf).2, ?_⟩
  rw [hm, e65, VG.Proof.MlDsa.Arm.Sign.bytes2_write, hk, ← BitVec.ofNat_add, VG.Proof.MlDsa.Arm.Sign.kappa_bytes hx]

/-! ## `y` and `ŷ` -/

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure ICm (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) r (VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yhBase p) r (VG.Proof.MlDsa.Arm.Sign.YHv p σ (p.ℓ * t))

def icmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.ilChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yBase p) r && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yhBase p) r

theorem ICm.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : VG.Proof.MlDsa.Arm.Sign.ICm p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.icmChk p ws r = true) : VG.Proof.MlDsa.Arm.Sign.ICm p D σ t r s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.icmChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `y[r]` and `ŷ[r]` need of the layout. -/
def mChk (p : Params) (r : Nat) : Bool :=
  let y := pS (VG.Proof.MlDsa.Arm.Sign.yBase p + r)
  let yh := pS (VG.Proof.MlDsa.Arm.Sign.yhBase p + r)
  let w1 : List (Ptr × Nat) := [(sc (oMS + 64), 2)]
  let w2 : List (Ptr × Nat) := [(y, 1024), (sc oPS, 2048)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  VG.Proof.MlDsa.Arm.Sign.icmChk p w1 r && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oKAP) 4 && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc (oMS + 64)) 2 && VG.Proof.MlDsa.Arm.Sign.maskChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) y &&
    VG.Proof.MlDsa.Arm.Sign.icmChk p w2 r && VG.Proof.MlDsa.Arm.Sign.copyChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) yh y 1024 && VG.Proof.MlDsa.Arm.Sign.icmChk p w3 r && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w3 (VG.Proof.MlDsa.Arm.Sign.yBase p) (r + 1) &&
    VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) yh && VG.Proof.MlDsa.Arm.Sign.icmChk p w4 r && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w4 (VG.Proof.MlDsa.Arm.Sign.yBase p) (r + 1) &&
    decide (p.ℓ * 813 + r < 2 ^ 16) && decide (r < 256) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem maskR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.mChk p r = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.ICm p D σ t r s) : WP isa (maskR P p r) s (VG.Proof.MlDsa.Arm.Sign.ICm p D σ t (r + 1)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, k1⟩, w1⟩, cm⟩, c2⟩, cc⟩, c3⟩, f3⟩, ci⟩, c4⟩, f4⟩, hx⟩, hr⟩, hγ⟩ := hc
  have ht := h.l.t_lt
  unfold maskR
  have hx' : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.step hP1 c1
  have hms : bytesAt s1.mem (VG.Proof.MlDsa.Arm.Sign.pa s1 (sc oMS)) 66 = VG.Proof.MlDsa.Arm.Sign.rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, I1.l.k.rpp, VG.Proof.MlDsa.Arm.Sign.pa_sc_add, hP1.pa (by decide), hb1]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.maskAt_ok hP I1.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_)
  rw [hms] at hq2
  have I2 := I1.step hP2 c2
  have hy2 : VG.Proof.MlDsa.Arm.Sign.Fam s2 (VG.Proof.MlDsa.Arm.Sign.yBase p) (r + 1) (VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t)) :=
    Fam.snoc I2.y (by
      show PolyIs s2.mem (VG.Proof.MlDsa.Arm.Sign.pa s2 (pS (VG.Proof.MlDsa.Arm.Sign.yBase p + r))) _
      rw [hP2.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq2)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB I2.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := I2.step hP3 c3
  have hyh3 : VG.Proof.MlDsa.Arm.Sign.Pl s3 (VG.Proof.MlDsa.Arm.Sign.yhBase p + r) (VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]
    exact polyIs_of_bytes hb3 (hy2 r (by omega))
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, Fam.keep I3.l.st.lay hP4 f4 (Fam.keep I2.l.st.lay hP3 f3 hy2), Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _), hyh3.2] at *
  exact hq4

/-! ## `w` -/

/-- Iteration `t`, with `y`, `ŷ`, and the first `i` polynomials of `w`. -/
structure ICw (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yhBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.YHv p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p) i (VG.Proof.MlDsa.Arm.Sign.Wv p σ (p.ℓ * t))

def icwChk (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.icmChk p ws p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.wBase p) i

theorem ICw.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.icwChk p ws i = true) : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.icwChk, Bool.and_eq_true] at hc
  have I : VG.Proof.MlDsa.Arm.Sign.ICm p D σ t p.ℓ s' := (ICm.mk h.l h.y h.yh).step hP hc.1
  exact ⟨I.l, I.y, I.yh, Fam.keep h.l.st.lay hP hc.2 h.w⟩

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (σ : State) (κ i m : Nat) : VG.Spec.MlDsa.Poly :=
  ((List.range m).map fun j => multiplyNTT (VG.Proof.MlDsa.Arm.Sign.Am p σ i j) (VG.Proof.MlDsa.Arm.Sign.YHv p σ κ j)).foldl VG.Spec.MlDsa.add VG.Spec.MlDsa.zero

theorem add_zero_left (x : VG.Spec.MlDsa.Poly) : VG.Spec.MlDsa.add VG.Spec.MlDsa.zero x = x := by
  apply Vector.ext
  intro j hj
  simp [VG.Spec.MlDsa.add, VG.Spec.MlDsa.zero]

theorem wAcc_one (p : Params) (σ : State) (κ i : Nat) :
    VG.Proof.MlDsa.Arm.Sign.wAcc p σ κ i 1 = multiplyNTT (VG.Proof.MlDsa.Arm.Sign.Am p σ i 0) (VG.Proof.MlDsa.Arm.Sign.YHv p σ κ 0) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, VG.Proof.MlDsa.Arm.Sign.add_zero_left]

theorem wAcc_succ (p : Params) (σ : State) (κ i m : Nat) :
    VG.Proof.MlDsa.Arm.Sign.wAcc p σ κ i (m + 1) = VG.Spec.MlDsa.add (VG.Proof.MlDsa.Arm.Sign.wAcc p σ κ i m) (multiplyNTT (VG.Proof.MlDsa.Arm.Sign.Am p σ i m) (VG.Proof.MlDsa.Arm.Sign.YHv p σ κ m)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem aP_ij (p : Params) (i j : Nat) : aP p i j = pS (VG.Proof.MlDsa.Arm.Sign.aBase p + (p.ℓ * i + j)) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j) = _
  rw [Nat.add_assoc (5 + 4 * p.k + 3 * p.ℓ)]

/-- What `w[i]` needs of the layout. -/
def wChk (p : Params) (i : Nat) : Bool :=
  let w := pS (VG.Proof.MlDsa.Arm.Sign.wBase p + i)
  (List.range p.ℓ).all (fun j => VG.Proof.MlDsa.Arm.Sign.mulChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) w (aP p i j) (yhP p j)) && VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) w &&
    VG.Proof.MlDsa.Arm.Sign.icwChk p [(w, 1024)] i && VG.Proof.MlDsa.Arm.Sign.icwChk p [(w, 1024), (sc oPS, 1024)] i && decide (0 < p.ℓ)

theorem rowW_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.wChk p i = true) (hi : i < p.k) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) :
    WP isa (VG.Impl.MlDsa.Arm.Sign.rowW P p i) s (VG.Proof.MlDsa.Arm.Sign.ICw p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, c2⟩, hl⟩ := hc
  have hA : ∀ {s : State} (I : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (aP p i j)) (VG.Proof.MlDsa.Arm.Sign.Am p σ i j) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [VG.Proof.MlDsa.Arm.Sign.aVal_ij hj] at this
      rw [VG.Proof.MlDsa.Arm.Sign.aP_ij]; exact this
  have hY : ∀ {s : State} (I : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (yhP p j)) (VG.Proof.MlDsa.Arm.Sign.YHv p σ (p.ℓ * t) j) :=
    fun I j hj => I.yh j hj
  unfold VG.Impl.MlDsa.Arm.Sign.rowW
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP h.l.st.lay (cm 0 hl) (hA h 0 hl).1 (hY h 0 hl).1)
    fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 c1
  rw [(hA h 0 hl).2, (hY h 0 hl).2, ← VG.Proof.MlDsa.Arm.Sign.wAcc_one] at hq1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun j s => VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s ∧ VG.Proof.MlDsa.Arm.Sign.Pl s (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.wAcc p σ (p.ℓ * t) i j))
    (p.ℓ - 1) 1 (fun j hj1 hj s ⟨I, hw⟩ => ?_) s1 ⟨I1, by show PolyIs _ _ _; rw [hP1.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq1⟩)
    fun s2 ⟨I2, hw2⟩ => ?_)
  · refine WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAddAt_ok hP I.l.st.lay (cm j (by omega)) hw.1 (hA I j (by omega)).1
      (hY I j (by omega)).1) fun s' ⟨hP', _, hq'⟩ => ⟨I.step hP' c1, ?_⟩
    rw [hw.2, (hA I j (by omega)).2, (hY I j (by omega)).2, ← VG.Proof.MlDsa.Arm.Sign.wAcc_succ] at hq'
    show PolyIs _ _ _
    rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq'
  rw [show 1 + (p.ℓ - 1) = p.ℓ by omega] at hw2
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I2.l.st.lay ci hw2.1) fun s3 ⟨hP3, _, hq3⟩ => ?_
  have I3 := I2.step hP3 c2
  refine ⟨I3.l, I3.y, I3.yh, Fam.snoc I3.w ?_⟩
  show PolyIs _ _ _
  rw [hP3.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]
  rw [hw2.2] at hq3
  exact hq3

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (σ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => VG.Spec.MlDsa.simpleBitPack (w1F p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `ŷ`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure ICh (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t p.k s
  w1 : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oW1)) (w1Len p * i) = VG.Proof.MlDsa.Arm.Sign.w1Enc p σ (p.ℓ * t) i

/-- What `w1Encode(w₁[i])` needs of the layout. -/
def hChk (p : Params) (i : Nat) : Bool :=
  let w := pS (VG.Proof.MlDsa.Arm.Sign.wBase p + i)
  let o := sc (oW1 + w1Len p * i)
  VG.Proof.MlDsa.Arm.Sign.rwChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) w 1024 t1P 1024 && VG.Proof.MlDsa.Arm.Sign.rwChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t1P 1024 o (w1Len p) &&
    VG.Proof.MlDsa.Arm.Sign.icwChk p [(t1P, 1024)] p.k && VG.Proof.MlDsa.Arm.Sign.icwChk p [(o, w1Len p)] p.k && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(t1P, 1024)] (sc oW1) (w1Len p * i) &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(o, w1Len p)] (sc oW1) (w1Len p * i) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (p.γ₂ ∈ gamma2s)

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

theorem w1R_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.hChk p i = true) (hi : i < p.k) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.ICh p D σ t i s) :
    WP isa (w1R P p i) s (VG.Proof.MlDsa.Arm.Sign.ICh p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, k1⟩, k2⟩, e1⟩, e2⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.highBitsAt_ok hP h.c.l.st.lay hγ c1 (h.c.w i hi).1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.c.step hP1 k1
  rw [(h.c.w i hi).2] at hq1
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.sbpAt_ok hP I1.l.st.lay hb rfl c2 fun j hj => ?_) fun s2 ⟨hP2, _, hq2⟩ => ?_
  · rw [hP1.pa (by decide), VG.Proof.MlDsa.Arm.Sign.natPolyIs_coeff hq1 hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _
  have I2 := I1.step hP2 k2
  refine ⟨I2, ?_⟩
  have b1 : bytesAt s2.mem (VG.Proof.MlDsa.Arm.Sign.pa s2 (sc oW1)) (w1Len p * i) = VG.Proof.MlDsa.Arm.Sign.w1Enc p σ (p.ℓ * t) i := by
    rw [I1.l.st.lay.keepBytes hP2 e2, h.c.l.st.lay.keepBytes hP1 e1, h.w1]
  have b2 : bytesAt s2.mem (VG.Proof.MlDsa.Arm.Sign.pa s2 (sc (oW1 + w1Len p * i))) (w1Len p) =
      VG.Spec.MlDsa.simpleBitPack (w1F p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) (p.ℓ * t) i) (w1Max p) := by
    rw [hP2.pa (VG.Proof.MlDsa.Arm.Sign.sc_bases _), hq2, hP1.pa (by decide), show natPolyAt s1.mem (VG.Proof.MlDsa.Arm.Sign.pa s t1P) = _ from hq1]
    rfl
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, VG.Proof.MlDsa.Arm.Sign.pa_sc_add, b1, b2, VG.Proof.MlDsa.Arm.Sign.w1Enc, VG.Proof.MlDsa.Arm.Sign.w1Enc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton]

/-- The commitment of iteration `t`: `y`, `ŷ`, `w`, and `c̃` at `CT`. -/
structure IC (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  (List.range p.ℓ).all (VG.Proof.MlDsa.Arm.Sign.mChk p) && (List.range p.k).all (VG.Proof.MlDsa.Arm.Sign.wChk p) && (List.range p.k).all (VG.Proof.MlDsa.Arm.Sign.hChk p) &&
    VG.Proof.MlDsa.Arm.Sign.shakeChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) [((.r5, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p) &&
    VG.Proof.MlDsa.Arm.Sign.icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem commit_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) : WP isa (commit P p) s (VG.Proof.MlDsa.Arm.Sign.IC p D σ t) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, hk⟩ := hc
  unfold commit
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.Arm.Sign.ICm p D σ t r) p.ℓ 0
    (fun r _ hr s hs => VG.Proof.MlDsa.Arm.Sign.maskR_ok hP (hm r (by omega)) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.Arm.Sign.rowW_ok hP (hw i (by omega)) (by omega) hs) s1
    ⟨hs1.l, hs1.y, hs1.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.Arm.Sign.ICh p D σ t i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.Arm.Sign.w1R_ok hP (hh i (by omega)) (by omega) hs) s2
    ⟨hs2, by simp [VG.Proof.MlDsa.Arm.Sign.w1Enc]; rfl⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.shake_ok (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hP.hD hs hs3.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs3.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [VG.Proof.MlDsa.Arm.Sign.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, hs3.w1, hs3.c.l.st.mu]
  simp only [VG.Proof.MlDsa.Arm.Sign.CTv, ctF, w1Encode, List.flatMap_map]

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseK`. -/
section

/-!
# ML-DSA signing on ARMv7: the checks of an iteration

`c = SampleInBall(c̃)` at `ĉ` (`ball_ok`), and, if it succeeded, `ĉ = NTT(c)`
and each check of the iteration, their results ANDed into `r11`: the norm of
each `z[r]` (`zR_ok`), of each `r₀[i]` (`r0R_ok`) and of each `ct₀[i]`, with
each hint `h[i]` and the number of its 1s summed at `ONES` (`hR_ok`), and that
sum against `ω` (`onesOk_ok`); so `r11` is 1 exactly when the iteration passes
(`checks_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `c = SampleInBall(c̃)` of the iteration with counter `κ`, within `maxBounds`. -/
abbrev cV (σ : State) (κ : Nat) : IPoly :=
  (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)).getD (Vector.replicate n 0)

/-- `z[r]`, `r₀[i]`, `ct₀[i]`, `w[i] - cs₂[i]`, `w[i] - cs₂[i] + ct₀[i]` and `h[i]`. -/
abbrev Zv (σ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := zF p (VG.Proof.MlDsa.Arm.Sign.S1v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) r
abbrev R0v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := r0F p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) i
abbrev CT0v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := ct0F (VG.Proof.MlDsa.Arm.Sign.T0v p σ) (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) i
abbrev W'v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := w'F p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) i
abbrev W''v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := w''F p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.T0v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) i
abbrev Hv (σ : State) (κ i : Nat) : Vector Bool n := hF p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.T0v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) i

/-- Whether the iteration with counter `κ` passes, once `SampleInBall` succeeded. -/
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S1v p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.T0v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ (VG.Proof.MlDsa.Arm.Sign.cV p σ κ)

end

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)
  r01 : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1
  ok : s.gpr .r0 = 1 → VG.Proof.MlDsa.Arm.Sign.Pl s 0 (toRq (VG.Proof.MlDsa.Arm.Sign.cV p σ (p.ℓ * t))) ∧
    (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome
  bad : s.gpr .r0 = 0 → VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)) = none

def bChk (p : Params) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.ballChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (cLen p) cP && VG.Proof.MlDsa.Arm.Sign.icwChk p [(cP, 1024), (sc oPS, 2048)] p.k &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(cP, 1024), (sc oPS, 2048)] (sc oCT) (cLen p) && decide ((cLen p, p.τ) ∈ ballParams)

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : VG.Spec.MlDsa.Poly}
    (h : Outcome (fun b => (VG.Spec.MlDsa.sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (VG.Spec.MlDsa.sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((VG.Spec.MlDsa.sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem ball_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.bChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IC p D σ t s) : WP isa (ballAt P (cLen p) p.τ cP) s (VG.Proof.MlDsa.Arm.Sign.IB p D σ t) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.bChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, hbp⟩ := hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.ballCall_ok hP h.c.l.st.lay hbp c1) fun s' ⟨hP1, _, hred, hout, hmax⟩ => ?_
  rw [h.ct] at hout hmax
  refine ⟨h.c.step hP1 c2, by rw [h.c.l.st.lay.keepBytes hP1 c3, h.ct], ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · refine ⟨?_, hmax h1⟩
    show PolyIs _ _ _
    rw [hP1.pa (by decide)]
    exact ⟨hred h1, VG.Proof.MlDsa.Arm.Sign.ball_val hout h1 (hmax h1)⟩
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

/-! ## Norms, into `r11` -/

theorem normAt_okB {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.Arm.Sign.normChk (rbs ++ wbs) f = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) {a : Prop} [Decidable a] (h15 : s.gpr .r11 = VG.Proof.MlDsa.Arm.Sign.bit a) :
    WP isa (normAt P f B) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [] ∧
      (∀ r ∈ preserved, r ≠ .lr → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r11 = VG.Proof.MlDsa.Arm.Sign.bit (a ∧ normRq [polyAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)] < B) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.normCall_ok hP L hB hc hr) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.and11_ok s1) fun s2 ⟨h15', k2⟩ => ?_
  obtain ⟨hP2, hcs2⟩ := VG.Proof.MlDsa.Arm.Sign.postB11 (D := D) k2 (([] : List (Ptr × Nat)).map (VG.Proof.MlDsa.Arm.Sign.toR s1))
  refine ⟨PPostB.trans hP1 hP2 (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil), fun r hr hl hne => (hcs2 r hr hl hne).trans (hcs1 r hr hl), ?_⟩
  rw [h15', VG.Proof.MlDsa.Arm.Sign.bit_and (hcs1 _ (by decide) (by decide) |>.trans h15) hq1]

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : VG.Proof.MlDsa.Arm.Sign.bit a = VG.Proof.MlDsa.Arm.Sign.bit b := by
  by_cases ha : a
  · rw [show VG.Proof.MlDsa.Arm.Sign.bit a = 1 from VG.Proof.MlDsa.Sign.ifp ha _ _, show VG.Proof.MlDsa.Arm.Sign.bit b = 1 from VG.Proof.MlDsa.Sign.ifp (h.mp ha) _ _]
  · rw [show VG.Proof.MlDsa.Arm.Sign.bit a = 0 from VG.Proof.MlDsa.Sign.ifn ha _ _, show VG.Proof.MlDsa.Arm.Sign.bit b = 0 from VG.Proof.MlDsa.Sign.ifn (fun hb => ha (h.mpr hb)) _ _]

theorem bit01 {a : Prop} [Decidable a] : VG.Proof.MlDsa.Arm.Sign.bit a = 0 ∨ VG.Proof.MlDsa.Arm.Sign.bit a = 1 := by
  by_cases ha : a
  · exact .inr (VG.Proof.MlDsa.Sign.ifp ha _ _)
  · exact .inl (VG.Proof.MlDsa.Sign.ifn ha _ _)

theorem bit_one {a : Prop} [Decidable a] : VG.Proof.MlDsa.Arm.Sign.bit a = 1 ↔ a := by
  by_cases ha : a
  · exact ⟨fun _ => ha, fun _ => VG.Proof.MlDsa.Sign.ifp ha _ _⟩
  · exact ⟨fun h => absurd (h.symm.trans (VG.Proof.MlDsa.Sign.ifn ha 1 0)) (by decide), fun h => absurd h ha⟩

theorem bit_zero {a : Prop} [Decidable a] : VG.Proof.MlDsa.Arm.Sign.bit a = 0 ↔ ¬ a := by
  by_cases ha : a
  · exact ⟨fun h => absurd (h.symm.trans (VG.Proof.MlDsa.Sign.ifp ha 1 0)) (by decide), fun h => absurd ha h⟩
  · exact ⟨fun _ => ha, fun _ => VG.Proof.MlDsa.Sign.ifn ha _ _⟩

theorem forall_lt_succ {P : Nat → Prop} {r : Nat} : ((∀ j < r, P j) ∧ P r) ↔ ∀ j < r + 1, P j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega), h r (by omega)⟩⟩

theorem Fam.head {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s b (m + 1) f) : VG.Proof.MlDsa.Arm.Sign.Pl s b (f 0) := h 0 (by omega)

theorem Fam.tail {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s b (m + 1) f) :
    VG.Proof.MlDsa.Arm.Sign.Fam s (b + 1) m fun j => f (j + 1) := fun j hj => by
  have := h (j + 1) (by omega)
  show VG.Proof.MlDsa.Arm.Sign.Pl s (b + 1 + j) _
  rw [show b + 1 + j = b + (j + 1) by omega]
  exact this

theorem Fam.shift {s : State} {b m r : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s (b + r) (m - r) fun j => f (r + j))
    (hr : r < m) : VG.Proof.MlDsa.Arm.Sign.Fam s (b + (r + 1)) (m - (r + 1)) fun j => f (r + 1 + j) := fun j hj => by
  have := h (j + 1) (by omega)
  show VG.Proof.MlDsa.Arm.Sign.Pl s (b + (r + 1) + j) (f (r + 1 + j))
  rw [show b + (r + 1) + j = b + r + (j + 1) by omega, show r + 1 + j = r + (j + 1) by omega]
  exact this

theorem Fam.zero {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.Arm.Sign.Fam s b m f) :
    VG.Proof.MlDsa.Arm.Sign.Fam s (b + 0) (m - 0) fun j => f (0 + j) := fun j hj => by
  show VG.Proof.MlDsa.Arm.Sign.Pl s (b + 0 + j) (f (0 + j))
  rw [Nat.add_zero, Nat.zero_add]
  exact h j hj

/-! ## The checks' state -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded: `ĉ = NTT(c)`. -/
structure KB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s
  ct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)
  c : VG.Proof.MlDsa.Arm.Sign.Pl s 0 (chF (VG.Proof.MlDsa.Arm.Sign.cV p σ (p.ℓ * t)))
  some : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome

def kbChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.ilChk p ws && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oCT) (cLen p) && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws cP 1024

theorem KB.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.kbChk p ws = true) : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.kbChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP h1, (L.keepBytes hP h2).trans h.ct, L.keepPoly hP h3 h.c, h.some⟩

/-! ## `z` -/

/-- The checks of `z[j]` for `j < r`, with `ONES = 0` (but `r11`). -/
structure IZb (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) r (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t))
  y : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p + r) (p.ℓ - r) fun j => VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t) (r + j)
  w : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k (VG.Proof.MlDsa.Arm.Sign.Wv p σ (p.ℓ * t))
  ones : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oONES)) 32 = 0

/-- The checks of `z[j]` for `j < r`, their results in `r11`. -/
def IZ (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Sign.IZb p D σ t r s ∧ s.gpr .r11 = VG.Proof.MlDsa.Arm.Sign.bit (∀ j < r, normRq [VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

def zfam (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.kbChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yBase p) r && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oONES) 4

theorem IZb.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : VG.Proof.MlDsa.Arm.Sign.IZb p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.zfam p ws r = true)
    (hy : VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yBase p + r) (p.ℓ - r) = true) : VG.Proof.MlDsa.Arm.Sign.IZb p D σ t r s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.zfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP hy h.y, Fam.keep L hP h3 h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `z[r]` needs of the layout. -/
def zChk (p : Params) (r : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(yP p r, 1024)]
  VG.Proof.MlDsa.Arm.Sign.mulChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t1P cP (s1P p r) && VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t1P && VG.Proof.MlDsa.Arm.Sign.accChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (yP p r) t1P &&
    VG.Proof.MlDsa.Arm.Sign.normChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (yP p r) && VG.Proof.MlDsa.Arm.Sign.zfam p w1 r && VG.Proof.MlDsa.Arm.Sign.zfam p w2 r && VG.Proof.MlDsa.Arm.Sign.zfam p w3 r && VG.Proof.MlDsa.Arm.Sign.zfam p [] (r + 1) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (VG.Proof.MlDsa.Arm.Sign.yBase p + r) (p.ℓ - r) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w2 (VG.Proof.MlDsa.Arm.Sign.yBase p + r) (p.ℓ - r) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w3 (VG.Proof.MlDsa.Arm.Sign.yBase p + (r + 1)) (p.ℓ - (r + 1)) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.yBase p + (r + 1)) (p.ℓ - (r + 1)) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w3 (VG.Proof.MlDsa.Arm.Sign.yBase p) r && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (s1P p r) 1024 && decide (p.γ₁ - p.β < 2 ^ 32) &&
    decide (r < p.ℓ)

theorem zR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.zChk p r = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IZ p D σ t r s) : WP isa (zR P p r) s (VG.Proof.MlDsa.Arm.Sign.IZ p D σ t (r + 1)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, y1⟩, y2⟩, y3⟩, y4⟩, f3⟩, e1⟩, hB⟩, hr⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs1 := h.b.l.k.d.s1 r hr
  unfold zR
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L cm h.b.c.1 hs1.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs1.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hy2 : VG.Proof.MlDsa.Arm.Sign.Pl s2 (VG.Proof.MlDsa.Arm.Sign.yBase p + r) (VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t) r) := I2.y 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.addAt_ok hP I2.b.l.st.lay ca hy2.1 (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1))
    fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hy2.2, hP2.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1), hP1.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [VG.Proof.MlDsa.Arm.Sign.zfam, Bool.and_eq_true] at z3 z4
  have hz3 : VG.Proof.MlDsa.Arm.Sign.Pl s3 (VG.Proof.MlDsa.Arm.Sign.yBase p + r) (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]
    exact hq3
  have J3 : VG.Proof.MlDsa.Arm.Sign.IZb p D σ t (r + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.snoc (Fam.keep L2 hP3 f3 I2.z) hz3,
    Fam.keep L2 hP3 y3 (I2.y.shift hr),
    Fam.keep L2 hP3 z3.1.2 I2.w, (L2.keepW hP3 z3.2).trans I2.ones⟩
  have e15 : s3.gpr .r11 = s.gpr .r11 := by
    rw [hcs3 _ (by decide) (by decide), hcs2 _ (by decide) (by decide), hcs1 _ (by decide) (by decide)]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.normAt_okB hP J3.b.l.st.lay hB cn hz3.1 (e15.trans h15)) fun s4 ⟨hP4, _, h4⟩ => ?_
  have L3 := J3.b.l.st.lay
  refine ⟨⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z, Fam.keep L3 hP4 y4 J3.y,
    Fam.keep L3 hP4 z4.1.2 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩, ?_⟩
  rw [h4, hz3.2]
  exact VG.Proof.MlDsa.Arm.Sign.bit_congr VG.Proof.MlDsa.Arm.Sign.forall_lt_succ

/-! ## `r₀` -/

/-- The checks of `r₀[j]` for `j < i` (`w[j]` is `w[j] - cs₂[j]`), with `z` checked and `ONES = 0`. -/
structure IRb (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t))
  w' : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p) i (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (p.k - i) fun j => VG.Proof.MlDsa.Arm.Sign.Wv p σ (p.ℓ * t) (i + j)
  ones : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oONES)) 32 = 0

/-- `z` passed. -/
abbrev ZOk (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [VG.Proof.MlDsa.Arm.Sign.Zv p σ κ j] < p.γ₁ - p.β

def IR (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Sign.IRb p D σ t i s ∧
    s.gpr .r11 = VG.Proof.MlDsa.Arm.Sign.bit (VG.Proof.MlDsa.Arm.Sign.ZOk p σ (p.ℓ * t) ∧ ∀ j < i, normRq [VG.Proof.MlDsa.Arm.Sign.R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

def rfam (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.kbChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.wBase p) i && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oONES) 4

theorem IRb.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : VG.Proof.MlDsa.Arm.Sign.IRb p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.rfam p ws i = true)
    (hw : VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (p.k - i) = true) : VG.Proof.MlDsa.Arm.Sign.IRb p D σ t i s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.rfam, Bool.and_eq_true] at hc
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
  VG.Proof.MlDsa.Arm.Sign.mulChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t1P cP (s2P p i) && VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t1P && VG.Proof.MlDsa.Arm.Sign.accChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (wP p i) t1P &&
    VG.Proof.MlDsa.Arm.Sign.rwChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (wP p i) 1024 t2P 1024 && VG.Proof.MlDsa.Arm.Sign.normChk (VG.Proof.MlDsa.Arm.Sign.sgB p) t2P && VG.Proof.MlDsa.Arm.Sign.rfam p w1 i && VG.Proof.MlDsa.Arm.Sign.rfam p w2 i &&
    VG.Proof.MlDsa.Arm.Sign.rfam p w3 i && VG.Proof.MlDsa.Arm.Sign.rfam p w4 (i + 1) && VG.Proof.MlDsa.Arm.Sign.rfam p [] (i + 1) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (p.k - i) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w2 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (p.k - i) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w3 (VG.Proof.MlDsa.Arm.Sign.wBase p + (i + 1)) (p.k - (i + 1)) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w4 (VG.Proof.MlDsa.Arm.Sign.wBase p + (i + 1)) (p.k - (i + 1)) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.wBase p + (i + 1)) (p.k - (i + 1)) && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w4 (wP p i) 1024 &&
    decide (p.γ₂ - p.β < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k)

theorem r0R_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.rChk p i = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IR p D σ t i s) : WP isa (r0R P p i) s (VG.Proof.MlDsa.Arm.Sign.IR p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, y1⟩, y2⟩, y3⟩, y4⟩, y5⟩, k4⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs2 := h.b.l.k.d.s2 i hi
  unfold r0R
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L cm h.b.c.1 hs2.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs2.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hw2 : VG.Proof.MlDsa.Arm.Sign.Pl s2 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.Wv p σ (p.ℓ * t) i) := I2.w 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.subAt_ok hP I2.b.l.st.lay ca hw2.1
    (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1)) fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hw2.2, hP2.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1), hP1.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [VG.Proof.MlDsa.Arm.Sign.rfam, Bool.and_eq_true] at z3 z4 z5
  have hw3 : VG.Proof.MlDsa.Arm.Sign.Pl s3 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]
    exact hq3
  have J3 : VG.Proof.MlDsa.Arm.Sign.IRb p D σ t (i + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.keep L2 hP3 z3.1.1.2 I2.z,
    Fam.snoc (Fam.keep L2 hP3 z3.1.2 I2.w') hw3, Fam.keep L2 hP3 y3 (I2.w.shift hi), (L2.keepW hP3 z3.2).trans I2.ones⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.lowBitsAt_ok hP J3.b.l.st.lay hγ cl hw3.1) fun s4 ⟨hP4, hcs4, hq4⟩ => ?_)
  rw [hw3.2] at hq4
  have L3 := J3.b.l.st.lay
  have J4 : VG.Proof.MlDsa.Arm.Sign.IRb p D σ t (i + 1) s4 := ⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z,
    Fam.keep L3 hP4 z4.1.2 J3.w', Fam.keep L3 hP4 y4 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩
  have e15 : s4.gpr .r11 = s.gpr .r11 := by
    rw [hcs4 _ (by decide) (by decide), hcs3 _ (by decide) (by decide), hcs2 _ (by decide) (by decide),
      hcs1 _ (by decide) (by decide)]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.normAt_okB hP J4.b.l.st.lay hB cn (by rw [hP4.pa (by decide)]; exact hq4.1) (e15.trans h15))
    fun s5 ⟨hP5, _, h5⟩ => ?_
  have L4 := J4.b.l.st.lay
  refine ⟨⟨J4.b.step hP5 z5.1.1.1, Fam.keep L4 hP5 z5.1.1.2 J4.z, Fam.keep L4 hP5 z5.1.2 J4.w',
    Fam.keep L4 hP5 y5 J4.w, (L4.keepW hP5 z5.2).trans J4.ones⟩, ?_⟩
  rw [h5, hP4.pa (by decide), hq4.2]
  exact VG.Proof.MlDsa.Arm.Sign.bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
    fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## Hints and their 1s -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, VG.Spec.MlDsa.q] at *
  omega

theorem sub_add_neg (a b : VG.Spec.MlDsa.Poly) : VG.Spec.MlDsa.sub a (VG.Spec.MlDsa.add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.MlDsa.sub, VG.Spec.MlDsa.add, neg, Vector.getElem_zipWith, Vector.getElem_map, VG.Proof.MlDsa.Arm.Sign.zq_sub_add]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : List (Vector Bool n)}
    (hb : ∀ k < 1024, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) (H : HintIs m a 1 h) :
    HintIs m' a 1 h :=
  ⟨H.1, fun i hi j hj => by
    have hn : n = 256 := rfl
    rw [coeffAt_congr₂ hb (show 256 * i + j < 256 by omega)]; exact H.2 i hi j hj⟩

/-- The hints of the first `m` slots from `b`. -/
def HFam (s : State) (b m : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < m, HintIs s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (pS (b + j))) 1 [f j]

theorem HFam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) {b m : Nat} {f : Nat → Vector Bool n}
    (hc : VG.Proof.MlDsa.Arm.Sign.famChk (rbs ++ wbs) ws b m = true) (h : VG.Proof.MlDsa.Arm.Sign.HFam s b m f) : VG.Proof.MlDsa.Arm.Sign.HFam s' b m f := fun j hj => by
  have hk := VG.Proof.MlDsa.Arm.Sign.famChk_one hc hj
  rw [hP.pa (VG.Proof.MlDsa.Arm.Sign.keepB_cs hk)]
  exact VG.Proof.MlDsa.Arm.Sign.hintIs_congr (VG.Proof.MlKem.bytes_frame hP.frame (L.fdisj hk) (by decide)) (h j hj)

theorem HFam.snoc {s : State} {b m : Nat} {f : Nat → Vector Bool n} (h : VG.Proof.MlDsa.Arm.Sign.HFam s b m f)
    (h' : HintIs s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (pS (b + m))) 1 [f m]) : VG.Proof.MlDsa.Arm.Sign.HFam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [VG.Proof.MlDsa.Sign.hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The sum of the 1s of the first `i` hints. -/
abbrev onesSum (f : Nat → Vector Bool n) (i : Nat) : Nat := ((List.range i).map fun j => hintOnes [f j]).sum

theorem onesSum_le (f : Nat → Vector Bool n) : ∀ i, VG.Proof.MlDsa.Arm.Sign.onesSum f i ≤ 256 * i
  | 0 => by simp [VG.Proof.MlDsa.Arm.Sign.onesSum]
  | i + 1 => by
    simp only [VG.Proof.MlDsa.Arm.Sign.onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have := VG.Proof.MlDsa.Arm.Sign.onesSum_le f i; have := VG.Proof.MlDsa.Arm.Sign.hintOnes_le (f i)
    simp only [VG.Proof.MlDsa.Arm.Sign.onesSum] at *
    omega

theorem onesSum_succ (f : Nat → Vector Bool n) (i : Nat) : VG.Proof.MlDsa.Arm.Sign.onesSum f (i + 1) = VG.Proof.MlDsa.Arm.Sign.onesSum f i + hintOnes [f i] := by
  simp only [VG.Proof.MlDsa.Arm.Sign.onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The block after `vg_mldsa_make_hint`: its result added to `ONES`. -/
abbrev onesAdd : List Instr := [.ldr .r1 .r7 oONES, .dp .add .r1 .r1 (.reg .r0), .str .r1 .r7 oONES]

theorem onesAdd_ok (s : State) (h2 : InRegions s.wr (State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES)) 4) :
    WP isa (.block VG.Proof.MlDsa.Arm.Sign.onesAdd) s fun s' => s'.mem = s.mem.writeW (State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES))
      (s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES)) 32 + s.gpr .r0) ∧ VG.Proof.MlDsa.Arm.Sign.KeepM [.r1] s s' := by
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES)) 4 := Covers.right (Covers.one h2) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  run_block [h1, h2]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

/-! ## `ct₀` and the hint -/

/-- `r₀` passed. -/
abbrev R0Ok (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [VG.Proof.MlDsa.Arm.Sign.R0v p σ κ j] < p.γ₂ - p.β

/-- The checks of `ct₀[j]` for `j < a`, where `w[j]` is `w[j] - cs₂[j] + ct₀[j]`, and the hints `h[j]` for
`j < c`, their 1s summed at `ONES`. -/
structure IHb (p : Params) (D : Nat) (σ : State) (t a c : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t))
  w'' : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p) a (VG.Proof.MlDsa.Arm.Sign.W''v p σ (p.ℓ * t))
  w' : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p + a) (p.k - a) fun j => VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) (a + j)
  h : VG.Proof.MlDsa.Arm.Sign.HFam s 5 c (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t))
  ones : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oONES)) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sign.onesSum (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t)) c)

def IH (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Sign.IHb p D σ t i i s ∧ s.gpr .r11 = VG.Proof.MlDsa.Arm.Sign.bit ((VG.Proof.MlDsa.Arm.Sign.ZOk p σ (p.ℓ * t) ∧ VG.Proof.MlDsa.Arm.Sign.R0Ok p σ (p.ℓ * t)) ∧
    ∀ j < i, normRq [VG.Proof.MlDsa.Arm.Sign.CT0v p σ (p.ℓ * t) j] < p.γ₂)

def hfam (p : Params) (ws : List (Ptr × Nat)) (a c : Nat) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.kbChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.wBase p) a &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.wBase p + a) (p.k - a) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws 5 c

theorem IHb.step {p : Params} {D : Nat} {σ s s' : State} {t a c : Nat} (h : VG.Proof.MlDsa.Arm.Sign.IHb p D σ t a c s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.hfam p ws a c = true)
    (ho : VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (sc oONES) 4 = true) : VG.Proof.MlDsa.Arm.Sign.IHb p D σ t a c s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.hfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w'', Fam.keep L hP h4 h.w',
    HFam.keep L hP h5 h.h, (L.keepW hP ho).trans h.ones⟩

/-- What `h[i]` needs of the layout. -/
def hChk2 (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t3P, 1024)]
  let w2 : List (Ptr × Nat) := [(t3P, 1024), (sc oPS, 1024)]
  let w4 : List (Ptr × Nat) := [(t4P, 1024)]
  let w5 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w7 : List (Ptr × Nat) := [(hP i, 1024)]
  let w8 : List (Ptr × Nat) := [(sc oONES, 4)]
  VG.Proof.MlDsa.Arm.Sign.mulChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t3P cP (t0P p i) && VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t3P && VG.Proof.MlDsa.Arm.Sign.normChk (VG.Proof.MlDsa.Arm.Sign.sgB p) t3P &&
    VG.Proof.MlDsa.Arm.Sign.copyChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t4P (wP p i) 1024 && VG.Proof.MlDsa.Arm.Sign.accChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (wP p i) t3P &&
    VG.Proof.MlDsa.Arm.Sign.accChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t4P (wP p i) && VG.Proof.MlDsa.Arm.Sign.hintChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) t4P (wP p i) (hP i) &&
    VG.Proof.MlDsa.Arm.Sign.hfam p w1 i i && VG.Proof.MlDsa.Arm.Sign.hfam p w2 i i && VG.Proof.MlDsa.Arm.Sign.hfam p [] i i && VG.Proof.MlDsa.Arm.Sign.hfam p w4 i i &&
    (VG.Proof.MlDsa.Arm.Sign.kbChk p w5 && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w5 (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w5 5 i) &&
    VG.Proof.MlDsa.Arm.Sign.hfam p w4 (i + 1) i && VG.Proof.MlDsa.Arm.Sign.hfam p w7 (i + 1) i && VG.Proof.MlDsa.Arm.Sign.hfam p w8 (i + 1) (i + 1) &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w5 (VG.Proof.MlDsa.Arm.Sign.wBase p) i && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) w5 (VG.Proof.MlDsa.Arm.Sign.wBase p + (i + 1)) (p.k - (i + 1)) &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (sc oONES) 4 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w2 (sc oONES) 4 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (sc oONES) 4 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w4 (sc oONES) 4 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w5 (sc oONES) 4 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w7 (sc oONES) 4 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [] t3P 1024 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w4 t3P 1024 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w5 t4P 1024 && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) w1 (t0P p i) 1024 &&
    VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oONES) 4 && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oONES) 4 &&
    decide (p.γ₂ < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k) && decide (256 * p.k < 2 ^ 32)

theorem pa_sc {s s' : State} (h : s'.gpr .r7 = s.gpr .r7) (o : Nat) : VG.Proof.MlDsa.Arm.Sign.pa s' (sc o) = VG.Proof.MlDsa.Arm.Sign.pa s (sc o) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.pa, h]

theorem hR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.Arm.Sign.hChk2 p i = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IH p D σ t i s) : WP isa (VG.Impl.MlDsa.Arm.Sign.hR P p i) s (VG.Proof.MlDsa.Arm.Sign.IH p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, f5a⟩, f5b⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o7⟩, t3⟩, t4⟩, u5⟩, v1⟩, i1⟩, i2⟩, hγ'⟩, hγ⟩, hi⟩, hk⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have ht0 := h.b.l.k.d.t0 i hi
  unfold VG.Impl.MlDsa.Arm.Sign.hR
  -- `ĉ t̂₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L cm h.b.c.1 ht0.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, ht0.2] at hq1
  have I1 := h.step hP1 g1 o1
  have b1 : s1.gpr .r7 = s.gpr .r7 := hP1.bs _ (by decide)
  -- `ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I1.b.l.st.lay ci (by rw [VG.Proof.MlDsa.Arm.Sign.pa_sc b1]; exact hq1.1))
    fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [VG.Proof.MlDsa.Arm.Sign.pa_sc b1, hq1.2] at hq2
  have I2 := I1.step hP2 g2 o2
  have b2 : s2.gpr .r7 = s.gpr .r7 := (hP2.bs _ (by decide)).trans b1
  have q2 : VG.Proof.MlDsa.Arm.Sign.Pl s2 3 (VG.Proof.MlDsa.Arm.Sign.CT0v p σ (p.ℓ * t) i) := by show PolyIs _ _ _; rw [VG.Proof.MlDsa.Arm.Sign.pa_sc b2]; exact hq2
  -- its norm
  have e2 : s2.gpr .r11 = s.gpr .r11 := by rw [hcs2 _ (by decide) (by decide), hcs1 _ (by decide) (by decide)]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.normAt_okB hP I2.b.l.st.lay hγ' cn q2.1 (e2.trans h15)) fun s3 ⟨hP3, hcs3, h3⟩ => ?_)
  rw [q2.2] at h3
  have I3 := I2.step hP3 g3 o3
  have q3 : VG.Proof.MlDsa.Arm.Sign.Pl s3 3 (VG.Proof.MlDsa.Arm.Sign.CT0v p σ (p.ℓ * t) i) := I2.b.l.st.lay.keepPoly hP3 t3 q2
  -- `T4 ← w[i] - cs₂[i]`
  have hw3 : VG.Proof.MlDsa.Arm.Sign.Pl s3 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) i) := I3.w' 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB I3.b.l.st.lay cc) fun s4 ⟨hP4, hcs4, hb4⟩ => ?_)
  have I4 := I3.step hP4 g4 o4
  have q4 : VG.Proof.MlDsa.Arm.Sign.Pl s4 3 (VG.Proof.MlDsa.Arm.Sign.CT0v p σ (p.ℓ * t) i) := I3.b.l.st.lay.keepPoly hP4 t4 q3
  have r4 : VG.Proof.MlDsa.Arm.Sign.Pl s4 4 (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP4.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 4)]; exact polyIs_of_bytes hb4 hw3
  have hw4 : VG.Proof.MlDsa.Arm.Sign.Pl s4 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) i) := I4.w' 0 (by omega)
  -- `w[i] ← w[i] - cs₂[i] + ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.addAt_ok hP I4.b.l.st.lay ca hw4.1 q4.1) fun s5 ⟨hP5, hcs5, hq5⟩ => ?_)
  rw [hw4.2, q4.2] at hq5
  have L4 := I4.b.l.st.lay
  have hw5 : VG.Proof.MlDsa.Arm.Sign.Pl s5 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.W''v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP5.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq5
  have J5 : VG.Proof.MlDsa.Arm.Sign.IHb p D σ t (i + 1) i s5 := ⟨I4.b.step hP5 g5.1.1, Fam.keep L4 hP5 g5.1.2 I4.z,
    Fam.snoc (Fam.keep L4 hP5 f5a I4.w'') hw5, Fam.keep L4 hP5 f5b (I4.w'.shift hi), HFam.keep L4 hP5 g5.2 I4.h,
    (L4.keepW hP5 o5).trans I4.ones⟩
  have r5 : VG.Proof.MlDsa.Arm.Sign.Pl s5 4 (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) i) := L4.keepPoly hP5 u5 r4
  -- `T4 ← -ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.subAt_ok hP J5.b.l.st.lay cs r5.1 hw5.1) fun s6 ⟨hP6, hcs6, hq6⟩ => ?_)
  rw [r5.2, hw5.2, show VG.Proof.MlDsa.Arm.Sign.W''v p σ (p.ℓ * t) i = VG.Spec.MlDsa.add (VG.Proof.MlDsa.Arm.Sign.W'v p σ (p.ℓ * t) i) (VG.Proof.MlDsa.Arm.Sign.CT0v p σ (p.ℓ * t) i) from rfl,
    VG.Proof.MlDsa.Arm.Sign.sub_add_neg] at hq6
  have J6 := J5.step hP6 g6 o4
  have r6 : VG.Proof.MlDsa.Arm.Sign.Pl s6 4 (neg (VG.Proof.MlDsa.Arm.Sign.CT0v p σ (p.ℓ * t) i)) := by show PolyIs _ _ _; rw [hP6.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 4)]; exact hq6
  have hw6 : VG.Proof.MlDsa.Arm.Sign.Pl s6 (VG.Proof.MlDsa.Arm.Sign.wBase p + i) (VG.Proof.MlDsa.Arm.Sign.W''v p σ (p.ℓ * t) i) := J6.w'' i (by omega)
  -- the hint
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.hintCall_ok hP J6.b.l.st.lay hγ ch r6.1 hw6.1) fun s7 ⟨hP7, hcs7, hq7, he7⟩ => ?_)
  rw [r6.2, hw6.2] at hq7 he7
  have J7 := J6.step hP7 g7 o7
  have hh7 : VG.Proof.MlDsa.Arm.Sign.HFam s7 5 (i + 1) (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t)) :=
    HFam.snoc J7.h (by rw [hP7.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq7)
  -- `ONES`
  have ho7 : s7.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s7 (sc oONES)) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Sign.onesSum (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t)) i) := J7.ones
  have L7 := J7.b.l.st.lay
  have ao : State.addr (s7.gpr .r7 + BitVec.ofNat 32 oONES) = VG.Proof.MlDsa.Arm.Sign.pa s7 (sc oONES) := L7.pa32W (p := sc oONES) i2 (by decide)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.onesAdd_ok s7 (by rw [ao]; exact L7.iW i2)) fun s8 ⟨hm8, hg8, hrd8, hwr8, hsp8⟩ => ?_
  rw [ao] at hm8
  have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s7 (sc oONES), 4⟩] s7.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcs8 : VG.Proof.MlDsa.Arm.Sign.CS s7 s8 := fun r hr _ => hg8 r fun h => by
    simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
  have hP8' : VG.Proof.MlDsa.Arm.Sign.PPostB D s7 s8 [(sc oONES, 4)] := PostB.of_cs hcs8 hrd8 hwr8 hsp8 hf
  simp only [VG.Proof.MlDsa.Arm.Sign.hfam, Bool.and_eq_true] at g8
  have hS := VG.Proof.MlDsa.Arm.Sign.onesSum_le (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t)) i
  have hS1 := VG.Proof.MlDsa.Arm.Sign.hintOnes_le (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t) i)
  have hik : 256 * (i + 1) ≤ 256 * p.k := Nat.mul_le_mul_left _ hi
  refine ⟨⟨J7.b.step hP8' g8.1.1.1.1, Fam.keep L7 hP8' g8.1.1.1.2 J7.z, Fam.keep L7 hP8' g8.1.1.2 J7.w'',
    Fam.keep L7 hP8' g8.1.2 J7.w', HFam.keep L7 hP8' g8.2 hh7, ?_⟩, ?_⟩
  · rw [hP8'.pa (VG.Proof.MlDsa.Arm.Sign.sc_bases _), hm8, Mem.readW_writeW_self32, ho7, VG.Proof.MlDsa.Arm.Sign.onesSum_succ]
    have he7' : (s7.gpr .r0).toNat = hintOnes [VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t) i] := he7
    have ea : s7.gpr .r0 = BitVec.ofNat 32 (hintOnes [VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq; rw [he7', BitVec.toNat_ofNat]; omega
    rw [ea, ← BitVec.ofNat_add]
  · have e8 : s8.gpr .r11 = s3.gpr .r11 := by
      rw [hcs8 _ (by decide) (by decide), hcs7 _ (by decide) (by decide), hcs6 _ (by decide) (by decide),
        hcs5 _ (by decide) (by decide), hcs4 _ (by decide) (by decide)]
    rw [e8, h3]
    exact VG.Proof.MlDsa.Arm.Sign.bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
      fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## `ω` -/

theorem onesOk_run (p : Params) (hω : p.ω + 1 < 256) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES)) 4) :
    WP isa (.block (onesOk p)) s fun s' => s'.gpr .r11 = s.gpr .r11 &&&
      ((s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES)) 32 - BitVec.ofNat 32 (p.ω + 1)) >>> 31) ∧
      VG.Proof.MlDsa.Arm.Sign.Keep [.r0, .r11] s s' := by
  have enc := VG.Proof.MlDsa.Arm.Sign.encodable_small hω
  unfold onesOk
  run_block [h1, enc]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 31) (hw : w < 2 ^ 31) :
    (BitVec.ofNat 32 S - BitVec.ofNat 32 w) >>> 31 = if S < w then 1 else 0 := by
  by_cases h : S < w
  · rw [VG.Proof.MlDsa.Sign.ifp h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · rw [VG.Proof.MlDsa.Sign.ifn h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-! ## The checks -/

/-- Iteration `t` after `SampleInBall` succeeded. -/
structure KA (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)
  cc : VG.Proof.MlDsa.Arm.Sign.Pl s 0 (toRq (VG.Proof.MlDsa.Arm.Sign.cV p σ (p.ℓ * t)))
  some : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `CNT = 1`. -/
structure EP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.Arm.Sign.IK p D σ s
  ct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)
  z : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t))
  h : VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t))
  some : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome
  pass : VG.Proof.MlDsa.Arm.Sign.PassV p σ (p.ℓ * t)
  r11 : s.gpr .r11 = 1
  cnt : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 = 1
  t_lt : t < 814
  rej : VG.Proof.MlDsa.Arm.Sign.RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `CNT = 814 - t`. -/
structure EF (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.Arm.Sign.IK p D σ s
  kap : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oKAP)) 32 = BitVec.ofNat 32 (p.ℓ * (t + 1))
  cnt : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 = BitVec.ofNat 32 (814 - t)
  some : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome
  fail : ¬ VG.Proof.MlDsa.Arm.Sign.PassV p σ (p.ℓ * t)
  r11 : s.gpr .r11 = 0
  t_lt : t < 814
  rej : VG.Proof.MlDsa.Arm.Sign.RejT p σ t

/-- What the checks need of the layout. -/
def ksChk (p : Params) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) cP && VG.Proof.MlDsa.Arm.Sign.icwChk p [(cP, 1024), (sc oPS, 1024)] p.k &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oONES) 4 &&
    VG.Proof.MlDsa.Arm.Sign.kbChk p [(sc oONES, 4)] && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oONES, 4)] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oONES, 4)] (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k &&
    (List.range p.ℓ).all (VG.Proof.MlDsa.Arm.Sign.zChk p) && (List.range p.k).all (VG.Proof.MlDsa.Arm.Sign.rChk p) && (List.range p.k).all (VG.Proof.MlDsa.Arm.Sign.hChk2 p) &&
    VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oONES) 4 && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oCNT) 4 && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oKAP) 4 &&
    VG.Proof.MlDsa.Arm.Sign.kbChk p [] &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] 5 p.k &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] 5 p.k &&
    VG.Proof.MlDsa.Arm.Sign.ikChk p [(sc oCNT, 4)] && VG.Proof.MlDsa.Arm.Sign.ikChk p [(sc oKAP, 4)] && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oKAP, 4)] (sc oCNT) 4 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (sc oCT) (cLen p) && decide (p.ω + 1 < 256) && decide (p.ℓ < 256) &&
    decide (256 * p.k < 2 ^ 31) && decide (0 < p.ℓ) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oKAP) 4

theorem bit_ne {a : Prop} [Decidable a] : VG.Proof.MlDsa.Arm.Sign.bit a ≠ 0 ↔ a := by
  by_cases ha : a
  · rw [show VG.Proof.MlDsa.Arm.Sign.bit a = 1 from VG.Proof.MlDsa.Sign.ifp ha _ _]; exact ⟨fun _ => ha, fun _ => by decide⟩
  · rw [show VG.Proof.MlDsa.Arm.Sign.bit a = 0 from VG.Proof.MlDsa.Sign.ifn ha _ _]; exact ⟨fun h => absurd rfl h, fun h => absurd h ha⟩

theorem passV_iff {p : Params} {σ : State} {κ : Nat} :
    (((VG.Proof.MlDsa.Arm.Sign.ZOk p σ κ ∧ VG.Proof.MlDsa.Arm.Sign.R0Ok p σ κ) ∧ ∀ j < p.k, normRq [VG.Proof.MlDsa.Arm.Sign.CT0v p σ κ j] < p.γ₂) ∧ VG.Proof.MlDsa.Arm.Sign.onesSum (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ) p.k < p.ω + 1) ↔
      VG.Proof.MlDsa.Arm.Sign.PassV p σ κ :=
  ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, Nat.le_of_lt_succ d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, Nat.lt_succ_of_le d⟩⟩

theorem ksChk_spec {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) : ∀ {Q : Prop}, (VG.Proof.MlDsa.Arm.Sign.ipChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) cP = true →
    VG.Proof.MlDsa.Arm.Sign.icwChk p [(cP, 1024), (sc oPS, 1024)] p.k = true →
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) = true → VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oONES) 4 = true →
    VG.Proof.MlDsa.Arm.Sign.kbChk p [(sc oONES, 4)] = true → VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oONES, 4)] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oONES, 4)] (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k = true →
    (∀ r < p.ℓ, VG.Proof.MlDsa.Arm.Sign.zChk p r = true) → (∀ i < p.k, VG.Proof.MlDsa.Arm.Sign.rChk p i = true) → (∀ i < p.k, VG.Proof.MlDsa.Arm.Sign.hChk2 p i = true) →
    VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oONES) 4 = true → VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oCNT) 4 = true → VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oKAP) 4 = true →
    VG.Proof.MlDsa.Arm.Sign.kbChk p [] = true → VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] 5 p.k = true → VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] 5 p.k = true → VG.Proof.MlDsa.Arm.Sign.ikChk p [(sc oCNT, 4)] = true → VG.Proof.MlDsa.Arm.Sign.ikChk p [(sc oKAP, 4)] = true →
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oKAP, 4)] (sc oCNT) 4 = true → VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (sc oCT) (cLen p) = true →
    p.ω + 1 < 256 → p.ℓ < 256 → 256 * p.k < 2 ^ 31 → 0 < p.ℓ → VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k = true →
    VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oKAP) 4 = true → Q) → Q := by
  intro Q k
  simp only [VG.Proof.MlDsa.Arm.Sign.ksChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, hz⟩, hr⟩, hh⟩, c8⟩, c9⟩, c10⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, hω⟩, hl⟩, hk⟩, hl0⟩, c22⟩, c23⟩ := hc
  exact k c1 c2 c3 c4 c5 c6 c7 hz hr hh c8 c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 hω hl hk hl0 c22 c23

/-- The checks, after `ĉ = NTT(c)`. -/
structure KN (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s
  y : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Yv p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.wBase p) p.k (VG.Proof.MlDsa.Arm.Sign.Wv p σ (p.ℓ * t))

theorem cntt_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.Arm.Sign.KA p D σ t s) : WP isa (nttAt P cP) s (VG.Proof.MlDsa.Arm.Sign.KN p D σ t) := by
  refine VG.Proof.MlDsa.Arm.Sign.ksChk_spec hc fun c1 c2 c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have L := h.c.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.ntt L c1 h.cc.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_
  rw [h.cc.2] at hq1
  have I1 := h.c.step hP1 c2
  exact ⟨⟨I1.l, by rw [L.keepBytes hP1 c3, h.ct], by
    show PolyIs _ _ _; rw [hP1.pa (by decide)]; exact hq1, h.some⟩, I1.y, I1.w⟩

/-- `r11 ← 1`, `ONES ← 0`. -/
abbrev kInit : List Instr := [.mov .r11 (.imm 1)] ++ setW (sc oONES) 0

theorem mov11_ok (s : State) : WP isa (.block [.mov .r11 (.imm 1)]) s fun s' => s'.gpr .r11 = 1 ∧ VG.Proof.MlDsa.Arm.Sign.Keep [.r11] s s' := by
  run_block []
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

theorem kInit_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.KN p D σ t s) : WP isa (.block VG.Proof.MlDsa.Arm.Sign.kInit) s (VG.Proof.MlDsa.Arm.Sign.IZ p D σ t 0) := by
  refine VG.Proof.MlDsa.Arm.Sign.ksChk_spec hc fun _ _ _ c4 c5 c6 c7 _ _ _ _ _ _ c13 _ _ c16 _ _ _ _ _ _ _ _ _ c22 _ => ?_
  have L1 := h.b.l.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.mov11_ok s) fun s2 ⟨h152, k2⟩ => ?_
  have hP2 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s2 [] := (VG.Proof.MlDsa.Arm.Sign.postB11 k2 _).1
  have B2 := h.b.step hP2 c13
  have L2 := B2.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setW_okB L2 (by decide) (by decide) c4) fun s3 ⟨hP3, hcs3, hm3⟩ => ?_
  have y3 := Fam.keep L2 hP3 c6 (Fam.keep L1 hP2 c16 h.y)
  exact ⟨⟨B2.step hP3 c5, fun _ h => absurd h (Nat.not_lt_zero _), y3.zero,
    Fam.keep L2 hP3 c7 (Fam.keep L1 hP2 c22 h.w), by rw [hP3.pa (by decide), hm3, Mem.readW_writeW_self32]; rfl⟩,
    by rw [hcs3 _ (by decide) (by decide), h152]; exact (bit_one.mpr fun _ h => absurd h (Nat.not_lt_zero _)).symm⟩

theorem IZ.ir {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IZ p D σ t p.ℓ s) : VG.Proof.MlDsa.Arm.Sign.IR p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w.zero, h.1.ones⟩,
    by rw [h.2]; exact VG.Proof.MlDsa.Arm.Sign.bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

theorem IR.ih {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IR p D σ t p.k s) : VG.Proof.MlDsa.Arm.Sign.IH p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w'.zero, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h.1.ones]; rfl⟩,
    by rw [h.2]; exact VG.Proof.MlDsa.Arm.Sign.bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-- The checks done: whether the iteration passes in `r11`. -/
structure KO (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.Arm.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t))
  h : VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t))
  r11 : s.gpr .r11 = VG.Proof.MlDsa.Arm.Sign.bit (VG.Proof.MlDsa.Arm.Sign.PassV p σ (p.ℓ * t))

theorem onesOk_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.IH p D σ t p.k s) : WP isa (.block (onesOk p)) s (VG.Proof.MlDsa.Arm.Sign.KO p D σ t) := by
  refine VG.Proof.MlDsa.Arm.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ c13 _ _ c16 c17 _ _ _ _ hω _ hk _ _ _ => ?_
  obtain ⟨J6, h156⟩ := h
  have L6 := J6.b.l.st.lay
  have hS := VG.Proof.MlDsa.Arm.Sign.onesSum_le (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t)) p.k
  have ao : State.addr (s.gpr .r7 + BitVec.ofNat 32 oONES) = VG.Proof.MlDsa.Arm.Sign.pa s (sc oONES) := L6.w (p := sc oONES) c8 (by decide)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.onesOk_run p hω s (by rw [ao]; exact L6.iR c8)) fun s7 ⟨h157, k7⟩ => ?_
  rw [ao, J6.ones, VG.Proof.MlDsa.Arm.Sign.sign_bit (by omega) (by omega), h156, VG.Proof.MlDsa.Arm.Sign.bit_and rfl rfl, VG.Proof.MlDsa.Arm.Sign.bit_congr VG.Proof.MlDsa.Arm.Sign.passV_iff] at h157
  have hP7 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s7 [] := ⟨k7.rd, k7.wr, fun r hr => k7.gpr r (by
      simp only [VG.Proof.MlDsa.Arm.Sign.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k7.sp,
      by rw [k7.mem]; exact Frame.refl _ _⟩
  exact ⟨J6.b.step hP7 c13, Fam.keep L6 hP7 c16 J6.z, HFam.keep L6 hP7 c17 J6.h, h157⟩

/-- `κ ← κ + ℓ`. -/
abbrev kapAdd (p : Params) : List Instr :=
  [.ldr .r0 .r7 oKAP, .dp .add .r0 .r0 (.imm (BitVec.ofNat 32 p.ℓ)), .str .r0 .r7 oKAP]

theorem kBranch_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.KO p D σ t s) :
    WP isa (ifOkElse (.block (setW (sc oCNT) 1)) (.block (VG.Proof.MlDsa.Arm.Sign.kapAdd p))) s fun s' => VG.Proof.MlDsa.Arm.Sign.EP p D σ t s' ∨ VG.Proof.MlDsa.Arm.Sign.EF p D σ t s' := by
  refine VG.Proof.MlDsa.Arm.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 _ hl _ _ _ c23 => ?_
  have B7 := h.b
  have L7 := B7.l.st.lay
  refine VG.Proof.MlDsa.Arm.Sign.ifOkElse_ok (D := D) (fun s8 hP8 hcs8 hm8 hne => ?_) fun s8 hP8 hcs8 hm8 he => ?_
  · rw [h.r11] at hne
    have hpass := bit_ne.mp hne
    have B8 := B7.step hP8 c13
    have L8 := B8.l.st.lay
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setW_okB L8 (by decide) (by decide) c9) fun s9 ⟨hP9, hcs9, hm9⟩ => ?_
    exact .inl ⟨B8.l.k.step hP9 c18, by rw [L8.keepBytes hP9 c21, B8.ct],
      Fam.keep L8 hP9 c14 (Fam.keep L7 hP8 c16 h.z), HFam.keep L8 hP9 c15 (HFam.keep L7 hP8 c17 h.h), B8.some,
      hpass, by rw [hcs9 _ (by decide) (by decide), hcs8 _ (by decide) (by decide), h.r11]; exact bit_one.mpr hpass,
      by rw [hP9.pa (by decide), hm9, Mem.readW_writeW_self32]; rfl, B8.l.t_lt, B8.l.rej⟩
  · rw [h.r11] at he
    have hfail : ¬ VG.Proof.MlDsa.Arm.Sign.PassV p σ (p.ℓ * t) := fun hp => (bit_ne.mpr hp) he
    have B8 := B7.step hP8 c13
    have L8 := B8.l.st.lay
    have ak : State.addr (s8.gpr .r7 + BitVec.ofNat 32 oKAP) = VG.Proof.MlDsa.Arm.Sign.pa s8 (sc oKAP) := L8.pa32W (p := sc oKAP) c10 (by decide)
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.addW_ok (sc oKAP) p.ℓ (by decide) (by decide) (VG.Proof.MlDsa.Arm.Sign.encodable_small hl) s8 (by rw [ak]; exact L8.iW c10))
      fun s9 ⟨hm9, hg9, hrd9, hwr9, hsp9⟩ => ?_
    rw [ak] at hm9
    have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s8 (sc oKAP), 4⟩] s8.mem s9.mem := by
      rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hcs9 : VG.Proof.MlDsa.Arm.Sign.CS s8 s9 := fun r hr _ => hg9 r fun h => by
      simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    have hP9' : VG.Proof.MlDsa.Arm.Sign.PPostB D s8 s9 [(sc oKAP, 4)] := PostB.of_cs hcs9 hrd9 hwr9 hsp9 hf
    refine .inr ⟨B8.l.k.step hP9' c19, ?_, by rw [L8.keepW hP9' c20, B8.l.cnt], B8.some, hfail,
      by rw [hcs9 _ (by decide) (by decide), hcs8 _ (by decide) (by decide), h.r11]; exact bit_zero.mpr hfail,
      B8.l.t_lt, B8.l.rej⟩
    rw [hP9'.pa (by decide), hm9, Mem.readW_writeW_self32, B8.l.kap, ← BitVec.ofNat_add, Nat.mul_succ]

theorem checks_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.Arm.Sign.KA p D σ t s) :
    WP isa (checks P p) s fun s' => VG.Proof.MlDsa.Arm.Sign.EP p D σ t s' ∨ VG.Proof.MlDsa.Arm.Sign.EF p D σ t s' := by
  refine VG.Proof.MlDsa.Arm.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.cntt_ok hP hc h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.kInit_ok hc h1) fun s3 I3 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.Arm.Sign.IZ p D σ t r) p.ℓ 0 (fun r _ hr s hs => VG.Proof.MlDsa.Arm.Sign.zR_ok hP (hz r (by omega)) hs)
    s3 I3) fun s4 hs4 => ?_)
  rw [Nat.zero_add] at hs4
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.Arm.Sign.IR p D σ t i) p.k 0 (fun i _ hi s hs => VG.Proof.MlDsa.Arm.Sign.r0R_ok hP (hr i (by omega)) hs)
    s4 hs4.ir) fun s5 hs5 => ?_)
  rw [Nat.zero_add] at hs5
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun i => VG.Proof.MlDsa.Arm.Sign.IH p D σ t i) p.k 0 (fun i _ hi s hs => VG.Proof.MlDsa.Arm.Sign.hR_ok hP (hh i (by omega)) hs)
    s5 hs5.ih) fun s6 hs6 => ?_)
  rw [Nat.zero_add] at hs6
  exact WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.onesOk_ok hc hs6) fun s7 h7 => VG.Proof.MlDsa.Arm.Sign.kBranch_ok hc h7)

theorem ksChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.ksChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem bChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.bChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseL`. -/
section

/-!
# ML-DSA signing on ARMv7: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `r11 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `r11 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem paramsOk {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : ParamsOk p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List VG.Spec.MlDsa.Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ)) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List VG.Spec.MlDsa.Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ)) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    VG.Proof.MlDsa.Arm.Sign.iterF p σ b κ = (VG.Spec.MlDsa.sampleInBall p.τ b.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)).map fun c =>
      (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ, if passF p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S1v p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.T0v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (VG.Proof.MlDsa.Arm.Sign.S1v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ c),
          (List.range p.k).map (hF p (VG.Proof.MlDsa.Arm.Sign.Am p σ) (VG.Proof.MlDsa.Arm.Sign.S2v p σ) (VG.Proof.MlDsa.Arm.Sign.T0v p σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)).isSome) :
    VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ) = some (VG.Proof.MlDsa.Arm.Sign.cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [VG.Proof.MlDsa.Arm.Sign.cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)).isSome)
    (hf : ¬ VG.Proof.MlDsa.Arm.Sign.PassV p σ κ) : VG.Proof.MlDsa.Arm.Sign.iterF p σ maxBounds κ = some (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ, none) := by
  rw [VG.Proof.MlDsa.Arm.Sign.iterF_eq hp, VG.Proof.MlDsa.Arm.Sign.cV_eq h, Option.map_some, VG.Proof.MlDsa.Sign.ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)).isSome)
    (hf : VG.Proof.MlDsa.Arm.Sign.PassV p σ κ) : VG.Proof.MlDsa.Arm.Sign.iterF p σ maxBounds κ =
      some (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ, some ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.Zv p σ κ), (List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ))) := by
  rw [VG.Proof.MlDsa.Arm.Sign.iterF_eq hp, VG.Proof.MlDsa.Arm.Sign.cV_eq h, Option.map_some, VG.Proof.MlDsa.Sign.ifp hf]

theorem iter_none (h : VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ) = none) : VG.Proof.MlDsa.Arm.Sign.iterF p σ minBounds κ = none := by
  rw [VG.Proof.MlDsa.Arm.Sign.iterF, signIteration_eq, signCommit_eq, h]; rfl

end

/-! ## The end of the loop -/

/-- The loop ended: in `r11`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : VG.Proof.MlDsa.Arm.Sign.IK p D σ s
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  pass : s.gpr .r11 = 1 → ∃ t < 814, VG.Proof.MlDsa.Arm.Sign.RejT p σ t ∧
    (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome ∧ VG.Proof.MlDsa.Arm.Sign.PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t) ∧ VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ (p.ℓ * t)) ∧
    VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ (p.ℓ * t))
  fail : s.gpr .r11 = 0 → VG.Proof.MlDsa.Arm.Sign.loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `r11 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.Arm.Sign.IK p D σ s
  none : VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)) = none
  r11 : s.gpr .r11 = 0
  cnt : s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 = 1
  t_lt : t < 814
  rej : VG.Proof.MlDsa.Arm.Sign.RejT p σ t

theorem rej_zero {p : Params} {σ : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sign.RejT p σ t) :
    Rej p (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ))
      ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ)) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) maxBounds 0 t := h

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sign.RejT p σ t)
    (hn : VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t)) = none) : VG.Proof.MlDsa.Arm.Sign.loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.Arm.Sign.iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : VG.Proof.MlDsa.Arm.Sign.RejT p σ 814) : VG.Proof.MlDsa.Arm.Sign.loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## An iteration -/

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.z = false ∧ VG.Proof.MlDsa.Arm.Sign.IL p D σ (t + 1) s) ∨ (s.z = true ∧ VG.Proof.MlDsa.Arm.Sign.XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oCNT) 4 && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oCNT) 4 && VG.Proof.MlDsa.Arm.Sign.ikChk p [(sc oCNT, 4)] && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (sc oKAP) 4 &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (sc oCT) (cLen p) && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oCNT, 4)] 5 p.k && VG.Proof.MlDsa.Arm.Sign.icwChk p [] p.k && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (sc oCT) (cLen p) &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [] cP 1024 && VG.Proof.MlDsa.Arm.Sign.ikChk p [] &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(sc oKAP, 4)] (sc oCNT) 4 && VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgW p) (sc oKAP) 4 && VG.Proof.MlDsa.Arm.Sign.ikChk p [(sc oKAP, 4)]

theorem lChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ofNat32_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 32) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  rw [this]
  omega

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- `CNT ← CNT - 1`, setting Z when it reaches 0. -/
abbrev decCnt : List Instr := [.ldr .r0 .r7 oCNT, .subs .r0 .r0 (.imm 1), .str .r0 .r7 oCNT]

/-- `decW_ok` in the layout. -/
theorem decCnt_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s)
    (w1 : VG.Proof.MlDsa.Arm.Sign.inB wbs (sc oCNT) 4 = true) :
    WP isa (.block VG.Proof.MlDsa.Arm.Sign.decCnt) s fun s' => (s'.mem = s.mem.writeW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) (s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 - 1) ∧
      s'.z = (s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 - 1 == 0)) ∧ VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [(sc oCNT, 4)] ∧ VG.Proof.MlDsa.Arm.Sign.CS s s' := by
  have ac : State.addr (s.gpr .r7 + BitVec.ofNat 32 oCNT) = VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT) := L.pa32W (p := sc oCNT) w1 (by decide)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.decW_ok (sc oCNT) (by decide) (by decide) s (by rw [ac]; exact L.iW w1))
    fun s' ⟨⟨hm, hz⟩, hg, hrd, hwr, hsp⟩ => ?_
  rw [ac] at hm hz
  have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT), 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcs : VG.Proof.MlDsa.Arm.Sign.CS s s' := fun r hr _ => hg r fun h => by
    simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
  exact ⟨⟨hm, hz⟩, PostB.of_cs hcs hrd hwr hsp hf, hcs⟩

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.Arm.Sign.EF p D σ t s ∨ VG.Proof.MlDsa.Arm.Sign.EB p D σ t s) :
    WP isa (.block VG.Proof.MlDsa.Arm.Sign.decCnt) s (VG.Proof.MlDsa.Arm.Sign.LP p D σ t) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : VG.Proof.MlDsa.Arm.Sign.IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.decCnt_okB L w1) fun s' ⟨⟨hm, hz⟩, hP, hcs⟩ => ?_
  have K := hk.step hP k1
  have e15 : s'.gpr .r11 = s.gpr .r11 := hcs _ (by decide) (by decide)
  rcases h with h | h | h
  · -- passed
    rw [h.cnt] at hz
    refine .inr ⟨by rw [hz]; rfl, K, .inr (e15.trans h.r11), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.r11)) (by decide)⟩
  · -- rejected
    have hr : VG.Proof.MlDsa.Arm.Sign.RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.Arm.Sign.iter_rej hp h.some h.fail)
    rw [h.cnt, VG.Proof.MlDsa.Arm.Sign.ofNat32_sub_one (by have := h.t_lt; omega) (by have := h.t_lt; omega),
      VG.Proof.MlDsa.Arm.Sign.ofNat32_beq_zero (by have := h.t_lt; omega)] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r11),
        fun h1 => absurd (h1.symm.trans (e15.trans h.r11)) (by decide), fun _ => VG.Proof.MlDsa.Arm.Sign.loop_none_exh hr⟩
    · have hne : decide (814 - t - 1 = 0) = false := by have := h.t_lt; simp only [decide_eq_false_iff_not]; omega
      refine .inl ⟨by rw [hz, hne], K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega, hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self32, h.cnt,
        VG.Proof.MlDsa.Arm.Sign.ofNat32_sub_one (by have := h.t_lt; omega) (by have := h.t_lt; omega), Nat.sub_sub]
  · -- `SampleInBall` failed
    rw [h.cnt] at hz
    exact .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r11),
      fun h1 => absurd (h1.symm.trans (e15.trans h.r11)) (by decide), fun _ => VG.Proof.MlDsa.Arm.Sign.loop_none_ball h.rej h.none⟩

theorem cmp0_ok (s : State) : WP isa (.block [.cmp .r0 (.imm 0)]) s fun s₁ =>
    s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r0 == 0) := by
  run_block []
  simp

theorem IB.step0 {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.Arm.Sign.IB p D σ t s) (hc : VG.Proof.MlDsa.Arm.Sign.lChk p = true)
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' []) (hax : s'.gpr .r0 = s.gpr .r0) : VG.Proof.MlDsa.Arm.Sign.IB p D σ t s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, c1⟩, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := h.c.l.st.lay
  refine ⟨h.c.step hP c1, by rw [L.keepBytes hP c2, h.ct], hax ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (hax ▸ h0)⟩
  obtain ⟨hc', hs⟩ := h.ok (hax ▸ h1)
  exact ⟨L.keepPoly hP c3 hc', hs⟩

theorem test_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IB p D σ t s) :
    WP isa (.block [.cmp .r0 (.imm 0)]) s fun s' =>
      (VG.Proof.MlDsa.Arm.Sign.IB p D σ t s' ∧ s'.z = (s'.gpr .r0 == 0)) ∧ s'.gpr .r0 = s.gpr .r0 := by
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.cmp0_ok s) fun s3 ⟨g3, hm3, hrd, hwr, hsp, hz3⟩ => ?_
  have hcs : VG.Proof.MlDsa.Arm.Sign.CS s s3 := fun r _ _ => by rw [g3]
  have hP3 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s3 [] := PostB.of_cs hcs hrd hwr hsp (by rw [hm3]; exact Frame.refl _ _)
  have hax3 : s3.gpr .r0 = s.gpr .r0 := by rw [g3]
  exact ⟨⟨h.step0 hc4 hP3 hax3, by rw [hz3, hax3]⟩, hax3⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IB p D σ t s)
    (h1 : s.gpr .r0 = 1) : VG.Proof.MlDsa.Arm.Sign.KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem mov0_ok (s : State) : WP isa (.block [.mov .r11 (.imm 0)]) s fun s' => s'.gpr .r11 = 0 ∧ VG.Proof.MlDsa.Arm.Sign.Keep [.r11] s s' := by
  run_block []
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

theorem else_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IB p D σ t s)
    (h0 : s.gpr .r0 = 0) :
    WP isa (.block (([.mov .r11 (.imm 0)] : List Instr) ++ setW (sc oCNT) 1)) s (VG.Proof.MlDsa.Arm.Sign.EB p D σ t) := by
  have hc4' := hc4
  simp only [VG.Proof.MlDsa.Arm.Sign.lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.mov0_ok s) fun s4 ⟨h154, k4⟩ => ?_
  have hP4 : VG.Proof.MlDsa.Arm.Sign.PPostB D s s4 [] := (VG.Proof.MlDsa.Arm.Sign.postB11 k4 _).1
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setW_okB L4 (by decide) (by decide) w1) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5 _ (by decide) (by decide), h154],
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self32]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {s : State} (hk : VG.Proof.MlDsa.Arm.Sign.IK p D σ s) :
    WP isa (.block VG.Proof.MlDsa.Arm.Sign.decCnt) s fun s' =>
      s'.z = (s.mem.readW (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCNT)) 32 - 1 == 0) ∧ s'.gpr .r11 = s.gpr .r11 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' (sc oCT)) (cLen p) = bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) ∧
      ∀ f, VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.Arm.Sign.HFam s' 5 p.k f := by
  simp only [VG.Proof.MlDsa.Arm.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.decCnt_okB L w1) fun s' ⟨⟨_, hz⟩, hP, hcs⟩ => ?_
  exact ⟨hz, hcs _ (by decide) (by decide), L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem iter_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.Arm.Sign.cChk p = true)
    (hc2 : VG.Proof.MlDsa.Arm.Sign.bChk p = true) (hc3 : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) : WP isa (iter P p) s (VG.Proof.MlDsa.Arm.Sign.LP p D σ t) := by
  unfold iter
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.ball_ok hP hc2 h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.test_ok hc4 h2) fun s3 ⟨⟨I3, hz3⟩, _⟩ => ?_)
  refine WP.seq (WP.ite (M := isa) (!(s3.gpr .r0 == 0)) (show some (!s3.z) = _ by rw [hz3])
    (fun hb => ?_) fun hb => ?_)
  · have h1 : s3.gpr .r0 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.checks_ok hP hc3 (I3.ka h1)) fun s' h' => VG.Proof.MlDsa.Arm.Sign.dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (VG.Proof.MlDsa.Arm.Sign.else_ok hc4 I3 (by simpa using hb)) fun s' h' => VG.Proof.MlDsa.Arm.Sign.dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IK p D σ s) :
    WP isa (.block (setW (sc oKAP) 0 ++ setW (sc oCNT) 814)) s (VG.Proof.MlDsa.Arm.Sign.IL p D σ 0) := by
  have hc4' := hc4
  simp only [VG.Proof.MlDsa.Arm.Sign.lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setW_okB L (by decide) (by decide) wk) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setW_okB K1.d.im.st.lay (by decide) (by decide) w1) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self32]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self32], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.Arm.Sign.cChk p = true)
    (hc2 : VG.Proof.MlDsa.Arm.Sign.bChk p = true) (hc3 : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {σ : State} {s : State}
    (h : VG.Proof.MlDsa.Arm.Sign.IK p D σ s) : WP isa (Impl.MlDsa.Arm.Sign.signLoop P p) s (VG.Proof.MlDsa.Arm.Sign.XS p D σ) := by
  unfold Impl.MlDsa.Arm.Sign.signLoop
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.iter_ok hP hp hc1 hc2 hc3 hc4 hs) fun s' h' => ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [hev, hz]; rfl, 814 - (t + 1), by have := hs.t_lt; omega, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [hev, hz]; rfl, hX⟩

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseO`. -/
section

/-!
# ML-DSA signing on ARMv7: the signature

Once an iteration passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r`
(in range, as `z` passed its norm check: `inRange_of_norm`), then
`HintBitPack(h)` (with at most `ω` 1s) to `sig`, which then holds
`sigEncode(c̃, z mod± q, h)` (`output_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : VG.Proof.MlDsa.Arm.Sign.InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [VG.Proof.MlDsa.Arm.Sign.coeff_val h hi]
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
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = VG.Proof.MlDsa.Arm.Sign.onesSum f k := by
  simp only [hintOnes, VG.Proof.MlDsa.Arm.Sign.onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    VG.Proof.MlDsa.Arm.Sign.pa s (pS (5 + i)) = VG.Proof.MlDsa.Arm.Sign.pa s (Impl.MlDsa.Arm.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show VG.Proof.MlDsa.Arm.Sign.pa s (.r7, oP (5 + i)) = VG.Proof.MlDsa.Arm.Sign.pa s (.r7, oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [← VG.Proof.MlDsa.Arm.Sign.pa_add, show oP (5 + 0) + 1024 * i = oP (5 + i) by simp only [oP]; omega]

theorem r8_bases (o : Nat) : ((.r8, o) : Ptr).1 ∈ VG.Proof.MlDsa.Arm.Sign.bases := by
  show Reg.r8 ∈ VG.Proof.MlDsa.Arm.Sign.bases; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => VG.Spec.MlDsa.bitPack ((VG.Proof.MlDsa.Arm.Sign.Zv p σ κ j).map fun c => modPm c.val VG.Spec.MlDsa.q) (p.γ₁ - 1) p.γ₁

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.Arm.Sign.IK p D σ s
  z : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ κ)
  h : VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ)
  sig : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (.r8, 0)) (cLen p + zLen p * r) = VG.Proof.MlDsa.Arm.Sign.CTv p σ κ ++ VG.Proof.MlDsa.Arm.Sign.zEnc p σ κ r
  r11 : s.gpr .r11 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.ikChk p ws && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : VG.Proof.MlDsa.Arm.Sign.OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D s s' ws) (hc : VG.Proof.MlDsa.Arm.Sign.ofam p ws = true)
    (hs : VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) ws (.r8, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .r11 = s.gpr .r11) :
    VG.Proof.MlDsa.Arm.Sign.OS p D σ κ r s' := by
  simp only [VG.Proof.MlDsa.Arm.Sign.ofam, Bool.and_eq_true] at hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.r11⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.copyChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (.r8, 0) (sc oCT) (cLen p) && VG.Proof.MlDsa.Arm.Sign.ofam p [((.r8, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => VG.Proof.MlDsa.Arm.Sign.rwChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (yP p r) 1024 (.r8, sigZ p r) (zLen p) &&
      VG.Proof.MlDsa.Arm.Sign.ofam p [((.r8, sigZ p r), zLen p)] && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [((.r8, sigZ p r), zLen p)] (.r8, 0) (cLen p + zLen p * r)) &&
    VG.Proof.MlDsa.Arm.Sign.rwChk (VG.Proof.MlDsa.Arm.Sign.sgB p) (VG.Proof.MlDsa.Arm.Sign.sgW p) (hP 0) (256 * p.k * 4) (.r8, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    VG.Proof.MlDsa.Arm.Sign.ikChk p [((.r8, sigH p), p.ω + p.k)] &&
    VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [((.r8, sigH p), p.ω + p.k)] (.r8, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ, (List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.Zv p σ κ), (List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ))

section
variable {P : Prims} {D : Nat} (hPO : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.oChk p = true) {σ : State} {κ : Nat}
include hc

omit hPO in
theorem outCopy_ok {s : State} (hk : VG.Proof.MlDsa.Arm.Sign.IK p D σ s) (hct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)
    (hz : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ κ)) (hh : VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ)) (h15 : s.gpr .r11 = 1) :
    WP isa (copy (.r8, 0) (sc oCT) (cLen p)) s fun s1 =>
      VG.Proof.MlDsa.Arm.Sign.OS p D σ κ 0 s1 ∧ ∀ f, VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.Arm.Sign.HFam s1 5 p.k f := by
  simp only [VG.Proof.MlDsa.Arm.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_
  simp only [VG.Proof.MlDsa.Arm.Sign.ofam, Bool.and_eq_true] at c0
  refine ⟨⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
    by rw [hcs1 _ (by decide) (by decide), h15]⟩, fun f h => HFam.keep L hP1 c0.2 h⟩
  rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
  simp [VG.Proof.MlDsa.Arm.Sign.zEnc]

include hPO in
theorem packZ_ok {r : Nat} (hr : r < p.ℓ) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.OS p D σ κ r s) (hpass : VG.Proof.MlDsa.Arm.Sign.PassV p σ κ) :
    WP isa (packZ P p r) s fun s' => VG.Proof.MlDsa.Arm.Sign.OS p D σ κ (r + 1) s' ∧ ∀ f, VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.Arm.Sign.HFam s' 5 p.k f := by
  simp only [VG.Proof.MlDsa.Arm.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, cz⟩, -⟩, -⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := cz r hr
  have Lh := h.k.d.im.st.lay
  have hzr := h.z r hr
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.bpAt_ok hPO Lh hbp hzl c1 hzr.1 (VG.Proof.MlDsa.Arm.Sign.inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)))
    fun s' ⟨hP', hcs', hb'⟩ => ?_
  have O' := h.step hP' c2 c3 (hcs' _ (by decide) (by decide))
  have c2' := c2
  simp only [VG.Proof.MlDsa.Arm.Sign.ofam, Bool.and_eq_true] at c2'
  refine ⟨⟨O'.k, O'.z, O'.h, ?_, O'.r11⟩, fun f hf => HFam.keep Lh hP' c2'.2 hf⟩
  rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, ← VG.Proof.MlDsa.Arm.Sign.pa_add, Nat.zero_add,
    hP'.pa (VG.Proof.MlDsa.Arm.Sign.r8_bases _), hb', hzr.2, VG.Proof.MlDsa.Arm.Sign.zEnc, VG.Proof.MlDsa.Arm.Sign.zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

omit hc in
theorem hones_ok {s : State} (h : VG.Proof.MlDsa.Arm.Sign.OS p D σ κ p.ℓ s) (hpass : VG.Proof.MlDsa.Arm.Sign.PassV p σ κ) :
    hintOnes (hintAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (Impl.MlDsa.Arm.Sign.hP 0)) p.k) ≤ p.ω := by
  rw [VG.Proof.MlDsa.Arm.Sign.hintAt_of (f := VG.Proof.MlDsa.Arm.Sign.Hv p σ κ) fun i hi => by
      have := h.h i hi; rwa [VG.Proof.MlDsa.Arm.Sign.pS_hint] at this,
    VG.Proof.MlDsa.Arm.Sign.hintOnes_map]
  exact hpass.2.2.2

include hPO in
theorem hpack_ok {s : State} (h2 : VG.Proof.MlDsa.Arm.Sign.OS p D σ κ p.ℓ s) (hpass : VG.Proof.MlDsa.Arm.Sign.PassV p σ κ) :
    WP isa (hintBitPackAt P (Impl.MlDsa.Arm.Sign.hP 0) (256 * p.k) p.ω (.r8, sigH p) (p.ω + p.k)) s fun s' =>
      VG.Proof.MlDsa.Arm.Sign.IK p D σ s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' (.r8, 0)) p.sigLen = VG.Proof.MlDsa.Arm.Sign.sigV p σ κ ∧ s'.gpr .r11 = 1 := by
  simp only [VG.Proof.MlDsa.Arm.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ch⟩, hhp⟩, -⟩, -⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L2 := h2.k.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.hbpAt_ok hPO L2 hhp ch (VG.Proof.MlDsa.Arm.Sign.hones_ok h2 hpass)) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3 _ (by decide) (by decide), h2.r11]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), ← VG.Proof.MlDsa.Arm.Sign.pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, VG.Proof.MlDsa.Arm.Sign.hintAt_of (f := VG.Proof.MlDsa.Arm.Sign.Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [VG.Proof.MlDsa.Arm.Sign.pS_hint] at this]
  simp only [VG.Proof.MlDsa.Arm.Sign.sigV, sigOf, sigEncode, VG.Proof.MlDsa.Arm.Sign.zEnc, List.map_map, List.flatMap_map]
  rfl

include hPO in
theorem output_ok {s : State} (hk : VG.Proof.MlDsa.Arm.Sign.IK p D σ s) (hct : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)
    (hz : VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ κ)) (hh : VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ)) (hpass : VG.Proof.MlDsa.Arm.Sign.PassV p σ κ)
    (h15 : s.gpr .r11 = 1) :
    WP isa (output P p) s fun s' => VG.Proof.MlDsa.Arm.Sign.IK p D σ s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.Arm.Sign.pa s' (.r8, 0)) p.sigLen = VG.Proof.MlDsa.Arm.Sign.sigV p σ κ ∧
      s'.gpr .r11 = 1 := by
  unfold output
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.outCopy_ok hc hk hct hz hh h15) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun r => VG.Proof.MlDsa.Arm.Sign.OS p D σ κ r) p.ℓ 0
    (fun r _ hr s h => WP.mono (VG.Proof.MlDsa.Arm.Sign.packZ_ok hPO hc (by omega) h hpass) fun _ h => h.1) s1 h1.1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact VG.Proof.MlDsa.Arm.Sign.hpack_ok hPO hc h2 hpass

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Correct`. -/
section

/-!
# ML-DSA signing on ARMv7: correctness

The function returns 1 with `Sign_internal`'s signature (within `maxBounds`)
in `sig`, or 0 when `Sign_internal` returns nothing within `minBounds`
(`sign_correct`): its `ExpandA` or its loop does not finish (`signMu_min_A`,
`signMu_min_L`), or an iteration passes (`signMu_max`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.Arm.Sign.seedE p σ (p.ℓ * i + j) = aSeed (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.Arm.Sign.seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.seedE p σ e)).isSome) :
    expandA p maxBounds (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)) :=
  VG.Proof.MlDsa.Sign.expandA_some fun i hi j hj => by rw [← VG.Proof.MlDsa.Arm.Sign.seedE_ij hj]; exact hok _ (VG.Proof.MlDsa.Arm.Sign.ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.Arm.Sign.seedE p σ e) = none) :
    signMu p minBounds (VG.Proof.MlDsa.Arm.Sign.skOf p σ) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (VG.Proof.MlDsa.Sign.expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)))
    (hL : VG.Proof.MlDsa.Arm.Sign.loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (VG.Proof.MlDsa.Arm.Sign.skOf p σ) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rndOf σ) = none := by
  cases e : expandA p minBounds (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := VG.Proof.MlDsa.Sign.expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ))) {t : Nat}
    (ht : t < 814) (hr : VG.Proof.MlDsa.Arm.Sign.RejT p σ t) (hs : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ (p.ℓ * t))).isSome)
    (hpass : VG.Proof.MlDsa.Arm.Sign.PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (VG.Proof.MlDsa.Arm.Sign.skOf p σ) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rndOf σ) = some (VG.Proof.MlDsa.Arm.Sign.sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega) (VG.Proof.MlDsa.Arm.Sign.iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `r11`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : VG.Proof.MlDsa.Arm.Sign.St p D σ s
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  ok : s.gpr .r11 = 1 →
    signMu p maxBounds (VG.Proof.MlDsa.Arm.Sign.skOf p σ) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rndOf σ) = some (bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (.r8, 0)) p.sigLen)
  bad : s.gpr .r11 = 0 → signMu p minBounds (VG.Proof.MlDsa.Arm.Sign.skOf p σ) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.stChk p [] && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.aBase p) (p.k * p.ℓ) && VG.Proof.MlDsa.Arm.Sign.ikChk p [] && VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.Arm.Sign.famChk (VG.Proof.MlDsa.Arm.Sign.sgB p) [] 5 p.k && VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [] (sc oCT) (cLen p) &&
    VG.Proof.MlDsa.Arm.Sign.inB (VG.Proof.MlDsa.Arm.Sign.sgB p) (sc oSV) 36 &&
    decide (VG.Proof.MlDsa.Arm.Sign.scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32)

theorem fChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  VG.Proof.MlDsa.Arm.Sign.aChk p && VG.Proof.MlDsa.Arm.Sign.dChk p && VG.Proof.MlDsa.Arm.Sign.cChk p && VG.Proof.MlDsa.Arm.Sign.bChk p && VG.Proof.MlDsa.Arm.Sign.ksChk p && VG.Proof.MlDsa.Arm.Sign.lChk p && VG.Proof.MlDsa.Arm.Sign.oChk p && VG.Proof.MlDsa.Arm.Sign.fChk p

theorem allChk_ok {p : Params} (h : VG.Proof.MlDsa.Arm.Sign.Ok3 p) : VG.Proof.MlDsa.Arm.Sign.allChk p = true := by
  simp only [VG.Proof.MlDsa.Arm.Sign.allChk, VG.Proof.MlDsa.Arm.Sign.aChk_ok h, VG.Proof.MlDsa.Arm.Sign.dChk_ok h, VG.Proof.MlDsa.Arm.Sign.cChk_ok h, VG.Proof.MlDsa.Arm.Sign.bChk_ok h, VG.Proof.MlDsa.Arm.Sign.ksChk_ok h, VG.Proof.MlDsa.Arm.Sign.lChk_ok h, VG.Proof.MlDsa.Arm.Sign.oChk_ok h, VG.Proof.MlDsa.Arm.Sign.fChk_ok h,
    Bool.and_self]

theorem r11_one {s : State} (h : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1) (hne : s.gpr .r11 ≠ 0) : s.gpr .r11 = 1 := by
  rcases h with e | e
  · exact absurd e hne
  · exact e

theorem rest_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) {σ s : State} (h : VG.Proof.MlDsa.Arm.Sign.IM p D σ s) :
    WP isa (rest P p) s (VG.Proof.MlDsa.Arm.Sign.FS p D σ) := by
  have hc := VG.Proof.MlDsa.Arm.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.Arm.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.Arm.Sign.fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf'
  have hp := VG.Proof.MlDsa.Arm.Sign.paramsOk h3
  have hA := VG.Proof.MlDsa.Arm.Sign.expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.decode_ok hP hd h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.signLoop_ok hP hp hc1 hb hks hl h1) fun s2 h2 => ?_)
  have L2 := h2.k.d.im.st.lay
  unfold ifOk
  refine VG.Proof.MlDsa.Arm.Sign.ifOkElse_ok (D := D) (fun s3 hP3 hcs3 hm3 hne => ?_) fun s3 hP3 hcs3 hm3 he => ?_
  · have h15 := VG.Proof.MlDsa.Arm.Sign.r11_one h2.r01 hne
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h15
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.output_ok hP ho (h2.k.step hP3 ik) (by rw [L2.keepBytes hP3 kct, hct])
      (Fam.keep L2 hP3 fy hz) (HFam.keep L2 hP3 f5 hh) hpass (by rw [hcs3 _ (by decide) (by decide), h15]))
      fun s4 ⟨k4, hb4, h154⟩ => ⟨k4.d.im.st, .inr h154, fun _ => by rw [hb4]; exact VG.Proof.MlDsa.Arm.Sign.signMu_max hp hA ht hr hs hpass,
        fun h0 => absurd (h0.symm.trans h154) (by decide)⟩
  · have h15 := he
    have e15 : s3.gpr .r11 = 0 := by rw [hcs3 _ (by decide) (by decide), h15]
    exact WP.block_nil ⟨(h2.k.step hP3 ik).d.im.st, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
      fun _ => VG.Proof.MlDsa.Arm.Sign.signMu_min_L hA (h2.fail h15)⟩

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨State.addr (σ.gpr r), len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (b, 0)) len = bytesAt σ.mem (State.addr (σ.gpr r)) len := by
  rw [VG.Proof.MlDsa.Arm.Sign.pa, hb, BitVec.add_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {p : Params} {D : Nat} (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) {σ s : State}
    (hpre : (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ) (ht : VG.Proof.MlDsa.Arm.Sign.Top σ s) (hf : Frame [⟨State.addr (stackArg σ 0), VG.Proof.MlDsa.Arm.Sign.scrLen p⟩] σ.mem s.mem) :
    VG.Proof.MlDsa.Arm.Sign.St p D σ s := by
  have hc := VG.Proof.MlDsa.Arm.Sign.fChk_ok h3
  simp only [VG.Proof.MlDsa.Arm.Sign.fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hsz := hc.2
  have hpre' := hpre
  obtain ⟨_, _, -, d2, -, d4, -, d6, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre'
  exact ⟨ht, VG.Proof.MlDsa.Arm.Sign.sgLay hpre hsz ht,
    VG.Proof.MlDsa.Arm.Sign.entry_bytes hf d2 (by omega) (ht.regs .r4 (by decide)),
    VG.Proof.MlDsa.Arm.Sign.entry_bytes hf d4 (by omega) (ht.regs .r5 (by decide)),
    VG.Proof.MlDsa.Arm.Sign.entry_bytes hf d6 (by omega) (ht.regs .r6 (by decide))⟩

theorem sign_correct {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) (σ : State)
    (hpre : (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ) :
    ∃ t s', Exec isa (Impl.MlDsa.Arm.Sign.sign P p) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlDsa.Arm.Sign.signK p D).post σ s' := by
  have hc := VG.Proof.MlDsa.Arm.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.Arm.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.Arm.Sign.fChk, Bool.and_eq_true, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, hsv⟩, hsz⟩ := hf'
  have main : WP isa (Impl.MlDsa.Arm.Sign.sign P p) σ fun s₅ => (∀ r ∈ preserved, s₅.gpr r = σ.gpr r) ∧
      s₅.sp = σ.sp ∧ ∃ s₄, VG.Proof.MlDsa.Arm.Sign.FS p D σ s₄ ∧ s₅.gpr .r0 = s₄.gpr .r11 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.Arm.Sign.sign
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.pro_ok hpre) fun s₁ ⟨h₁, hf₁, h15⟩ => ?_)
    have S1 := VG.Proof.MlDsa.Arm.Sign.entry_st h3 hpre h₁ hf₁
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.expandA_ok hP ha S1 h15) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (VG.Proof.MlDsa.Arm.Sign.FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine VG.Proof.MlDsa.Arm.Sign.ifOkElse_ok (D := D) (fun s₃ hP₃ hcs₃ hm₃ hne => ?_) fun s₃ hP₃ hcs₃ hm₃ he => ?_
      · have h1 := VG.Proof.MlDsa.Arm.Sign.r11_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact VG.Proof.MlDsa.Arm.Sign.rest_ok hP h3 ⟨h₂.st.step hP₃ st0, ok, Fam.keep h₂.st.lay hP₃ fa0 fam⟩
      · have h0 := he
        have e15 : s₃.gpr .r11 = 0 := by rw [hcs₃ _ (by decide) (by decide), h0]
        exact WP.block_nil ⟨h₂.st.step hP₃ st0, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
          fun _ => VG.Proof.MlDsa.Arm.Sign.signMu_min_A (h₂.bad h0)⟩
    · have hn := h₄.st.lay.nw (.r7, VG.Proof.MlDsa.Arm.Sign.scrLen p) (by simp)
      have hge := VG.Proof.MlDsa.Arm.Sign.scrLen_ge p
      exact WP.mono (VG.Proof.MlDsa.Arm.Sign.topEnd_ok h₄.st.top (h₄.st.lay.iR hsv) (by simp only at hn; omega))
        fun s₅ ⟨hr, hg, hm, hsp⟩ => ⟨hg, hsp.trans h₄.st.top.sp, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, hsp, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, ⟨hg, hsp⟩, ?_⟩
  have e14 : VG.Proof.MlDsa.Arm.Sign.pa s₄ (.r8, 0) = State.addr (σ.gpr .r3) := by
    rw [VG.Proof.MlDsa.Arm.Sign.pa, h₄.st.top.regs .r8 (by decide), BitVec.add_zero]; rfl
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0], h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1], maxBounds, by rw [hm, ← e14]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Rel`. -/
section

/-!
# ML-DSA signing on ARMv7: two runs

Constant time is proven piece by piece (`RelCT`) for two runs from entry
states that satisfy `signK`'s precondition and agree on its public data, each
satisfying the invariant `I` of the correctness proof, and related by `E`
(`RR`): each piece leaks the same, correctness gives each run's next
invariant, and the piece's own proof the next relation (`relInvE`). The runs
are in the same layout (`RR.lrel`) and agree on `ρ` (`RR.rho`), which the
leakage begins with.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (D : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  VG.Proof.MlDsa.Arm.Sign.Rel2 (VG.Proof.MlDsa.Arm.Sign.signK p D).pre (VG.Proof.MlDsa.Arm.Sign.signK p D).pub I x y ∧ E x y

section
variable {p : Params} {D : Nat}

theorem relInvE {I J E E' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.Arm.Sign.RR p D I E) c E') : RelCT isa (VG.Proof.MlDsa.Arm.Sign.RR p D I E) c (VG.Proof.MlDsa.Arm.Sign.RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', he⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, he⟩

theorem RR.mono {I I' E E' : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.Arm.Sign.RR p D I E x y)
    (hI : ∀ σ s, I σ s → I' σ s) (hE : E x y → E' x y) : VG.Proof.MlDsa.Arm.Sign.RR p D I' E' x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, e⟩ := h
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, hI _ _ i₁, hI _ _ i₂⟩, hE e⟩

theorem RR.lrel {I E : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.Arm.Sign.St p D σ s) {x y : State}
    (h : VG.Proof.MlDsa.Arm.Sign.RR p D I E x y) : VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y := by
  obtain ⟨⟨σ₁, σ₂, _, _, hpub, i₁, i₂⟩, _⟩ := h
  have S₁ := hI _ _ i₁
  have S₂ := hI _ _ i₂
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.sp, S₂.top.sp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ .r4 (by decide), r₂ .r4 (by decide)]; exact h1
  · rw [r₁ .r5 (by decide), r₂ .r5 (by decide)]; exact h2
  · rw [r₁ .r6 (by decide), r₂ .r6 (by decide)]; exact h3
  · rw [r₁ .r7 (by decide), r₂ .r7 (by decide)]; exact h5
  · rw [r₁ .r8 (by decide), r₂ .r8 (by decide)]; exact h4

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
    (hw : ∀ σ s, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (VG.Proof.MlDsa.Arm.Sign.RR p D I E) c Q₀)
    (hE : ∀ x y x' y', VG.Proof.MlDsa.Arm.Sign.RR p D I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RR p D I E) c (VG.Proof.MlDsa.Arm.Sign.RR p D J E') := by
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
  ∃ σ₁ σ₂, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ₁ ∧ (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ₂ ∧ (VG.Proof.MlDsa.Arm.Sign.signK p D).pub σ₁ σ₂ ∧ E σ₁ σ₂ ∧ I σ₁ x ∧ I σ₂ y

section
variable {p : Params} {D : Nat}

theorem lrel_of {σ₁ σ₂ x y : State} (hpub : (VG.Proof.MlDsa.Arm.Sign.signK p D).pub σ₁ σ₂) (S₁ : VG.Proof.MlDsa.Arm.Sign.St p D σ₁ x) (S₂ : VG.Proof.MlDsa.Arm.Sign.St p D σ₂ y) :
    VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.sp, S₂.top.sp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ .r4 (by decide), r₂ .r4 (by decide)]; exact h1
  · rw [r₁ .r5 (by decide), r₂ .r5 (by decide)]; exact h2
  · rw [r₁ .r6 (by decide), r₂ .r6 (by decide)]; exact h3
  · rw [r₁ .r7 (by decide), r₂ .r7 (by decide)]; exact h5
  · rw [r₁ .r8 (by decide), r₂ .r8 (by decide)]; exact h4

theorem RS.lrel {E I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.Arm.Sign.St p D σ s) {x y : State}
    (h : VG.Proof.MlDsa.Arm.Sign.RS p D E I x y) : VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  exact VG.Proof.MlDsa.Arm.Sign.lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem RS.mono {E I E' I' : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.Arm.Sign.RS p D E I x y)
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → E' σ₁ σ₂) (hI : ∀ σ s, I σ s → I' σ s) : VG.Proof.MlDsa.Arm.Sign.RS p D E' I' x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, e, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, hE _ _ e, hI _ _ i₁, hI _ _ i₂⟩

/-- A piece that leaks the same from two runs in the layout that satisfy `T`, and takes each run from
`I` to `J`. -/
theorem liftL {E I J : State → State → Prop} {T : State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.Arm.Sign.St p D σ s ∧ T s) (hw : ∀ σ s, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ T x ∧ T y) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E I) c (VG.Proof.MlDsa.Arm.Sign.RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ ⟨VG.Proof.MlDsa.Arm.Sign.lrel_of hpub (hI _ _ i₁).1 (hI _ _ i₂).1, (hI _ _ i₁).2, (hI _ _ i₂).2⟩ e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- `liftL`, with a leakage proof from any relation the runs satisfy. -/
theorem liftR {E I J : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E I) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E I) c (VG.Proof.MlDsa.Arm.Sign.RS p D E J) := by
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
    (h₁ : RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, VG.Proof.MlDsa.Arm.Sign.Lay D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x → I x → WP isa c₁ x fun x' => (∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (VG.Proof.MlDsa.Arm.Sign.postDep h₁ (F := fun x x' => (∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.lx h.2.1, w₁ y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hx hy, jx, jy⟩) h₂

theorem trL_mono {c : Prog isa} {I I' : State → Prop}
    (h : RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I x ∧ I y) c fun _ _ => True) (hI : ∀ s, I' s → I s) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I' x ∧ I' y) c fun _ _ => True :=
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
  obtain ⟨X₁, e₁⟩ := VG.Proof.MlDsa.Arm.Sign.signLeakT_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := VG.Proof.MlDsa.Arm.Sign.signLeakT_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine VG.Proof.MlDsa.Sign.leakBytes_inj (List.append_inj h ?_).1
  rw [leakBytes_length, leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {D : Nat} {σ₁ σ₂ : State} (h : (VG.Proof.MlDsa.Arm.Sign.signK p D).pub σ₁ σ₂) :
    VG.Proof.MlDsa.Arm.Sign.rhoOf p σ₁ = VG.Proof.MlDsa.Arm.Sign.rhoOf p σ₂ :=
  VG.Proof.MlDsa.Arm.Sign.leak_rho (VG.Proof.MlKem.bytesAt_length _ _ _) (VG.Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT`. -/
section

/-!
# ML-DSA signing on ARMv7: decoding leaks only the pointers

Each call while decoding leaks only its pointers, given that its input
polynomial is reduced (`dec_tr`); so two runs agree on what decoding leaks
(`decode_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A piece that leaks only its pointers, from runs in the layout. -/
theorem liftT {p : Params} {D : Nat} {E I J : State → State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.Arm.Sign.St p D σ s) (hw : ∀ σ s, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p)) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E I) c (VG.Proof.MlDsa.Arm.Sign.RS p D E J) :=
  VG.Proof.MlDsa.Arm.Sign.liftL (T := fun _ => True) (fun σ s h => ⟨hI σ s h, trivial⟩) hw (RelCT.mono ht (fun _ _ h => h.1) fun _ _ h => h)

theorem dec_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y)) (hc : VG.Proof.MlDsa.Arm.Sign.decChk p a b c src len j = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p)) (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hc
  refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqL (p := p) (I := fun _ => True) (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (pS j)))
    (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.bupAt_tr hP hp hl h1) (fun _ _ h => h.1) fun _ _ h => h)
    (fun s L _ => WP.mono (VG.Proof.MlDsa.Arm.Sign.bupAt_ok hP L hp hl h1) fun s' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩)
    (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt h2)) (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem decode_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.dChk p = true) {E : State → State → Prop} :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E (VG.Proof.MlDsa.Arm.Sign.IM p D)) (decode P p) (VG.Proof.MlDsa.Arm.Sign.RS p D E (VG.Proof.MlDsa.Arm.Sign.IK p D)) := by
  have hs := VG.Proof.MlDsa.Arm.Sign.dChk_spec hc
  unfold decode
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ 0 0 s) ?_ (RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k 0 s)
    ?_ (RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k p.k s) ?_ ?_))
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ID p D σ r 0 0 s) p.ℓ 0 fun r _ hr =>
      VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.decS1_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.Arm.Sign.dec_tr hP hs.2.2.2.2.2.2.1 (VG.Proof.MlDsa.Arm.Sign.sLen_eq p) (hs.1 r (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ i 0 s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.decS2_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.Arm.Sign.dec_tr hP hs.2.2.2.2.2.2.1 (VG.Proof.MlDsa.Arm.Sign.sLen_eq p) (hs.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ID p D σ p.ℓ p.k i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.decT0_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.Arm.Sign.dec_tr hP (by decide) (by decide) (hs.2.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, h.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · exact VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.rpp_ok hP hc h)
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.shake_tr (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hP.hD hs.2.2.2.1) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT`. -/
section

/-!
# ML-DSA signing on ARMv7: the commitment leaks only the pointers

Each piece of the commitment leaks only its pointers, given that its inputs
are reduced (and the coefficients of `HighBits(w[i])` bounded): `maskR_trL`,
`rowW_trL`, `w1R_trL`; so two runs agree on what the commitment leaks
(`commit_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- A piece that keeps `I`, from runs in the layout that satisfy it. -/
theorem stepSelf {c : Prog isa} {I : State → Prop}
    (h : RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I x ∧ I y) c fun _ _ => True)
    (w : ∀ x, VG.Proof.MlDsa.Arm.Sign.Lay D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x → I x → WP isa c x fun x' => (∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x x' W) ∧ I x') :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I x ∧ I y) c
      fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ I x ∧ I y :=
  VG.Proof.MlDsa.Arm.Sign.postDep h (F := fun x x' => (∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x x' W) ∧ I x')
    (fun x y h => ⟨w x h.1.lx h.2.1, w y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hx hy, jx, jy⟩

theorem lrel_r7 {x y : State} (h : VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y) : ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact h.regs (.r7, VG.Proof.MlDsa.Arm.Sign.scrLen p) (by simp [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW])

end

/-! ## `y` and `ŷ` -/

theorem setKappa_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D rbs wbs s) {r : Nat}
    (hr : r < 256) (h1 : VG.Proof.MlDsa.Arm.Sign.inB (rbs ++ wbs) (sc oKAP) 4 = true) (h2 : VG.Proof.MlDsa.Arm.Sign.inB wbs (sc (oMS + 64)) 2 = true) :
    WP isa (.block (setKappa r)) s fun s' => ∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D s s' W := by
  have e65 : VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)) + 1 := (VG.Proof.MlDsa.Arm.Sign.pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.iW h2
  have ak : State.addr (s.gpr .r7 + BitVec.ofNat 32 oKAP) = VG.Proof.MlDsa.Arm.Sign.pa s (sc oKAP) := L.w (p := sc oKAP) h1 (by decide)
  have a64 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 64)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)) :=
    L.pa32W (p := sc (oMS + 64)) h2 (by decide)
  have a65 : State.addr (s.gpr .r7 + BitVec.ofNat 32 (oMS + 65)) = VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65)) :=
    L.pa32W (p := sc (oMS + 65)) (VG.Proof.MlDsa.Arm.Sign.inB_sub (l := 1) h2 (by decide)) (by decide)
  have c0 : (⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 1 := by
    have := VG.Proof.MlDsa.Arm.Sign.contains_sub (Region.contains_self (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 2) (off := 0) (l := 1) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.Arm.Sign.contains_sub (Region.contains_self _ 2) (off := 1) (l := 1) (by decide) (by decide)
  have i0 : InRegions s.wr (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64))) 1 := by
    have := VG.Proof.MlDsa.Arm.Sign.inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.Proof.MlDsa.Arm.Sign.inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.setKappa_ok r hr s (by rw [ak]; exact L.iR h1) (by rw [a64]; exact i0) (by rw [a65]; exact i1))
    fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  rw [ak, a64, a65] at hm
  have hf : Frame [⟨VG.Proof.MlDsa.Arm.Sign.pa s (sc (oMS + 64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  have hg' : ∀ r, r ≠ .r0 → s'.gpr r = s.gpr r := fun r h => hg r (by simpa using h)
  exact ⟨_, (VG.Proof.MlDsa.Arm.Sign.postB_store (D := D) hg' hrd hwr hsp hf).1⟩

theorem maskR_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {r : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.mChk p r = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p)) (maskR P p r) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, k1⟩, w1⟩, cm⟩, _⟩, cc⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩, hr⟩, hγ⟩ := hc
  have hcc := VG.Proof.MlDsa.Arm.Sign.copyChk_spec cc
  unfold maskR
  refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h.1) (fun x L _ => WP.mono (VG.Proof.MlDsa.Arm.Sign.setKappa_post L hr k1 w1) fun _ h => ⟨h, trivial⟩)
    (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (yP p r)))
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.maskAt_tr hP hγ cm) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x L _ => WP.mono (VG.Proof.MlDsa.Arm.Sign.maskAt_ok hP L hγ cm) fun x' ⟨hP', _, hq⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩)
      (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (yhP p r)))
        (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.copy_tr hcc.2.2.2.2.1 hcc.2.2.2.2.2
          fun x y h => ⟨VG.Proof.MlDsa.Arm.Sign.lrel_r7 h.1 _ (List.mem_singleton_self _), VG.Proof.MlDsa.Arm.Sign.lrel_r7 h.1 _ (List.mem_singleton_self _)⟩)
          (fun _ _ h => h) fun _ _ h => h)
        (fun x L hy => WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
          ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact reduced_congr₂ (VG.Proof.MlDsa.Sign.bytes_of_bytesAt hb) hy⟩)
        (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt ci))))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

/-! ## `w` -/

/-- `w[i]` from runs in iteration `t` with `y`, `ŷ` and the first `i` polynomials of `w`. -/
theorem rowW_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {t i : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.wChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i y) (rowW P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, _⟩, hl⟩ := hc
  have hA : ∀ {σ s : State} (I : VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) j, j < p.ℓ → Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (aP p i j)) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [VG.Proof.MlDsa.Arm.Sign.aP_ij]; exact this.1
  let J : State → Prop := fun s => (∃ σ, VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (wP p i))
  unfold rowW
  refine VG.Proof.MlDsa.Arm.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.Arm.Sign.seqL (J := J) ?_ ?_ ?_)
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_tr hP (cm 0 hl)) (fun x y ⟨R, ⟨σ₁, I₁⟩, ⟨σ₂, I₂⟩⟩ =>
      ⟨R, ⟨hA I₁ 0 hl, (I₁.yh 0 hl).1⟩, ⟨hA I₂ 0 hl, (I₂.yh 0 hl).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L (cm 0 hl) (hA I 0 hl) (I.yh 0 hl).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun _ x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ J x ∧ J y) (p.ℓ - 1) 1
      fun j hj1 hj => VG.Proof.MlDsa.Arm.Sign.stepSelf ?_ ?_) (fun _ _ h => h) fun _ _ _ => trivial
    · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.mulAddAt_tr hP (cm j (by omega))) (fun x y ⟨R, ⟨⟨σ₁, I₁⟩, r₁⟩, ⟨⟨σ₂, I₂⟩, r₂⟩⟩ =>
        ⟨R, ⟨r₁, hA I₁ j (by omega), (I₁.yh j (by omega)).1⟩, ⟨r₂, hA I₂ j (by omega), (I₂.yh j (by omega)).1⟩⟩)
        fun _ _ h => h
    · rintro x L ⟨⟨σ, I⟩, r⟩
      refine WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAddAt_ok hP L (cm j (by omega)) r (hA I j (by omega)) (I.yh j (by omega)).1)
        fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩
  · rintro x L ⟨I, r⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.seqR_ok (I := fun _ s => ∃ W, VG.Proof.MlDsa.Arm.Sign.PostB D x s W ∧ J s) (p.ℓ - 1) 1
      (fun j hj1 hj s ⟨W, hW, ⟨σ, I'⟩, r'⟩ => WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAddAt_ok hP I'.l.st.lay (cm j (by omega)) r'
        (hA I' j (by omega)) (I'.yh j (by omega)).1) fun x' ⟨hP', _, hq⟩ =>
          ⟨_, hW.trans hP' (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h),
            ⟨σ, I'.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩) x ⟨[], PostB.refl D x [], I, r⟩)
      fun x' ⟨W, hW, j⟩ => ⟨⟨W, hW⟩, j⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun _ _ h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h

/-! ## `w₁` -/

theorem w1R_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {t i : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.hChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.Arm.Sign.ICh p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.Arm.Sign.ICh p D σ t i y) (w1R P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => ∀ j < 256, (coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t1P) j).toNat ≤ w1Max p) ?_ ?_
    (VG.Proof.MlDsa.Arm.Sign.sbpAt_tr hP hb rfl c2)
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.highBitsAt_tr hP hγ c1) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ => ⟨R, (I₁.c.w i hi).1, (I₂.c.w i hi).1⟩)
      fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (VG.Proof.MlDsa.Arm.Sign.highBitsAt_ok hP L hγ c1 (I.c.w i hi).1) fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, fun j hj => ?_⟩
    rw [hP'.pa (by decide), VG.Proof.MlDsa.Arm.Sign.natPolyIs_coeff hq hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _

/-! ## The commitment -/

theorem ctShake_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.Arm.Sign.ICh p D σ t p.k s) :
    WP isa (shakeAt [((.r5, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p)) s (VG.Proof.MlDsa.Arm.Sign.IC p D σ t) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.cChk, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hs⟩, hk⟩ := hc
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.shake_ok (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hP.hD hs h.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ => ⟨h.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [VG.Proof.MlDsa.Arm.Sign.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, h.w1, h.c.l.st.mu]
  simp only [VG.Proof.MlDsa.Arm.Sign.CTv, ctF, w1Encode, List.flatMap_map]

theorem commit_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) (commit P p) (VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.IC p D σ t s) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.Arm.Sign.cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commit
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ICw p D σ t 0 s) ?_ (RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ICh p D σ t p.k s) ?_ ?_))
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ICm p D σ t r s) p.ℓ 0 fun r _ hr =>
      VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.l.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.maskR_ok hP (hm r (by omega)) h) (VG.Proof.MlDsa.Arm.Sign.maskR_trL hP (hm r (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h.l, h.y, h.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.Arm.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.Arm.Sign.ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.rowW_ok hP (hw i (by omega)) (by omega) h) (VG.Proof.MlDsa.Arm.Sign.rowW_trL hP (hw i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [VG.Proof.MlDsa.Arm.Sign.w1Enc]; rfl⟩
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.ICh p D σ t i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.Arm.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.Arm.Sign.ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.w1R_ok hP (hh i (by omega)) (by omega) h) (VG.Proof.MlDsa.Arm.Sign.w1R_trL hP (hh i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · exact VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.ctShake_ok hP hc h)
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.shake_tr (VG.Proof.MlDsa.Arm.Sign.sgB_bases p) hP.hD hs) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT`. -/
section

/-!
# ML-DSA signing on ARMv7: the checks leak only the pointers and whether they passed

Each check leaks only its pointers, given that its inputs are reduced
(`zR_trL`, `r0R_trL`, `hR_trL`); the branch on their result leaks whether the
iteration passed, which two runs agree on when they agree on what the
iteration leaks (`checks_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params}
include hP

theorem normAt_post {s : State} (L : VG.Proof.MlDsa.Arm.Sign.Lay D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : VG.Proof.MlDsa.Arm.Sign.normChk (VG.Proof.MlDsa.Arm.Sign.sgB p) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s f)) :
    WP isa (normAt P f B) s fun s' => VG.Proof.MlDsa.Arm.Sign.PPostB D s s' [] := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Sign.normCall_ok hP L hB hc hr) fun s1 ⟨hP1, _, _⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.and11_ok s1) fun s2 ⟨_, k2⟩ => ?_
  exact PostB.trans hP1 (VG.Proof.MlDsa.Arm.Sign.postB11 (D := D) k2 ([] : List Region)).1 (fun r h => h) fun _ h => absurd h List.not_mem_nil

theorem normAt_trL {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.Arm.Sign.normChk (VG.Proof.MlDsa.Arm.Sign.sgB p) f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.Sign.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.Sign.pa y f)) (normAt P f B)
      fun _ _ => True :=
  VG.Proof.MlDsa.Arm.Sign.seqL (J := fun _ => True) (VG.Proof.MlDsa.Arm.Sign.normCall_tr hP (B := B) hc)
    (fun x L hr => WP.mono (VG.Proof.MlDsa.Arm.Sign.normCall_ok hP L hB hc hr) fun _ h => ⟨⟨_, h.1⟩, trivial⟩)
    (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)

/-! ## `z` -/

theorem zR_trL {t r : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.zChk p r = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.Arm.Sign.IZ p D σ t r x) ∧ ∃ σ, VG.Proof.MlDsa.Arm.Sign.IZ p D σ t r y) (zR P p r)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩, hr⟩ := hc
  unfold zR
  refine VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.Arm.Sign.IZb p D σ t r s) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t1P)) ?_ ?_
    (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.Arm.Sign.IZb p D σ t r s) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t1P)) ?_ ?_
      (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (yP p r))) ?_ ?_ (VG.Proof.MlDsa.Arm.Sign.normAt_trL hP hB cn)))
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_tr hP cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s1 r hr).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s1 r hr).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L cm I.1.b.c.1 (I.1.b.l.k.d.s1 r hr).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.addAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.y 0 (by omega)).1, r₁⟩, ⟨(I₂.y 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.addAt_ok hP L ca (I.y 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩

/-! ## `r₀` -/

theorem r0R_trL {t i : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.rChk p i = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.Arm.Sign.IR p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.Arm.Sign.IR p D σ t i y) (r0R P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  unfold r0R
  refine VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.Arm.Sign.IRb p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t1P)) ?_ ?_
    (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.Arm.Sign.IRb p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t1P)) ?_ ?_
      (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (wP p i))) ?_ ?_
        (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t2P)) ?_ ?_ (VG.Proof.MlDsa.Arm.Sign.normAt_trL hP hB cn))))
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_tr hP cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s2 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s2 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L cm I.1.b.c.1 (I.1.b.l.k.d.s2 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.subAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.w 0 (by omega)).1, r₁⟩, ⟨(I₂.w 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.subAt_ok hP L ca (I.w 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩
  · exact VG.Proof.MlDsa.Arm.Sign.lowBitsAt_tr hP hγ cl
  · intro x L r1
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.lowBitsAt_ok hP L hγ cl r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 2)]; exact hq.1⟩

/-! ## `ct₀` and `h` -/

theorem hR_trL {t i : Nat} (hc : VG.Proof.MlDsa.Arm.Sign.hChk2 p i = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.Arm.Sign.IH p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.Arm.Sign.IH p D σ t i y) (VG.Impl.MlDsa.Arm.Sign.hR P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.Arm.Sign.hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, _⟩, g6⟩, _⟩, _⟩,
    _⟩, _⟩, o1⟩, o2⟩, o3⟩, o4⟩, _⟩, _⟩, t3⟩, t4⟩, u5⟩, _⟩, _⟩, _⟩, hγ'⟩, hγ⟩, hi⟩, _⟩ := hc
  have hcc := VG.Proof.MlDsa.Arm.Sign.copyChk_spec cc
  have f6 : VG.Proof.MlDsa.Arm.Sign.keepB (VG.Proof.MlDsa.Arm.Sign.sgB p) [(t4P, 1024)] (wP p i) 1024 = true := by
    simp only [VG.Proof.MlDsa.Arm.Sign.hfam, Bool.and_eq_true] at g6
    exact VG.Proof.MlDsa.Arm.Sign.famChk_one (b := VG.Proof.MlDsa.Arm.Sign.wBase p) g6.1.1.2 (show i < i + 1 by omega)
  let J : State → Prop := fun s => (∃ σ, VG.Proof.MlDsa.Arm.Sign.IHb p D σ t i i s) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t3P)
  unfold VG.Impl.MlDsa.Arm.Sign.hR
  refine VG.Proof.MlDsa.Arm.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.Arm.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.Arm.Sign.seqL (J := J) ?_ ?_
    (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => J s ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t4P)) ?_ ?_
      (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t4P) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (wP p i))) ?_ ?_
        (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s t4P) ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (wP p i))) ?_ ?_
          (VG.Proof.MlDsa.Arm.Sign.seqL (J := fun _ => True) ?_ ?_ ?_))))))
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_tr hP cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.t0 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.t0 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.mulAt_ok hP L cm I.1.b.c.1 (I.1.b.l.k.d.t0 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' g1 o1⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g2 o2⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.normAt_trL hP hγ' cn) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.normAt_post hP L hγ' cn r1) fun x' hP' => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g3 o3⟩, L.keepRed hP' t3 r1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.copy_tr hcc.2.2.2.2.1 hcc.2.2.2.2.2
      fun x y h => ⟨VG.Proof.MlDsa.Arm.Sign.lrel_r7 h.1 _ (List.mem_singleton_self _), VG.Proof.MlDsa.Arm.Sign.lrel_r7 h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r3⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB L cc) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, ⟨⟨σ, I.step hP' g4 o4⟩, L.keepRed hP' t4 r3⟩,
      by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 4)]; exact reduced_congr₂ (VG.Proof.MlDsa.Sign.bytes_of_bytesAt hb) (I.w' 0 (by omega)).1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.addAt_tr hP ca) (fun x y ⟨R, ⟨⟨⟨_, I₁⟩, r₁⟩, _⟩, ⟨⟨⟨_, I₂⟩, r₂⟩, _⟩⟩ =>
      ⟨R, ⟨(I₁.w' 0 (by omega)).1, r₁⟩, ⟨(I₂.w' 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨⟨σ, I⟩, r3⟩, r4⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.addAt_ok hP L ca (I.w' 0 (by omega)).1 r3) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, L.keepRed hP' u5 r4, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases _)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.subAt_tr hP cs) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.subAt_ok hP L cs r4 rw) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.Arm.Sign.pS_bases 4)]; exact hq.1, L.keepRed hP' f6 rw⟩
  · exact RelCT.mono (VG.Proof.MlDsa.Arm.Sign.hintCall_tr hP hγ ch) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩)
      fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (VG.Proof.MlDsa.Arm.Sign.hintCall_ok hP L hγ ch r4 rw) fun x' ⟨hP', _, _⟩ => ⟨⟨_, hP'⟩, trivial⟩
  · exact VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h.1

/-! ## The checks -/

omit hP in
theorem ifOk_r7 {E I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.Arm.Sign.St p D σ s) {C : State → Prop} {x y : State}
    (h : ∃ x₀ y₀, VG.Proof.MlDsa.Arm.Sign.RS p D E I x₀ y₀ ∧ (VG.Proof.MlDsa.Arm.Sign.PPostB D x₀ x [] ∧ VG.Proof.MlDsa.Arm.Sign.CS x₀ x ∧ x.mem = x₀.mem) ∧
      (VG.Proof.MlDsa.Arm.Sign.PPostB D y₀ y [] ∧ VG.Proof.MlDsa.Arm.Sign.CS y₀ y ∧ y.mem = y₀.mem) ∧ C x₀) :
    ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := by
  obtain ⟨x₀, y₀, R, ⟨hx, _⟩, ⟨hy, _⟩, _⟩ := h
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [hx.bs _ (by decide), hy.bs _ (by decide)]
  exact VG.Proof.MlDsa.Arm.Sign.lrel_r7 (R.lrel hI) _ (List.mem_singleton_self _)

theorem checks_tr (hc : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) {E : State → State → Prop} {t : Nat}
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ₁ (p.ℓ * t))).isSome →
      (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ₂ (p.ℓ * t))).isSome → (VG.Proof.MlDsa.Arm.Sign.PassV p σ₁ (p.ℓ * t) ↔ VG.Proof.MlDsa.Arm.Sign.PassV p σ₂ (p.ℓ * t))) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.KA p D σ t s) (checks P p)
      (VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.Arm.Sign.EF p D σ t s) := by
  refine VG.Proof.MlDsa.Arm.Sign.ksChk_spec hc fun c1 _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.KN p D σ t s)
    (VG.Proof.MlDsa.Arm.Sign.liftL (T := fun s => Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s cP)) (fun σ s h => ⟨h.c.l.st, h.cc.1⟩)
      (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.cntt_ok hP hc h) (VG.Proof.MlDsa.Arm.Sign.ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt c1)) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.IZ p D σ t 0 s)
    (VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.b.l.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.kInit_ok hc h) (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h)) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.IR p D σ t 0 s) (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun r => VG.Proof.MlDsa.Arm.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.Arm.Sign.IZ p D σ t r s) p.ℓ 0 fun r _ hr => VG.Proof.MlDsa.Arm.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.Arm.Sign.IZ p D σ t r s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.zR_ok hP (hz r (by omega)) h) (VG.Proof.MlDsa.Arm.Sign.zR_trL hP (hz r (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ir) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.IH p D σ t 0 s) (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.Arm.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.Arm.Sign.IR p D σ t i s) p.k 0 fun i _ hi => VG.Proof.MlDsa.Arm.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.Arm.Sign.IR p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.r0R_ok hP (hr i (by omega)) h) (VG.Proof.MlDsa.Arm.Sign.r0R_trL hP (hr i (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ih) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.IH p D σ t p.k s) (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr (R := fun i => VG.Proof.MlDsa.Arm.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.Arm.Sign.IH p D σ t i s) p.k 0 fun i _ hi => VG.Proof.MlDsa.Arm.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.Arm.Sign.IH p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.hR_ok hP (hh i (by omega)) h) (VG.Proof.MlDsa.Arm.Sign.hR_trL hP (hh i (by omega))))
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RS p D E fun σ s => VG.Proof.MlDsa.Arm.Sign.KO p D σ t s)
    (VG.Proof.MlDsa.Arm.Sign.liftT (fun _ _ h => h.1.b.l.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.onesOk_ok hc h) (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h)) ?_
  refine VG.Proof.MlDsa.Arm.Sign.liftR (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.kBranch_ok hc h) (VG.Proof.MlDsa.Arm.Sign.ifOkElse_tr (D := D) (fun x y h => ?_)
    (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.ifOk_r7 (I := fun σ s => VG.Proof.MlDsa.Arm.Sign.KO p D σ t s) (fun _ _ h => h.b.l.st) h)
    (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.ifOk_r7 (I := fun σ s => VG.Proof.MlDsa.Arm.Sign.KO p D σ t s) (fun _ _ h => h.b.l.st) h))
  obtain ⟨σ₁, σ₂, _, _, _, he, k₁, k₂⟩ := h
  rw [k₁.r11, k₂.r11, VG.Proof.MlDsa.Arm.Sign.bit_congr (hE σ₁ σ₂ he k₁.b.some k₂.b.some)]

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseLCT`. -/
section

/-!
# ML-DSA signing on ARMv7: the loop leaks what `signLeakT` says

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration, and leak the
same (`iter_tr`, `signLoop_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## What the iterations leak -/

section
variable (p : Params)

/-- What the `n` iterations from counter `κ` leak, for the function entered in `σ`. -/
abbrev leakL (σ : State) (n κ : Nat) : List Nat :=
  signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ)) (VG.Proof.MlDsa.Arm.Sign.muOf σ) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ) n κ

/-- Two runs agree on what the iterations from `t` leak. -/
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := VG.Proof.MlDsa.Arm.Sign.leakL p σ₁ (1000 - t) (p.ℓ * t) = VG.Proof.MlDsa.Arm.Sign.leakL p σ₂ (1000 - t) (p.ℓ * t)

end

theorem map_toNat_inj : ∀ {l₁ l₂ : List Bool}, l₁.map Bool.toNat = l₂.map Bool.toNat → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [VG.Proof.MlDsa.Arm.Sign.map_toNat_inj h.2]
    cases a <;> cases b <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem hints_inj : ∀ {a b : List (Vector Bool n)}, a.length = b.length →
    (a.flatMap fun hi => hi.toList.map Bool.toNat) = (b.flatMap fun hi => hi.toList.map Bool.toNat) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp (VG.Proof.MlDsa.Arm.Sign.map_toNat_inj h1), VG.Proof.MlDsa.Arm.Sign.hints_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}

theorem leq_step (h : VG.Proof.MlDsa.Arm.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ₁)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ₁)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ₁))
      ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ₁)) (VG.Proof.MlDsa.Arm.Sign.muOf σ₁) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ₂)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Arm.Sign.S1v p σ₂)) ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.S2v p σ₂))
      ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.T0v p σ₂)) (VG.Proof.MlDsa.Arm.Sign.muOf σ₂) (VG.Proof.MlDsa.Arm.Sign.rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : VG.Proof.MlDsa.Arm.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814) : VG.Proof.MlDsa.Arm.Sign.CTv p σ₁ (p.ℓ * t) = VG.Proof.MlDsa.Arm.Sign.CTv p σ₂ (p.ℓ * t) := by
  have := (leakT_step (VG.Proof.MlDsa.Arm.Sign.leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : VG.Proof.MlDsa.Arm.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, VG.Proof.MlDsa.Arm.Sign.iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : VG.Proof.MlDsa.Arm.Sign.LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakT_step (VG.Proof.MlDsa.Arm.Sign.leq_step h ht)).2.1 hr).2
  unfold VG.Proof.MlDsa.Arm.Sign.LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ κ)).isSome) :
    outTag (VG.Proof.MlDsa.Arm.Sign.iterF p σ maxBounds κ) = if VG.Proof.MlDsa.Arm.Sign.PassV p σ κ then
      1 :: ((List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [VG.Proof.MlDsa.Arm.Sign.iterF_eq hp, VG.Proof.MlDsa.Arm.Sign.cV_eq hs, Option.map_some]
  by_cases hv : VG.Proof.MlDsa.Arm.Sign.PassV p σ κ
  · rw [VG.Proof.MlDsa.Sign.ifp hv, VG.Proof.MlDsa.Sign.ifp hv]; rfl
  · rw [VG.Proof.MlDsa.Sign.ifn hv, VG.Proof.MlDsa.Sign.ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : VG.Proof.MlDsa.Arm.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ₂ (p.ℓ * t))).isSome) :
    VG.Proof.MlDsa.Arm.Sign.PassV p σ₁ (p.ℓ * t) ↔ VG.Proof.MlDsa.Arm.Sign.PassV p σ₂ (p.ℓ * t) := by
  have e := (leakT_step (VG.Proof.MlDsa.Arm.Sign.leq_step h ht)).2.2
  rw [VG.Proof.MlDsa.Arm.Sign.outTag_eq hp hs₁, VG.Proof.MlDsa.Arm.Sign.outTag_eq hp hs₂] at e
  by_cases h1 : VG.Proof.MlDsa.Arm.Sign.PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : VG.Proof.MlDsa.Arm.Sign.PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [VG.Proof.MlDsa.Sign.ifp h1, VG.Proof.MlDsa.Sign.ifn h2] at e; cases e
  · rw [VG.Proof.MlDsa.Sign.ifn h1, VG.Proof.MlDsa.Sign.ifp h2] at e; cases e
  · exact iff_of_false h1 h2

theorem leq_hints (hp : ParamsOk p) (h : VG.Proof.MlDsa.Arm.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (VG.Spec.MlDsa.sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Arm.Sign.CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : VG.Proof.MlDsa.Arm.Sign.PassV p σ₁ (p.ℓ * t)) (h2 : VG.Proof.MlDsa.Arm.Sign.PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (VG.Proof.MlDsa.Arm.Sign.Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakT_step (VG.Proof.MlDsa.Arm.Sign.leq_step h ht)).2.2
  rw [VG.Proof.MlDsa.Arm.Sign.outTag_eq hp hs₁, VG.Proof.MlDsa.Arm.Sign.outTag_eq hp hs₂, VG.Proof.MlDsa.Sign.ifp h1, VG.Proof.MlDsa.Sign.ifp h2] at e
  exact VG.Proof.MlDsa.Arm.Sign.hints_inj (by simp) (List.cons.inj e).2

end

/-! ## Pieces from runs related through their entry states -/

section
variable {p : Params} {D : Nat}

/-- A piece that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS p D E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ₁ → (VG.Proof.MlDsa.Arm.Sign.signK p D).pre σ₂ → (VG.Proof.MlDsa.Arm.Sign.signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D E I x y ∧ G x y) c Q := by
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

theorem z_of_eval {s : State} {b : Bool} (h : isa.eval .ne s = some b) : s.z = !b := by
  have e : some (!s.z) = some b := h
  cases hz : s.z <;> cases b <;> simp_all

theorem LP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.LP p D σ t s) (hz : s.z = false) :
    VG.Proof.MlDsa.Arm.Sign.IL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · rw [hz] at h; cases h

theorem LP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.Sign.LP p D σ t s) (hz : s.z = true) :
    VG.Proof.MlDsa.Arm.Sign.XS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · rw [hz] at h; cases h
  · exact h

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on `c̃` and `h`. -/
abbrev OX (p : Params) (D : Nat) (x y : State) : Prop :=
  VG.Proof.MlDsa.Arm.Sign.RS p D (fun _ _ => True) (VG.Proof.MlDsa.Arm.Sign.XS p D) x y ∧ x.gpr .r11 = y.gpr .r11 ∧
    (x.gpr .r11 = 1 → bytesAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x (sc oCT)) (cLen p) = bytesAt y.mem (VG.Proof.MlDsa.Arm.Sign.pa y (sc oCT)) (cLen p) ∧
      ∃ f, VG.Proof.MlDsa.Arm.Sign.HFam x 5 p.k f ∧ VG.Proof.MlDsa.Arm.Sign.HFam y 5 p.k f)

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
abbrev IX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.z = y.z ∧ (x.z = false → VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p (t + 1)) (fun σ s => VG.Proof.MlDsa.Arm.Sign.IL p D σ (t + 1) s) x y) ∧
    (x.z = true → VG.Proof.MlDsa.Arm.Sign.OX p D x y)

section
variable {p : Params} {D : Nat}

theorem endPF_tr (hp : ParamsOk p) (hc : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {t : Nat} :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.Arm.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.Arm.Sign.EF p D σ t s) x y ∧ True)
      (.block VG.Proof.MlDsa.Arm.Sign.decCnt) (VG.Proof.MlDsa.Arm.Sign.IX p D t) := by
  refine VG.Proof.MlDsa.Arm.Sign.liftQ (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.LP p D σ t s) (fun σ s _ h => WP.conj (VG.Proof.MlDsa.Arm.Sign.dec_end hp hc (h.elim .inl (.inr ∘ .inl)))
      (VG.Proof.MlDsa.Arm.Sign.decF hc (h.elim (·.k) (·.k))))
    (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.block_tr (rs := [.r7]) rfl (P := fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y) fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h)
      (fun x y h => h.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.z = true := by rw [z₁, e₁.cnt]; rfl
    have zy : y'.z = true := by rw [z₂, e₂.cnt]; rfl
    refine ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r11, e₂.r11], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact VG.Proof.MlDsa.Arm.Sign.leq_ct he e₁.t_lt,
      VG.Proof.MlDsa.Arm.Sign.Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (VG.Proof.MlDsa.Arm.Sign.leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((VG.Proof.MlDsa.Arm.Sign.leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((VG.Proof.MlDsa.Arm.Sign.leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.z = y'.z := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, VG.Proof.MlDsa.Arm.Sign.leq_succ he f₁.t_lt ⟨_, VG.Proof.MlDsa.Arm.Sign.iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩,
      by rw [r₁, r₂, f₁.r11, f₂.r11], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.r11)) (by decide)⟩⟩

theorem endB_tr (hp : ParamsOk p) (hc : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {t : Nat} :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.Arm.Sign.EB p D σ t s) x y ∧ True)
      (.block VG.Proof.MlDsa.Arm.Sign.decCnt) (VG.Proof.MlDsa.Arm.Sign.IX p D t) := by
  refine VG.Proof.MlDsa.Arm.Sign.liftQ (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.LP p D σ t s) (fun σ s _ h => WP.conj (VG.Proof.MlDsa.Arm.Sign.dec_end hp hc (.inr (.inr h))) (VG.Proof.MlDsa.Arm.Sign.decF hc h.k))
    (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.block_tr (rs := [.r7]) rfl (P := fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y) fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h)
      (fun x y h => h.1.lrel fun σ s h => h.k.d.im.st) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _
  have zx : x'.z = true := by rw [z₁, e₁.cnt]; rfl
  have zy : y'.z = true := by rw [z₂, e₂.cnt]; rfl
  exact ⟨by rw [zx, zy], fun h => absurd (h.symm.trans zx) (by decide), fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.r11, e₂.r11],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.r11)) (by decide)⟩⟩

theorem ax_one {s : State} (hz : s.z = (s.gpr .r0 == 0))
    (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) (hb : isa.eval .ne s = some true) : s.gpr .r0 = 1 := by
  have e := VG.Proof.MlDsa.Arm.Sign.z_of_eval hb
  rcases hr with h | h
  · rw [hz, h] at e; cases e
  · exact h

theorem ax_zero {s : State} (hz : s.z = (s.gpr .r0 == 0)) (hb : isa.eval .ne s = some false) : s.gpr .r0 = 0 := by
  have e := VG.Proof.MlDsa.Arm.Sign.z_of_eval hb
  rw [hz] at e
  simpa using e

theorem iter_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.Arm.Sign.cChk p = true) (hc2 : VG.Proof.MlDsa.Arm.Sign.bChk p = true)
    (hc3 : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) {t : Nat} (ht : t < 814) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) fun σ s => VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) (iter P p) (VG.Proof.MlDsa.Arm.Sign.IX p D t) := by
  have hc2' := hc2
  simp only [VG.Proof.MlDsa.Arm.Sign.bChk, Bool.and_eq_true, decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1, -⟩, -⟩, hbp⟩ := hc2'
  unfold iter
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.commit_tr hP hc1) ?_
  refine RelCT.seq (R := fun (x y : State) => VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.Arm.Sign.IB p D σ t s) x y ∧
      x.gpr .r0 = y.gpr .r0)
    (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.liftQ (G := fun _ _ => True) (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.IB p D σ t s) (F := fun _ _ => True)
      (fun _ _ _ h => WP.mono (VG.Proof.MlDsa.Arm.Sign.ball_ok hP hc2 h) fun _ h => ⟨h, trivial⟩)
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.ballCall_tr hP hbp c1) (fun x y ⟨h, _⟩ => ⟨h.lrel (fun _ _ h => h.c.l.st), by
        obtain ⟨σ₁, σ₂, _, _, _, he, i₁, i₂⟩ := h
        rw [i₁.ct, i₂.ct]; exact VG.Proof.MlDsa.Arm.Sign.leq_ct he ht⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
      (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun (x y : State) => VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t)
      (fun σ s => VG.Proof.MlDsa.Arm.Sign.IB p D σ t s ∧ s.z = (s.gpr .r0 == 0)) x y ∧
      x.gpr .r0 = y.gpr .r0)
    (VG.Proof.MlDsa.Arm.Sign.liftQ (F := fun s s' => s'.gpr .r0 = s.gpr .r0)
      (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.test_ok hc4 h)
      (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hg j₁ j₂ f₁ f₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, by rw [f₁, f₂, hg]⟩) ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  refine RelCT.seq (R := fun (x y : State) => (VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.Arm.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.Arm.Sign.EF p D σ t s) x y ∧ True) ∨
      (VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.Arm.Sign.EB p D σ t s) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (VG.Proof.MlDsa.Arm.Sign.relOr (VG.Proof.MlDsa.Arm.Sign.endPF_tr hp hc4) (VG.Proof.MlDsa.Arm.Sign.endB_tr hp hc4))
  · rintro x y ⟨⟨σ₁, σ₂, _, _, _, _, ⟨_, z₁⟩, ⟨_, z₂⟩⟩, hg⟩
    rw [hev, hev, z₁, z₂, hg]
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.checks_tr hP hc3 fun σ₁ σ₂ he s₁ s₂ => VG.Proof.MlDsa.Arm.Sign.leq_pass hp he ht s₁ s₂)
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inl ⟨h, trivial⟩
    have h1 := VG.Proof.MlDsa.Arm.Sign.ax_one z₁ i₁.r01 hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁.ka h1, i₂.ka (hg.symm.trans h1)⟩
  · refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.liftT (I := fun σ s => VG.Proof.MlDsa.Arm.Sign.IB p D σ t s ∧ s.gpr .r0 = 0)
      (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.EB p D σ t s) (fun _ _ h => h.1.c.l.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.else_ok hc4 h.1 h.2)
      (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h))
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inr ⟨h, trivial⟩
    have h0 := VG.Proof.MlDsa.Arm.Sign.ax_zero z₁ hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, h0⟩, ⟨i₂, hg.symm.trans h0⟩⟩

/-! ## The loop -/

theorem signLoop_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.Arm.Sign.cChk p = true) (hc2 : VG.Proof.MlDsa.Arm.Sign.bChk p = true)
    (hc3 : VG.Proof.MlDsa.Arm.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.Arm.Sign.lChk p = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p 0) fun σ s => VG.Proof.MlDsa.Arm.Sign.IK p D σ s) (Impl.MlDsa.Arm.Sign.signLoop P p) (VG.Proof.MlDsa.Arm.Sign.OX p D) := by
  unfold Impl.MlDsa.Arm.Sign.signLoop
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.liftT (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.IL p D σ 0 s) (fun _ _ h => h.d.im.st) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Sign.loopInit_ok hc4 h)
    (VG.Proof.MlDsa.Arm.Sign.block_tr rfl fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 h)) ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.Arm.Sign.IL p D σ t s) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := VG.Proof.MlDsa.Arm.Sign.iter_tr hP hp hc1 hc2 hc3 hc4 ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [hev, hev, hz], fun h => ho (VG.Proof.MlDsa.Arm.Sign.z_of_eval h), fun h =>
    ⟨814 - (t + 1), by omega, t + 1, rfl, hc (VG.Proof.MlDsa.Arm.Sign.z_of_eval h)⟩⟩

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT`. -/
section

/-!
# ML-DSA signing on ARMv7: the signature leaks only the hint

Writing the signature leaks its pointers and the hint (`output_tr`), on which
two runs whose loops leaked the same agree (`OX`); so all but `Â` leaks what
`signLeakT` says (`rest_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem hint_coeffs {x y : State} {k : Nat} {f : Nat → Vector Bool n} (hx : VG.Proof.MlDsa.Arm.Sign.HFam x 5 k f) (hy : VG.Proof.MlDsa.Arm.Sign.HFam y 5 k f) :
    (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.Arm.Sign.pa x (Impl.MlDsa.Arm.Sign.hP 0)) i).toNat) =
      (List.range (256 * k)).map (fun i => (coeffAt y.mem (VG.Proof.MlDsa.Arm.Sign.pa y (Impl.MlDsa.Arm.Sign.hP 0)) i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ s : State, coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (Impl.MlDsa.Arm.Sign.hP 0)) i =
      coeffAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (pS (5 + i / 256))) (i % 256) := fun s => by
    rw [VG.Proof.MlDsa.Arm.Sign.pS_hint s (i / 256)]
    unfold coeffAt
    rw [BitVec.add_assoc (VG.Proof.MlDsa.Arm.Sign.pa s _) (BitVec.ofNat 64 (1024 * (i / 256))), ← BitVec.ofNat_add,
      show 1024 * (i / 256) + 4 * (i % 256) = 4 * i by omega]
  have hq : i / 256 < k := by omega
  have hj : i % 256 < n := Nat.mod_lt _ (by decide)
  have ex := (hx _ hq).2 0 (by decide) _ hj
  have ey := (hy _ hq).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [e x, e y, ex, ey]

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, VG.Proof.MlDsa.Arm.Sign.IK p D σ s ∧ bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.Arm.Sign.CTv p σ κ ∧ VG.Proof.MlDsa.Arm.Sign.Fam s (VG.Proof.MlDsa.Arm.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.Arm.Sign.Zv p σ κ) ∧
    VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k (VG.Proof.MlDsa.Arm.Sign.Hv p σ κ) ∧ VG.Proof.MlDsa.Arm.Sign.PassV p σ κ ∧ s.gpr .r11 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, VG.Proof.MlDsa.Arm.Sign.OS p D σ κ r s ∧ VG.Proof.MlDsa.Arm.Sign.PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, VG.Proof.MlDsa.Arm.Sign.HFam x 5 p.k f ∧ VG.Proof.MlDsa.Arm.Sign.HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Sign.IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (yP p r)) ∧ VG.Proof.MlDsa.Arm.Sign.InRange s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, VG.Proof.MlDsa.Arm.Sign.inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) (hc : VG.Proof.MlDsa.Arm.Sign.oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D E (VG.Proof.MlDsa.Arm.Sign.IOi p D) x y ∧ VG.Proof.MlDsa.Arm.Sign.HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.Arm.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  have hcc := VG.Proof.MlDsa.Arm.Sign.copyChk_spec cc
  unfold output
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D E (VG.Proof.MlDsa.Arm.Sign.IOr p D 0) x y ∧ VG.Proof.MlDsa.Arm.Sign.HJ p x y) (VG.Proof.MlDsa.Arm.Sign.liftQ
    (F := fun s s' => ∀ f, VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.Arm.Sign.HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (VG.Proof.MlDsa.Arm.Sign.outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.copy_tr hcc.2.2.2.2.1 hcc.2.2.2.2.2
        (P := fun x y => VG.Proof.MlDsa.Arm.Sign.LRel D (VG.Proof.MlDsa.Arm.Sign.sgR p) (VG.Proof.MlDsa.Arm.Sign.sgW p) x y)
        fun x y h => ⟨h.regs (.r8, p.sigLen) (by simp [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW]), VG.Proof.MlDsa.Arm.Sign.lrel_r7 h _ (List.mem_singleton_self _)⟩)
      (fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk.d.im.st) fun _ _ h => h)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.Arm.Sign.RS p D E (VG.Proof.MlDsa.Arm.Sign.IOr p D p.ℓ) x y ∧ VG.Proof.MlDsa.Arm.Sign.HJ p x y) (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.seqR_tr
    (R := fun r x y => VG.Proof.MlDsa.Arm.Sign.RS p D E (VG.Proof.MlDsa.Arm.Sign.IOr p D r) x y ∧ VG.Proof.MlDsa.Arm.Sign.HJ p x y) p.ℓ 0 fun r _ hr => VG.Proof.MlDsa.Arm.Sign.liftQ
      (F := fun s s' => ∀ f, VG.Proof.MlDsa.Arm.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.Arm.Sign.HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (VG.Proof.MlDsa.Arm.Sign.packZ_ok hP hc (by omega) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.bpAt_tr hP hbp hzl (cz r (by omega)).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega), i₂.zr (by omega)⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (VG.Proof.MlDsa.Arm.Sign.hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨VG.Proof.MlDsa.Arm.Sign.hones_ok o₁ a₁, VG.Proof.MlDsa.Arm.Sign.hones_ok o₂ a₂, VG.Proof.MlDsa.Arm.Sign.hint_coeffs hx hy⟩

theorem XS.io (hf : VG.Proof.MlDsa.Arm.Sign.fChk p = true) {σ x₀ x : State} (h : VG.Proof.MlDsa.Arm.Sign.XS p D σ x₀) (h15 : x₀.gpr .r11 = 1)
    (hP : VG.Proof.MlDsa.Arm.Sign.PPostB D x₀ x []) (hcs : VG.Proof.MlDsa.Arm.Sign.CS x₀ x) : VG.Proof.MlDsa.Arm.Sign.IOi p D σ x := by
  simp only [VG.Proof.MlDsa.Arm.Sign.fChk, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf
  have L := h.k.d.im.st.lay
  obtain ⟨t, _, _, _, hpass, hct, hz, hh⟩ := h.pass h15
  exact ⟨p.ℓ * t, h.k.step hP ik, by rw [L.keepBytes hP kct, hct], Fam.keep L hP fy hz, HFam.keep L hP f5 hh, hpass,
    by rw [hcs _ (by decide) (by decide), h15]⟩

theorem rest_tr {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p 0) (VG.Proof.MlDsa.Arm.Sign.IM p D)) (rest P p) (VG.Proof.MlDsa.Arm.Sign.RS p D (VG.Proof.MlDsa.Arm.Sign.LeakEq p 0) (VG.Proof.MlDsa.Arm.Sign.FS p D)) := by
  refine VG.Proof.MlDsa.Arm.Sign.liftR (fun σ s _ h => VG.Proof.MlDsa.Arm.Sign.rest_ok hP h3 h) ?_
  have hc := VG.Proof.MlDsa.Arm.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.Arm.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.Arm.Sign.fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, f5⟩, -⟩, -⟩, -⟩ := hf'
  have hp := VG.Proof.MlDsa.Arm.Sign.paramsOk h3
  unfold rest
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.decode_tr hP hd) (RelCT.seq (VG.Proof.MlDsa.Arm.Sign.signLoop_tr hP hp hc1 hb hks hl) ?_)
  unfold ifOk
  refine VG.Proof.MlDsa.Arm.Sign.ifOkElse_tr (D := D) (fun x y h => by rw [h.2.1]) (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.output_tr hP ho (E := fun _ _ => True))
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, _, s₁, s₂⟩, h15, hj⟩, ⟨hPx, hcx, _⟩, ⟨hPy, hcy, _⟩, hne⟩ => ?_)
    fun _ _ h => h) (RelCT.mono VG.Proof.MlDsa.Arm.Sign.nil_tr (fun _ _ h => h) fun _ _ _ => trivial)
  have e₁ := VG.Proof.MlDsa.Arm.Sign.r11_one s₁.r01 hne
  have e₂ : y₀.gpr .r11 = 1 := h15 ▸ e₁
  obtain ⟨_, f, hx, hy⟩ := hj e₁
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, s₁.io hf e₁ hPx hcx, s₂.io hf e₂ hPy hcy⟩, f,
    HFam.keep s₁.k.d.im.st.lay hPx f5 hx, HFam.keep s₂.k.d.im.st.lay hPy f5 hy⟩

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseACT`. -/
section

/-!
# ML-DSA signing on ARMv7: `ExpandA` leaks only `ρ`

Two runs of `ExpandA` with the same `ρ` compute the same results of
`vg_mldsa_rej_ntt_poly`, so they agree on `r11` (`RA`), and leak the same
(`expandA_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `r11`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  VG.Proof.MlDsa.Arm.Sign.RR p D (fun σ s => VG.Proof.MlDsa.Arm.Sign.IA p D σ e s) fun x y => x.gpr .r11 = y.gpr .r11

theorem callE_ok' {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.Arm.Sign.IA p D σ e s) (hs : bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS)) 34 = VG.Proof.MlDsa.Arm.Sign.seedE p σ e) :
    WP isa (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (VG.Proof.MlDsa.Arm.Sign.aBase p + e)), .ptr (sc oPS)]) s
      fun s' => VG.Proof.MlDsa.Arm.Sign.JE p D e σ s' ∧ s'.gpr .r11 = s.gpr .r11 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.eChk_spec he
  refine WP.mono (VG.Proof.MlDsa.Arm.Sign.rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3 _ (by decide) (by decide)⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem sampleE_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} {e : Nat} (he : VG.Proof.MlDsa.Arm.Sign.eChk p e = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RA p D e) (sampleE P p e) (VG.Proof.MlDsa.Arm.Sign.RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.Arm.Sign.eChk_spec he
  rw [VG.Proof.MlDsa.Arm.Sign.sampleE_eq]
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RR p D (fun σ s => VG.Proof.MlDsa.Arm.Sign.IA p D σ e s ∧ bytesAt s.mem (VG.Proof.MlDsa.Arm.Sign.pa s (sc oRS)) 34 = VG.Proof.MlDsa.Arm.Sign.seedE p σ e)
    fun x y => x.gpr .r11 = y.gpr .r11) ?_ (RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RR p D (VG.Proof.MlDsa.Arm.Sign.JE p D e)
      fun x y => x.gpr .r11 = y.gpr .r11 ∧ x.gpr .r0 = y.gpr .r0) ?_ ?_)
  · refine VG.Proof.MlDsa.Arm.Sign.stepRR (F := fun s s' => s'.gpr .r11 = s.gpr .r11) (fun σ s _ h => VG.Proof.MlDsa.Arm.Sign.blkE_ok he h)
      (VG.Proof.MlDsa.Arm.Sign.block_tr (rs := [.r7]) rfl fun x y h r hr => ?_) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.lrel fun _ _ h => h.st).regs (.r7, VG.Proof.MlDsa.Arm.Sign.scrLen p) (by simp [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW])
  · refine VG.Proof.MlDsa.Arm.Sign.stepRR (F := fun s s' => s'.gpr .r11 = s.gpr .r11) (fun σ s _ h => VG.Proof.MlDsa.Arm.Sign.callE_ok' hP he h.1 h.2)
      ((VG.Proof.MlDsa.Arm.Sign.rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, VG.Proof.MlDsa.Arm.Sign.seedE, VG.Proof.MlDsa.Arm.Sign.seedE, VG.Proof.MlDsa.Arm.Sign.pub_rho hpub]
  · refine VG.Proof.MlDsa.Arm.Sign.stepRR (F := fun s s' => s'.gpr .r11 = s.gpr .r11 &&& s.gpr .r0)
      (fun σ s _ h => WP.conj (VG.Proof.MlDsa.Arm.Sign.andE_ok he h) (WP.mono (VG.Proof.MlDsa.Arm.Sign.and11_ok s) fun _ h => h.1))
      (VG.Proof.MlDsa.Arm.Sign.block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

theorem expandA_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.Arm.Sign.aChk p = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Sign.RR p D (fun σ s => VG.Proof.MlDsa.Arm.Sign.St p D σ s ∧ s.gpr .r11 = 1) fun _ _ => True)
      (Impl.MlDsa.Arm.Sign.expandA P p) (VG.Proof.MlDsa.Arm.Sign.RA p D (p.k * p.ℓ)) := by
  simp only [VG.Proof.MlDsa.Arm.Sign.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.Arm.Sign.expandA
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Sign.RA p D 0) (VG.Proof.MlDsa.Arm.Sign.stepRR (F := fun s s' => s'.gpr .r11 = s.gpr .r11) (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.IA p D σ 0 s)
    (E' := fun x y => x.gpr .r11 = y.gpr .r11)
    (fun σ s _ h => ?_) (VG.Proof.MlDsa.Arm.Sign.copy_tr (by decide) (by decide) fun x y h => ?_)
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (VG.Proof.MlDsa.Arm.Sign.copy_okB h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1 _ (by decide) (by decide)⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .r11 = 1 := by rw [hcs1 _ (by decide) (by decide), h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, VG.Proof.MlDsa.Arm.Sign.rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · have L := h.lrel fun _ _ h => h.1
    exact ⟨L.regs (.r7, VG.Proof.MlDsa.Arm.Sign.scrLen p) (by simp [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW]), L.regs (.r4, p.skLen) (by simp [VG.Proof.MlDsa.Arm.Sign.sgR, VG.Proof.MlDsa.Arm.Sign.sgW])⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · have := VG.Proof.MlDsa.Arm.Sign.seqR_tr (f := sampleE P p) (R := fun k => VG.Proof.MlDsa.Arm.Sign.RA p D k) (p.k * p.ℓ) 0
      fun k _ hk => VG.Proof.MlDsa.Arm.Sign.sampleE_tr hP (he k (by omega))
    rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT`. -/
section

/-!
# ML-DSA signing on ARMv7: constant time

Two runs whose entry states agree on `signK`'s public data (`signLeakT` among
them) leak the same: the prologue and the return only the pointers, `ExpandA`
only `ρ` (`expandA_tr`), and the rest what `signLeakT` says after `ρ`, on
which they agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem relStart {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (VG.Proof.MlDsa.Arm.Sign.Rel2 Pre Pub fun σ s => s = σ) c Q) : ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

theorem ldrSp_one {s u : State} {a : List Leak} (h : execBlock isa [.ldrSp .r12 0] s = some (u, a)) :
    a = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 0))] ∧ u.gpr .r12 = stackArg s 0 := by
  simp only [execBlock] at h
  split at h
  · cases h
  · rename_i s' hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    simp only [isa, exec, State.load32, show (0 : Nat) < 4096 from by decide, ite_true] at hs
    split at hs
    · simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      simp [State.setReg, stackArg, stackArgAddr]
    · cases hs

/-- The prologue leaks only the stack pointer and the pointer to `scratch` it loads. -/
theorem pro_tr {P : State → State → Prop} (hP : ∀ x y, P x y → x.sp = y.sp ∧ stackArg x 0 = stackArg y 0) :
    RelCT isa P (.block VG.Impl.MlDsa.Arm.Sign.pro) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨hsp, harg⟩ := hP _ _ hp
  rw [Exec.block_iff, VG.Proof.MlDsa.Arm.Sign.pro_eq, List.append_assoc, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, a₁⟩, h₁, g₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, a₂⟩, h₂, g₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨v₁, b₁⟩, f₁, k₁⟩ := Option.map_eq_some_iff.mp g₁
  obtain ⟨⟨v₂, b₂⟩, f₂, k₂⟩ := Option.map_eq_some_iff.mp g₂
  simp only [Prod.mk.injEq] at k₁ k₂
  obtain ⟨ea₁, r₁⟩ := VG.Proof.MlDsa.Arm.Sign.ldrSp_one h₁
  obtain ⟨ea₂, r₂⟩ := VG.Proof.MlDsa.Arm.Sign.ldrSp_one h₂
  refine ⟨?_, trivial⟩
  rw [← k₁.2, ← k₂.2, ea₁, ea₂, hsp, VG.Proof.MlDsa.Arm.Sign.execBlock_tr (rs := [.r12]) (by decide) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [r₁, r₂, harg]) f₁ f₂]

section
variable {p : Params} {D : Nat}

/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : (VG.Proof.MlDsa.Arm.Sign.signK p D).pub σ₁ σ₂)
    (hA₁ : expandA p maxBounds (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ₁) = some (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ₁)))
    (hA₂ : expandA p maxBounds (VG.Proof.MlDsa.Arm.Sign.rhoOf p σ₂) = some (amat p (VG.Proof.MlDsa.Arm.Sign.Am p σ₂))) : VG.Proof.MlDsa.Arm.Sign.LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2
  rw [signLeakT_eq hA₁, signLeakT_eq hA₂] at e
  have hρ : (VG.Proof.MlDsa.Arm.Sign.skOf p σ₁).take 32 = (VG.Proof.MlDsa.Arm.Sign.skOf p σ₂).take 32 := VG.Proof.MlDsa.Arm.Sign.pub_rho hpub
  rw [hρ] at e
  exact List.append_cancel_left e

theorem rr_rs {I E : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.Arm.Sign.RR p D I E x y) : VG.Proof.MlDsa.Arm.Sign.RS p D (fun _ _ => True) I x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, trivial, i₁, i₂⟩

theorem sign_ct {P : Prims} (hP : VG.Proof.MlDsa.Arm.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) :
    ConstantTime isa (VG.Proof.MlDsa.Arm.Sign.signK p D).pre (VG.Proof.MlDsa.Arm.Sign.signK p D).pub (Impl.MlDsa.Arm.Sign.sign P p) := by
  have hc := VG.Proof.MlDsa.Arm.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.Arm.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.Arm.Sign.fChk, Bool.and_eq_true, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsz⟩ := hf'
  refine VG.Proof.MlDsa.Arm.Sign.relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.Arm.Sign.sign
  refine RelCT.seq (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.relInvE (J := fun σ s => VG.Proof.MlDsa.Arm.Sign.St p D σ s ∧ s.gpr .r11 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (VG.Proof.MlDsa.Arm.Sign.pro_ok hp) fun s₁ ⟨h₁, hf₁, h15⟩ => ⟨VG.Proof.MlDsa.Arm.Sign.entry_st h3 hp h₁ hf₁, h15⟩)
    (VG.Proof.MlDsa.Arm.Sign.pro_tr fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ => by
      subst h₁ h₂
      exact ⟨hpub.2.2.2.2.2.1, hpub.2.2.2.2.1⟩)) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (VG.Proof.MlDsa.Arm.Sign.expandA_tr hP ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r) ?_
    (VG.Proof.MlKem.Arm.taint_prog [.r7] (fun x y h => h) (by taint_decide))
  unfold ifOk
  refine VG.Proof.MlDsa.Arm.Sign.ifOkElse_tr (D := D) (P := VG.Proof.MlDsa.Arm.Sign.RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (VG.Proof.MlDsa.Arm.Sign.rest_tr hP h3)
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, ⟨hPx, _, _⟩, ⟨hPy, _, _⟩, hne⟩ => ?_)
    fun x y h => VG.Proof.MlDsa.Arm.Sign.lrel_r7 (h.lrel fun _ _ h => h.st))
    (RelCT.mono VG.Proof.MlDsa.Arm.Sign.nil_tr (fun _ _ h => h) fun x y h =>
      VG.Proof.MlDsa.Arm.Sign.ifOk_r7 (I := fun σ s => VG.Proof.MlDsa.Arm.Sign.IA p D σ (p.k * p.ℓ) s) (fun _ _ h => h.st) (E := fun _ _ => True)
        (C := fun x₀ => x₀.gpr .r11 = 0)
        (by obtain ⟨x₀, y₀, R, hx, hy, h0⟩ := h; exact ⟨x₀, y₀, VG.Proof.MlDsa.Arm.Sign.rr_rs R, hx, hy, h0⟩))
  have e₁ := VG.Proof.MlDsa.Arm.Sign.r11_one i₁.r01 hne
  have e₂ : y₀.gpr .r11 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, VG.Proof.MlDsa.Arm.Sign.pub_leq hpub (VG.Proof.MlDsa.Arm.Sign.expandA_max ok₁) (VG.Proof.MlDsa.Arm.Sign.expandA_max ok₂),
    ⟨i₁.st.step hPx st0, ok₁, Fam.keep i₁.st.lay hPx fa0 fam₁⟩,
    ⟨i₂.st.step hPy st0, ok₂, Fam.keep i₂.st.lay hPy fa0 fam₂⟩⟩

end

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst`. -/
section

/-!
# ML-DSA signing on ARMv7: the primitives it calls

The verified ARMv7 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`), with 28 bytes of stack below the
function's stack pointer: their contracts with the stack of their
registrations (at most 28 bytes, or 20 for the four whose fifth argument
signing pushes), that their frames fit in it, and, of the two samplers whose
result signing branches on, that it depends only on their public data and that
they succeed only if the algorithm finishes within `maxBounds` (from what
their own proofs say they return).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The ARMv7 implementations of the primitives. -/
def prims : Prims where
  ntt := Impl.MlDsa.Arm.Arith.ntt
  invNtt := Impl.MlDsa.Arm.Arith.nttInv
  mul := Impl.MlDsa.Arm.Arith.mul
  mulAdd := Impl.MlDsa.Arm.Arith.mulAdd
  add := Impl.MlDsa.Arm.Arith.add
  sub := Impl.MlDsa.Arm.Arith.sub
  rejNTT := Impl.MlDsa.Arm.Sample.rejNTT
  expandMask := Impl.MlDsa.Arm.Sample.expandMask
  ball := Impl.MlDsa.Arm.Sample.sampleInBall
  highBits := Impl.MlDsa.Arm.Round.highBits
  lowBits := Impl.MlDsa.Arm.Round.lowBits
  normLt := Impl.MlDsa.Arm.Round.normLt
  makeHint := Impl.MlDsa.Arm.Round.makeHint
  simpleBitPack := Impl.MlDsa.Arm.Pack.simpleBitPack
  bitPack := Impl.MlDsa.Arm.Pack.bitPack
  bitUnpack := Impl.MlDsa.Arm.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.Arm.Pack.hintBitPack

/-- The stack signing may use below its stack pointer. -/
abbrev signStack : Nat := 28

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.Arm.Sample VG.Proof.MlDsa.Sample

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract Arm.abi 8).pre s)
    (e : Exec isa Impl.MlDsa.Arm.Sample.rejNTT s tr s') :
    s'.gpr .r0 = if (rnFold [] (G (bytesAt s.mem (State.addr (s.gpr .r0)) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := RejNtt.correct (RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract Arm.abi 8).pub s₁ s₂) :
    bytesAt s₁.mem (State.addr (s₁.gpr .r0)) 34 = bytesAt s₂.mem (State.addr (s₂.gpr .r0)) 34 := by
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨_, hb, _⟩ := h
  exact VG.Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract Arm.abi 8).pre s)
    (e : Exec isa Impl.MlDsa.Arm.Sample.sampleInBall s tr s') :
    s'.gpr .r0 = if (ballFold (s.gpr .r2).toNat
      (H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Ball.correct (Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract Arm.abi 8).pub s₁ s₂) :
    s₁.gpr .r2 = s₂.gpr .r2 ∧ bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (s₁.gpr .r1).toNat =
      bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (s₂.gpr .r1).toNat := by
  sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨_, hb, _, _, h2, _⟩ := h
  exact ⟨h2, (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
def prims_ok : VG.Proof.MlDsa.Arm.Sign.PrimsOk VG.Proof.MlDsa.Arm.Sign.prims VG.Proof.MlDsa.Arm.Sign.signStack where
  ntt := ⟨28, by decide, Proof.MlDsa.Arm.Arith.Ntt.verified, by decide +kernel⟩
  invNtt := ⟨28, by decide, Proof.MlDsa.Arm.Arith.NttInv.verified, by decide +kernel⟩
  mul := ⟨24, by decide, Proof.MlDsa.Arm.Arith.Mul.mul_verified, by decide +kernel⟩
  mulAdd := ⟨24, by decide, Proof.MlDsa.Arm.Arith.Mul.mulAdd_verified, by decide +kernel⟩
  add := ⟨0, by decide, Proof.MlDsa.Arm.Arith.AddSub.add_verified, by decide +kernel⟩
  sub := ⟨0, by decide, Proof.MlDsa.Arm.Arith.AddSub.sub_verified, by decide +kernel⟩
  rejNTT := ⟨8, by decide, Proof.MlDsa.Arm.Sample.rejNTT_verified, by decide +kernel⟩
  expandMask := ⟨8, by decide, Proof.MlDsa.Arm.Sample.expandMask_verified, by decide +kernel⟩
  ball := ⟨8, by decide, Proof.MlDsa.Arm.Sample.sampleInBall_verified, by decide +kernel⟩
  highBits := ⟨0, by decide, Proof.MlDsa.Arm.Round.Bits.high_verified, by decide +kernel⟩
  lowBits := ⟨0, by decide, Proof.MlDsa.Arm.Round.Bits.low_verified, by decide +kernel⟩
  normLt := ⟨4, by decide, Proof.MlDsa.Arm.Round.NormLt.verified, by decide +kernel⟩
  makeHint := ⟨12, by decide, Proof.MlDsa.Arm.Round.MakeHint.verified, by decide +kernel⟩
  simpleBitPack := ⟨0, by decide, Proof.MlDsa.Arm.Pack.simpleBitPack_verified, by decide +kernel⟩
  bitPack := ⟨4, by decide, Proof.MlDsa.Arm.Pack.bitPack_verified, by decide +kernel⟩
  bitUnpack := ⟨4, by decide, Proof.MlDsa.Arm.Pack.bitUnpack_verified, by decide +kernel⟩
  hintBitPack := ⟨8, by decide, Proof.MlDsa.Arm.Pack.Hint.hintBitPack_verified, by decide +kernel⟩
  rejRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.Arm.Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.Arm.Sign.rn_ret h₁ e₁, VG.Proof.MlDsa.Arm.Sign.rn_ret h₂ e₂, VG.Proof.MlDsa.Arm.Sign.rn_pub s₁ s₂ hp]⟩
  rejMax := fun s t s' h e h1 => by
    rw [VG.Proof.MlDsa.Arm.Sign.rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (State.addr (s.gpr .r0)) 34) 1008)).length = 256
    · rw [VG.Proof.MlDsa.Sign.rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [VG.Proof.MlDsa.Sign.ifn hf] at h1; exact absurd h1.symm VG.Proof.MlDsa.Arm.Sign.one_ne_zero32
  ballRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.Arm.Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.Arm.Sign.sb_ret h₁ e₁, VG.Proof.MlDsa.Arm.Sign.sb_ret h₂ e₂, (VG.Proof.MlDsa.Arm.Sign.sb_pub s₁ s₂ hp).1, (VG.Proof.MlDsa.Arm.Sign.sb_pub s₁ s₂ hp).2]⟩
  ballMax := fun s t s' h e h1 => by
    rw [VG.Proof.MlDsa.Arm.Sign.sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (s.gpr .r2).toNat
      (H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide)
        (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [VG.Proof.MlDsa.Sign.ifn hf] at h1; exact absurd h1.symm VG.Proof.MlDsa.Arm.Sign.one_ne_zero32
  hD := by decide
  hD' := by decide

end VG.Proof.MlDsa.Arm.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified`. -/
section

/-!
# ML-DSA signing on ARMv7: verified

`vg_mldsa{44,65,87}_sign` (`sign prims p`) is verified against
`signContractT`: `signContract` with `signLeakT`
(`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`, which tags what each iteration
of the loop leaks after its `c̃` with whether it was rejected. The contract's
`signLeak` tags the iterations the same way (`signLeakT_eq_signLeak`), so
`signContractT` is `signContract` (`signContractT_eq`), against which
`sign*_verified'` state it.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `signContract`, with `signLeakT` for `signLeak`. -/
def signContractT (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeakT p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

/-- A state satisfying `signContractT`'s precondition: `scratch` at `0x10000`, on the stack. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 0x3100 | .r3 => 0x4000
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80002 then 1 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩, ⟨0x80000, 4⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK_implies_of {p : Params} (hsat : ∃ s, (VG.Proof.MlDsa.Arm.Sign.signContractT p Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack).pre s) :
    (VG.Proof.MlDsa.Arm.Sign.signK p VG.Proof.MlDsa.Arm.Sign.signStack).Implies (VG.Proof.MlDsa.Arm.Sign.signContractT p Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack) where
  pre := by
    intro s h
    sig_pre [VG.Proof.MlDsa.Arm.Sign.signContractT, signSig, VG.Proof.MlDsa.Arm.Sign.signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, -, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, -, n1, n2, n3, n4, n5⟩ := h
    simp only [Nat.mul_comm (scratchWords p) 8] at hwr d2 d4 d6 d7 d9 k5 n5
    exact ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩
  post := by
    intro s s' _ h
    sig_post [VG.Proof.MlDsa.Arm.Sign.signContractT, signSig, VG.Proof.MlDsa.Arm.Sign.signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32]
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [VG.Proof.MlDsa.Arm.Sign.signContractT, signSig, VG.Proof.MlDsa.Arm.Sign.signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, hb, h0, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) :
    (VG.Proof.MlDsa.Arm.Sign.signK p VG.Proof.MlDsa.Arm.Sign.signStack).Implies (VG.Proof.MlDsa.Arm.Sign.signContractT p Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack) := by
  refine VG.Proof.MlDsa.Arm.Sign.signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [VG.Proof.MlDsa.Arm.Sign.signContractT, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using VG.Proof.MlDsa.Arm.Sign.signSat mlDsa44
  · sig_implies_sat [VG.Proof.MlDsa.Arm.Sign.signContractT, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using VG.Proof.MlDsa.Arm.Sign.signSat mlDsa65
  · sig_implies_sat [VG.Proof.MlDsa.Arm.Sign.signContractT, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using VG.Proof.MlDsa.Arm.Sign.signSat mlDsa87

theorem sign_verified {p : Params} (h3 : VG.Proof.MlDsa.Arm.Sign.Ok3 p) :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign VG.Proof.MlDsa.Arm.Sign.prims p) (VG.Proof.MlDsa.Arm.Sign.signContractT p Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack) :=
  Verified.of_correct (VG.Proof.MlDsa.Arm.Sign.sign_correct VG.Proof.MlDsa.Arm.Sign.prims_ok h3) (VG.Proof.MlDsa.Arm.Sign.sign_ct VG.Proof.MlDsa.Arm.Sign.prims_ok h3) (VG.Proof.MlDsa.Arm.Sign.signK_implies h3)

/-! Against the contract: `signContractT` is `signContract`, whose leakage
tags each iteration as `signLeakT` does (`signLeakT_eq_signLeak`). -/

theorem signContractT_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    VG.Proof.MlDsa.Arm.Sign.signContractT p A stack = signContract p A stack := by
  unfold VG.Proof.MlDsa.Arm.Sign.signContractT signContract
  simp only [Sign.signLeakT_eq_signLeak]

theorem sign44_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign VG.Proof.MlDsa.Arm.Sign.prims mlDsa44) (signContract mlDsa44 Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack) :=
  VG.Proof.MlDsa.Arm.Sign.signContractT_eq mlDsa44 Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack ▸ VG.Proof.MlDsa.Arm.Sign.sign_verified (.inl rfl)

theorem sign65_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign VG.Proof.MlDsa.Arm.Sign.prims mlDsa65) (signContract mlDsa65 Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack) :=
  VG.Proof.MlDsa.Arm.Sign.signContractT_eq mlDsa65 Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack ▸ VG.Proof.MlDsa.Arm.Sign.sign_verified (.inr (.inl rfl))

theorem sign87_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign VG.Proof.MlDsa.Arm.Sign.prims mlDsa87) (signContract mlDsa87 Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack) :=
  VG.Proof.MlDsa.Arm.Sign.signContractT_eq mlDsa87 Arm.abi VG.Proof.MlDsa.Arm.Sign.signStack ▸ VG.Proof.MlDsa.Arm.Sign.sign_verified (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.Sign

end
