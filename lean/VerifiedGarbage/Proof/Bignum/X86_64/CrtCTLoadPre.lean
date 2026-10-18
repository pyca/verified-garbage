module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtLoadPre
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtLoadPre
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: constant time, loading `pre`

`loadPre j po` is constant time (`loadPre_ct`), given that `po` is: its
pointers and lengths are public (the workspace, `pre`, `w` and `d`), and
only data flows from `pre`'s words and the arrays.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of `loadPre`: the workspace at `W` of `Zl` bytes and `w`
words, `pre` at `P`, the offset `d`, and the stack pointer. -/
structure LPub where
  W : Addr
  Zl : Nat
  w : Nat
  P : Addr
  d : Nat
  rsp : Addr

/-- The workspace, and `pre`'s `w` words from word `d` readable and apart from
array `j`. -/
def LpGood (j : Nat) (p : LPub) (s : State) : Prop :=
  ∃ minv, Good s p.W p.Zl p.w minv ∧ slot p.w 8 ≤ p.Zl ∧ 1 ≤ p.w ∧ p.w < 2 ^ 31 ∧ j < 8 ∧
    (∀ i < p.w, InRegions (s.rd ++ s.wr) (off p.P (8 * p.d + 8 * i)) 8) ∧
    (∀ i < p.w, ∀ b < 8, ofs p.W (off p.P (8 * p.d + 8 * i) + BitVec.ofNat 64 b) < slot p.w j ∨
      slot p.w j + 8 * (p.w + 2) ≤ ofs p.W (off p.P (8 * p.d + 8 * i) + BitVec.ofNat 64 b))

/-- Before `loadPre`: `LpGood`, and the stack argument 12 is `pre`. -/
def LpPre (j : Nat) (p : LPub) (s : State) : Prop :=
  LpGood j p s ∧ s.gpr .rsp = p.rsp ∧ InRegions (s.rd ++ s.wr) (stackArgAddr s 12) 8 ∧
    s.mem.readW (stackArgAddr s 12) 64 = p.P

/-- Before `po`: `pre` in `rsi`. -/
def LpA (j : Nat) (p : LPub) (s : State) : Prop :=
  LpGood j p s ∧ s.gpr .rsi = p.P

/-- After `po`: the offset in `rax`. -/
def LpB (j : Nat) (p : LPub) (s : State) : Prop :=
  LpGood j p s ∧ s.gpr .rsi = p.P ∧ s.gpr .rax = BitVec.ofNat 64 p.d

/-- The source, the array and its length in `rsi`, `r8` and `r12`. -/
def LpC (j : Nat) (p : LPub) (s : State) : Prop :=
  LpGood j p s ∧ s.gpr .rsi = off p.P (8 * p.d) ∧ s.gpr .r8 = off p.W (slot p.w j) ∧
    s.gpr .r12 = BitVec.ofNat 64 p.w

/-- Before the copy: the array also in `rbx`. -/
def LpD (j : Nat) (p : LPub) (s : State) : Prop :=
  LpGood j p s ∧ s.gpr .rsi = off p.P (8 * p.d) ∧ s.gpr .rbx = off p.W (slot p.w j) ∧
    s.gpr .r12 = BitVec.ofNat 64 p.w

/-- After the copy. -/
def LpE (j : Nat) (p : LPub) (s : State) : Prop :=
  LpGood j p s ∧ s.gpr .rbx = off p.W (slot p.w j) ∧ s.gpr .r12 = BitVec.ofNat 64 p.w

/-- Before the comparison: the modulus' array in `r10`. -/
def LpF (j : Nat) (p : LPub) (s : State) : Prop :=
  s.gpr .rbx = off p.W (slot p.w j) ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧
    s.gpr .r10 = off p.W (slot p.w aN) ∧ s.gpr .rdi = p.W

theorem LpGood.rdi {j : Nat} {p : LPub} {s : State} (h : LpGood j p s) : s.gpr .rdi = p.W := by
  obtain ⟨_, hg, _⟩ := h; exact hg.rdi

/-- `LpGood` through a change of registers but `rdi`. -/
theorem LpGood.congr {j : Nat} {p : LPub} {s t : State} {rs : List Reg} (h : LpGood j p s) (hm : t.mem = s.mem)
    (k : Keep rs s t) (hdi : Reg.rdi ∉ rs) : LpGood j p t := by
  obtain ⟨minv, hg, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨minv, ⟨hg.scr.congr k.2.2, (k.1 _ hdi).trans hg.rdi, hm ▸ hg.hdr⟩, h1, h2, h3, h4,
    fun i hi => by rw [k.2.1, k.2.2]; exact h5 i hi, h6⟩

/-- `LpGood` through a change of array `j`'s words. -/
theorem LpGood.of_outside {j : Nat} {p : LPub} {s t : State} {rs : List Reg} (h : LpGood j p s) {n : Nat}
    (ho : Outside p.W (slot p.w j) n s.mem t.mem) (hn : n ≤ 8 * (p.w + 2)) (k : Keep rs s t)
    (hdi : Reg.rdi ∉ rs) : LpGood j p t := by
  obtain ⟨minv, hg, h1, h2, h3, h4, h5, h6⟩ := h
  have ho' : Outside p.W (slot p.w j) (8 * (p.w + 2)) s.mem t.mem := ho.mono (Nat.le_refl _) (by omega)
  exact ⟨minv, ⟨hg.scr.congr k.2.2, (k.1 _ hdi).trans hg.rdi, (Arrays.of_outside (js := [j])
    (List.mem_singleton_self _) ho' (Nat.le_refl _) (Nat.le_refl _)).hdr hg.hdr⟩, h1, h2, h3, h4,
    fun i hi => by rw [k.2.1, k.2.2]; exact h5 i hi, h6⟩

theorem loadPre_ct {α : Type} (π : α → LPub) {j : Nat} {po : List Instr} {Q : α → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax, .rsi, .rdi]) (.block [.alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rsi (.reg .rax),
      .mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))]) hc).isSome = true)
    (hQ : ∀ a s t, Q a s → t.mem = s.mem → Keep [.rsi] s t → Q a t)
    (hpo : RelCT isa (Two fun a s => LpA j (π a) s ∧ Q a s) (.block po) (Two (LpB j))) :
    RelCT isa (Two fun a s => LpPre j (π a) s ∧ Q a s) (seqs (Crt.loadPre j po)) fun _ _ => True := by
  unfold Crt.loadPre
  simp only [seqs]
  refine RelCT.seq (R := Two (LpC j)) (RelCT.seq (R := Two (LpC j))
    (RelCT.block_append (RelCT.seq (RelCT.block_append (RelCT.seq ?_ hpo)) ?_)) ?_) ?_
  -- `pre` into `rsi`.
  · refine two_piece [.rsp] (pins_of (fun a _ => (π a).rsp) fun a s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.2.1) (by taint_decide) fun a s h => ?_
    obtain ⟨⟨hg, hsp, ha, hP⟩, hq⟩ := h
    have e13 : off (s.gpr .rsp) (8 * 13) = stackArgAddr s 12 := rfl
    exact WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = (π a).P ∧ t.mem = s.mem)
      (by xrun [Crt.stk, State.ea, hdrOff, e13, ha, hP]) rfl) fun t ⟨⟨h1, hm⟩, k⟩ =>
        ⟨⟨hg.congr hm k (by decide), h1⟩, hQ a s t hq hm k⟩
  -- The source, the array and its length.
  · refine (two_piece (Φ := LpB j) [.rax, .rsi, .rdi] (pins_of (fun p r => if r = .rax then BitVec.ofNat 64 p.d else
      if r = .rsi then p.P else p.W) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.2
        · exact h.2.1
        · exact h.1.rdi) hT fun p s h => ?_)
    obtain ⟨hgd, hsi, hax⟩ := h
    obtain ⟨minv, hg, hZ, hw, hw', hj, -, -⟩ := id hgd
    have hn := hg.scr.nowrap
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.W (8 * i)) 8 := fun i hi =>
      hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega_arith)
    have h8d : BitVec.ofNat 64 p.d + BitVec.ofNat 64 p.d + (BitVec.ofNat 64 p.d + BitVec.ofNat 64 p.d) +
        (BitVec.ofNat 64 p.d + BitVec.ofNat 64 p.d + (BitVec.ofNat 64 p.d + BitVec.ofNat 64 p.d)) =
        BitVec.ofNat 64 (8 * p.d) := by
      simp only [← BitVec.ofNat_add]; congr 1; omega
    have ep : p.P + BitVec.ofNat 64 (8 * p.d) = off p.P (8 * p.d) := rfl
    exact WP.mono (WP.keep [.rax, .rsi, .r8, .r12] (Q := fun t => t.gpr .rsi = off p.P (8 * p.d) ∧
        t.gpr .r8 = off p.W (slot p.w j) ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hax, hsi, h8d, ep, hl (sArr j) (by unfold sArr; omega_arith),
        hl sW (by decide), hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun t ⟨⟨h1, h2, h3, hm⟩, k⟩ =>
      ⟨hgd.congr hm k (by decide), h1, h2, h3⟩
  -- The array cleared.
  · refine (two_piece [.r8, .r12] (pins_of (fun p r => if r = .r8 then off p.W (slot p.w j) else
      BitVec.ofNat 64 p.w) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide) fun p s h => ?_)
    obtain ⟨hgd, hsi, h8, h12⟩ := h
    obtain ⟨minv, hg, hZ, hw, hw', hj, -, -⟩ := id hgd
    have sj := Nat.le_trans (slot_le (w := p.w) hj) hZ
    exact WP.mono (zeroAccLoop_ok hg.scr h8 h12 hw hw' sj) fun t ⟨_, ho, k⟩ =>
      ⟨hgd.of_outside ho (Nat.le_refl _) k (by decide), (k.gpr (by decide)).trans hsi,
        (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h12⟩
  -- `rbx := r8`.
  refine ct_taint [.r8] (Ψ := LpD j) (pins_of (fun p _ => off p.W (slot p.w j)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2.1) (by taint_decide) (fun p s h => ?_) ?_
  · obtain ⟨hgd, hsi, h8, h12⟩ := h
    exact WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off p.W (slot p.w j) ∧ t.mem = s.mem)
      (by xrun [h8]) rfl) fun t ⟨⟨h1, hm⟩, k⟩ =>
      ⟨hgd.congr hm k (by decide), (k.gpr (by decide)).trans hsi, h1, (k.gpr (by decide)).trans h12⟩
  -- `[j] := pre`'s words.
  refine ct_taint [.rsi, .rbx, .r12] (Ψ := LpE j) (pins_of (fun p r => if r = .rsi then off p.P (8 * p.d) else
      if r = .rbx then off p.W (slot p.w j) else BitVec.ofNat 64 p.w) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide) (fun p s h => ?_) ?_
  · obtain ⟨hgd, hsi, hbx, h12⟩ := h
    obtain ⟨minv, hg, hZ, hw, hw', hj, hrd, hsep⟩ := id hgd
    have sj := Nat.le_trans (slot_le (w := p.w) hj) hZ
    have hn := hg.scr.nowrap
    exact WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega_arith) hrd
      (fun i hi => hg.scr.st (by omega_arith))
      (fun i hi b hb => by rcases hsep i hi b hb with h | h <;> [exact .inl h; exact .inr (by omega_arith)]))
      fun t ⟨_, _, ho, k⟩ => ⟨hgd.of_outside ho (by omega) k (by decide), (k.gpr (by decide)).trans hbx,
        (k.gpr (by decide)).trans h12⟩
  -- The modulus' array.
  refine ct_taint [.rdi] (Ψ := LpF j) (pins_of (fun p _ => p.W) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi) (by taint_decide) (fun p s h => ?_) ?_
  · obtain ⟨hgd, hbx, h12⟩ := h
    obtain ⟨minv, hg, hZ, -, -, -, -, -⟩ := id hgd
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.W (8 * i)) 8 := fun i hi =>
      hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega_arith)
    exact WP.mono (WP.keep [.r10, .rbp] (Q := fun t => t.gpr .r10 = off p.W (slot p.w aN))
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aN) (by unfold sArr aN; omega_arith),
        hg.hdr.harr aN (by decide)]) rfl) fun t ⟨h1, k⟩ =>
      ⟨(k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h12, h1, (k.gpr (by decide)).trans hg.rdi⟩
  -- The comparison and the mask.
  exact two_taint [.rbx, .r12, .r10] (pins_of (fun p r => if r = .rbx then off p.W (slot p.w j) else
      if r = .r12 then BitVec.ofNat 64 p.w else off p.W (slot p.w aN)) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1) (by taint_decide)

end VG.Proof.Bignum.X86_64
