module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# ChaCha20 and Poly1305 together (x86-64): the keystream stored

`Stitch.storeRow kOff` writes a row of the eight blocks out to
`buf + kOff` (`kA buf`) rather than XORing it into the data (`storeRow_out`,
an `OutOk` for `Avx2.finishWith_ok`), so that `finishWith (storeRow kOff)`
leaves the keystream of the eight blocks there (`finishK_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20.X86_64.Avx2 (finishWith)
open VG.Proof.ChaCha20.X86_64.Avx2
open VG.Spec.ChaCha20 (stateAt serialize)
open VG.Proof.ChaCha20

/-- Where `tailK` stores the keystream: `buf + kOff`. -/
abbrev kA (buf : Addr) : Addr := buf + BitVec.ofNat 64 608

/-- The eight blocks' 512 bytes there. -/
abbrev kR (buf : Addr) : Region := ⟨kA buf, 512⟩

/-- The stores of row `row` of blocks `i` and `i + 4`, from the lanes of `x`. -/
def stP (row : Nat) (x : XReg) (i : Nat) : List Instr :=
  [.vmovdquStore .l128 (at_ .rcx (608 + 64 * i + 16 * row)) x, .vop (.vextracti128 .xmm13 x 1),
   .vmovdquStore .l128 (at_ .rcx (608 + 64 * (i + 4) + 16 * row)) .xmm13]

theorem storeRow_eq (row : Nat) (x0 x1 x2 x3 : XReg) : storeRow kOff row [x0, x1, x2, x3] =
    stP row x0 0 ++ (stP row x1 1 ++ (stP row x2 2 ++ stP row x3 3)) := rfl

theorem kR_contains (buf : Addr) {d n : Nat} (h : d + n ≤ 512) : (kR buf).Contains (kA buf + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by lit_omega)

theorem st16_ok (x : XReg) {off : Nat} (ho : off + 16 ≤ 512) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hk : kR buf ∈ s.wr) :
    WP isa (.block [.vmovdquStore .l128 (at_ .rcx (608 + off)) x]) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        byte (s.lane x 0) (k - off) else s.mem (kA buf + BitVec.ofNat 64 k)) ∧
      Frame [kR buf] s.mem s'.mem ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : buf + BitVec.ofNat 64 (608 + off) = kA buf + BitVec.ofNat 64 off := by rw [add_ofNat]
  have c := kR_contains buf ho
  have o1 : InRegions s.wr (kA buf + BitVec.ofNat 64 off) 16 := ⟨kR buf, hk, c⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, ea_at, hrcx, e, State.store128_eq, o1,
    ite_true, Option.some.injEq, exists_eq_left', State.setMem_gpr, State.setMem_mem, State.setMem_rd,
    State.setMem_wr, State.xmm_lane]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c,
    fun r l => by simp only [State.setMem_lane], trivial, trivial, trivial⟩
  rw [byte_write16 _ _ _ ho hk]

theorem stP_ok {row i : Nat} (hrow : row < 4) (hi : i < 4) {x : XReg} (_hx13 : x ≠ .xmm13)
    {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hk : kR buf ∈ s.wr) :
    WP isa (.block (stP row x i)) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
        if (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row then byte (s.lane x (k / 64 / 4)) (k % 16)
        else s.mem (kA buf + BitVec.ofNat 64 k)) ∧
      Frame [kR buf] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [show stP row x i = [.vmovdquStore .l128 (at_ .rcx (608 + (64 * i + 16 * row))) x] ++
      ([.vop (.vextracti128 .xmm13 x 1)] ++
        [.vmovdquStore .l128 (at_ .rcx (608 + (64 * (i + 4) + 16 * row))) .xmm13]) by
    simp only [stP, Nat.add_assoc, List.cons_append, List.nil_append]]
  refine WP.block_append (WP.mono (st16_ok x (off := 64 * i + 16 * row) (by lit_omega) hrcx hk)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Option.some.injEq, exists_eq_left']
  refine WP.mono (st16_ok .xmm13 (off := 64 * (i + 4) + 16 * row) (buf := buf) (by lit_omega)
    (by rw [VOp.exec_gpr, g₁, hrcx]) (by rw [VOp.exec_wr, w₁]; exact hk))
    fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_
  simp only [VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, lane_vextracti128_1, ite_true,
    l₁ x 1] at m₃ f₃ l₃ g₃ r₃ w₃
  refine ⟨fun k hk => ?_, f₁.trans f₃, fun r l h13 => ?_, g₃.trans g₁, r₃.trans r₁, w₃.trans w₁⟩
  · rw [m₃ k hk, m₁ k hk]
    by_cases h2 : 64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16
    · rw [ite_eq_left h2, ite_eq_left (by omega), show k / 64 / 4 = 1 by omega,
        show k - (64 * (i + 4) + 16 * row) = k % 16 by omega]
    · rw [ite_eq_right h2]
      by_cases h1 : 64 * i + 16 * row ≤ k ∧ k < 64 * i + 16 * row + 16
      · rw [ite_eq_left h1, ite_eq_left (by omega), show k / 64 / 4 = 0 by omega,
          show k - (64 * i + 16 * row) = k % 16 by omega]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · rw [l₃ r l, ite_eq_right h13, l₁ r l]

theorem storeRow_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm13) (h1 : x1 ≠ .xmm13) (h2 : x2 ≠ .xmm13) (h3 : x3 ≠ .xmm13) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hk : kR buf ∈ s.wr) :
    WP isa (.block (storeRow kOff row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then byte (s.lane ([x0, x1, x2, x3].getD (k / 64 % 4) .xmm0) (k / 64 / 4)) (k % 16)
        else s.mem (kA buf + BitVec.ofNat 64 k)) ∧
      Frame [kR buf] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [storeRow_eq]
  refine WP.block_append (WP.mono (stP_ok hrow (i := 0) (by decide) h0 hrcx hk)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (stP_ok hrow (i := 1) (buf := buf) (by decide) h1 (by rw [g₁, hrcx]) (by rw [w₁]; exact hk))
    fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (stP_ok hrow (i := 2) (buf := buf) (by decide) h2 (by rw [g₂, g₁, hrcx])
    (by rw [w₂, w₁]; exact hk)) fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (stP_ok hrow (i := 3) (buf := buf) (by decide) h3 (by rw [g₃, g₂, g₁, hrcx]) (by rw [w₃, w₂, w₁]; exact hk))
    fun s₄ ⟨m₄, f₄, l₄, g₄, r₄, w₄⟩ => ?_
  have e1 : ∀ l, s₁.lane x1 l = s.lane x1 l := fun l => l₁ _ l h1
  have e2 : ∀ l, s₂.lane x2 l = s.lane x2 l := fun l => (l₂ _ l h2).trans (l₁ _ l h2)
  have e3 : ∀ l, s₃.lane x3 l = s.lane x3 l := fun l => ((l₃ _ l h3).trans (l₂ _ l h3)).trans (l₁ _ l h3)
  refine ⟨fun k hk => ?_, (((f₁.trans f₂).trans f₃).trans f₄), fun r l n13 => ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [m₄ k hk, m₃ k hk, m₂ k hk, m₁ k hk, e1, e2, e3]
    rcases (by omega_using [hk] : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
      k / 64 = 4 ∨ k / 64 = 5 ∨ k / 64 = 6 ∨ k / 64 = 7) with h | h | h | h | h | h | h | h <;>
      by_cases hr : k % 64 / 16 = row <;>
      simp only [h, hr, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, or_true,
        or_false, and_true, and_false, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
  · rw [l₄ r l n13, l₃ r l n13, l₂ r l n13, l₁ r l n13]

/-- `storeRow`'s effect: row `row` of the blocks `B 0, …, B 7` stored to
`kA buf`. -/
def StoreEff (buf : Addr) (row : Nat) (B : Nat → CState) (m m' : Mem) : Prop :=
  ∀ k < 512, m' (kA buf + BitVec.ofNat 64 k) =
    if k % 64 / 16 = row then (serialize (B (k / 64))).getD (k % 64) 0 else m (kA buf + BitVec.ofNat 64 k)

theorem storeRow_out {buf : Addr} {g : Reg → BitVec 64} {w : List Region} (hrcx : g .rcx = buf)
    (hk : kR buf ∈ w) {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) :
    OutOk (storeRow kOff) (StoreEff buf) [kR buf] g w row x0 x1 x2 x3 := by
  intro B s hB hg hws
  refine WP.mono (storeRow_ok hrow h0.2.1 h1.2.1 h2.2.1 h3.2.1 (by rw [hg]; exact hrcx) (by rw [hws]; exact hk))
    fun s₂ ⟨d₂, f₂, l₂, g₂, r₂, w₂⟩ => ⟨fun k hk => ?_, f₂, fun r l _ _ _ _ _ n13 _ _ => l₂ r l n13, g₂, r₂, w₂⟩
  rw [d₂ k hk]
  by_cases hr : k % 64 / 16 = row
  · rw [ite_eq_left hr, ite_eq_left hr, serialize_row _ hrow hr]
    obtain ⟨b0, b1, b2, b3⟩ := hB (k / 64 / 4) (by omega) hrow
    have e : 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 := by omega
    rcases (by omega : k / 64 % 4 = 0 ∨ k / 64 % 4 = 1 ∨ k / 64 % 4 = 2 ∨ k / 64 % 4 = 3) with q | q | q | q <;>
      rw [q] at e ⊢
    · rw [List.getD_cons_zero, b0, e]
    · rw [List.getD_cons_succ, List.getD_cons_zero, b1, e]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, b2, e]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, b3, e]
  · rw [ite_eq_right hr, ite_eq_right hr]

/-- The eight blocks' keystream (the rounds' result `vs` plus the input
state) stored to `kA buf`. -/
theorem finishK_ok {st buf : Addr} {vs : Nat → CState} {s : State} (hh : Holds buf false vs s)
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hwst : stR st ∈ s.wr) (hwb : bufR buf ∈ s.wr) (hk : kR buf ∈ s.wr) (hinc : Incs buf s.mem)
    (dsb : (stR st).Disjoint (bufR buf)) (dsk : (stR st).Disjoint (kR buf))
    (dbk : (bufR buf).Disjoint (kR buf)) :
    WP isa (.block (finishWith (storeRow kOff))) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
        (serialize (plus vs (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
      Frame [slotsR buf, kR buf] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hR : ∀ r ∈ [kR buf], (stR st).Disjoint r ∧ (slotsR buf).Disjoint r ∧ (incR buf).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨dsk, dbk.sub_left (slotsR_sub buf), dbk.sub_left (Offset.sub_base buf (by lit_omega))⟩
  refine WP.mono (finishWith_ok (out := storeRow kOff) hh hrdi hrcx hwst hwb hinc dsb hR
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide))
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide))
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide))
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide)))
    fun s' ⟨m₀, m₁, m₂, m₃, _, d₀, d₁, d₃, d₂, F, g, rd, wr⟩ => ⟨fun k hk => ?_, F, g, rd, wr⟩
  rw [d₂ k hk, d₃ k hk, d₁ k hk, d₀ k hk]
  rcases (by omega : k % 64 / 16 = 0 ∨ k % 64 / 16 = 1 ∨ k % 64 / 16 = 2 ∨ k % 64 / 16 = 3)
    with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
