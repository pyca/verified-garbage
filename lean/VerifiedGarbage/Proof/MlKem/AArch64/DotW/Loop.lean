module

public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Compute
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Store
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64

Sixteen iterations of 16 coefficients (`loopW_ok`), each one `dot`'s blocks
`2c` and `2c + 1` (`stepW_ok`): `dotW out terms` writes `Σ F ∘ G` with 16-bit
coefficients to `bo + out` (`dotW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

theorem coeffAtW16_shift (m : Mem) (p : Addr) (j e : Nat) :
    coeffAtW 16 m (p + BitVec.ofNat 64 (2 * j)) e = coeffAtW 16 m p (j + e) := by
  simp only [coeffAtW]
  rw [ptr_add, show 2 * j + 16 / 8 * e = 16 / 8 * (j + e) by omega]

/-- What the loop needs, from the state before it: the polynomials of each term, the output
apart from them and from the table of `γ`. -/
structure LoopDataW (s₀ : State) (bf bg : Reg) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) : Prop where
  baseF : bf ∉ clob
  baseG : bg ∉ clob
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  boundF : ∀ fg ∈ terms, ∀ i < 256, F fg i < 3329
  boundG : ∀ fg ∈ terms, ∀ i < 256, G fg i < 3329
  valueF : ∀ fg ∈ terms, ∀ i < 256,
    (coeffAtW 16 s₀.mem (s₀.gpr bf + BitVec.ofNat 64 fg.1) i).toNat = F fg i
  valueG : ∀ fg ∈ terms, ∀ i < 256,
    (coeffAtW 16 s₀.mem (s₀.gpr bg + BitVec.ofNat 64 fg.2) i).toNat = G fg i
  apartF : ∀ fg ∈ terms, (⟨p, 512⟩ : Region).Disjoint ⟨s₀.gpr bf + BitVec.ofNat 64 fg.1, 512⟩
  apartG : ∀ fg ∈ terms, (⟨p, 512⟩ : Region).Disjoint ⟨s₀.gpr bg + BitVec.ofNat 64 fg.2, 512⟩
  readF : ∀ fg ∈ terms, ∀ o, o + 16 ≤ 512 →
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr bf + BitVec.ofNat 64 fg.1 + BitVec.ofNat 64 o) 16
  readG : ∀ fg ∈ terms, ∀ o, o + 16 ≤ 512 →
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr bg + BitVec.ofNat 64 fg.2 + BitVec.ofNat 64 o) 16
  write : ∀ o, o + 16 ≤ 512 → InRegions s₀.wr (p + BitVec.ofNat 64 o) 16
  tableApart : (⟨p, 512⟩ : Region).Disjoint ⟨t, 512⟩
  tableRead : ∀ c < 32, InRegions (s₀.rd ++ s₀.wr) (t + BitVec.ofNat 64 (16 * c)) 16
  tableValue : ∀ c < 32, Lanes (s₀.mem.read (t + BitVec.ofNat 64 (16 * c)) 16) (blockGamma Γ c)
  tableBound : ∀ i < 128, Γ i < 3329

/-- After `c` iterations. -/
structure LoopInvW (s₀ : State) (p t : Addr) (O : Nat → BitVec 16) (c : Nat) (s : State) : Prop where
  keep : Keep clob s₀ s
  frame : Frame [⟨p, 512⟩] s₀.mem s.mem
  constants : VConsts s
  x0 : s.gpr .x0 = p + BitVec.ofNat 64 (2 * (16 * c))
  x3 : s.gpr .x3 = t + BitVec.ofNat 64 (32 * c)
  x12 : s.gpr .x12 = BitVec.ofNat 64 (32 * c)
  x11 : (s.gpr .x11).toNat = 16 - c
  out : CoeffsInW s.mem p (· < 16 * c) O (fun i => coeffAtW 16 s₀.mem p i)

/-- The coefficients of the result, as 16-bit values. -/
def resultW (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) (j : Nat) :
    BitVec 16 :=
  BitVec.ofNat 16 (result terms F G Γ j).toNat

/-- A 16-bit coefficient of a polynomial apart from the frame. -/
theorem coeffAtW16_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {q : Addr}
    (hd : ∀ r ∈ rs, (⟨q, 512⟩ : Region).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAtW 16 m' q i = coeffAtW 16 m q i :=
  hf.readW (r := ⟨q, 512⟩) (contains_off (show 2 * i + 16 / 8 ≤ 512 by omega) (by decide)) hd (by decide)

theorem loop_inputW {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {O : Nat → BitVec 16} {c : Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (hc : c < 16) (h : LoopInvW s₀ p t O c s)
    {fg : Nat × Nat} (hf : fg ∈ terms) :
    TermInputW s bf bg fg (blockValues F (2 * c) fg) (blockValues G (2 * c) fg) := by
  have addr (b : Reg) (hb : b ∉ clob) (off : Nat) : s.gpr b + BitVec.ofNat 64 off + s.gpr .x12 =
      s₀.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (2 * (16 * c)) := by
    rw [h.keep.get b hb, h.x12, show 32 * c = 2 * (16 * c) by omega]
  refine ⟨hd.baseF, hd.baseG, hd.offF fg hf, hd.offG fg hf, fun e he => hd.boundF fg hf _ (by omega),
    fun e he => hd.boundG fg hf _ (by omega), fun e he => ?_, fun e he => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [addr bf hd.baseF, coeffAtW16_shift, coeffAtW16_frame h.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.apartF fg hf).symm) (by omega), hd.valueF fg hf _ (by omega)]
    simp only [blockValues]; congr 1; omega
  · rw [addr bg hd.baseG, coeffAtW16_shift, coeffAtW16_frame h.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.apartG fg hf).symm) (by omega), hd.valueG fg hf _ (by omega)]
    simp only [blockValues]; congr 1; omega
  · rw [h.keep.rd, h.keep.wr, addr bf hd.baseF, ptr_add]
    exact hd.readF fg hf _ (by omega)
  · rw [h.keep.rd, h.keep.wr, addr bg hd.baseG, ptr_add]
    exact hd.readG fg hf _ (by omega)

theorem loop_gammaW {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {O : Nat → BitVec 16} {c : Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (hc : c < 16) (h : LoopInvW s₀ p t O c s) {i : Nat} (hi : i < 2) :
    Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * i)) 16) (blockGamma Γ (2 * c + i)) := by
  rw [h.x3, ptr_add, h.frame.read (r := ⟨t, 512⟩) (contains_off (by omega) (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.tableApart.symm) (by decide),
    show 32 * c + 16 * i = 16 * (2 * c + i) by omega]
  exact hd.tableValue _ (by omega)

theorem upper_block (F : (Nat × Nat) → Nat → Nat) (c : Nat) :
    (fun fg => upper (blockValues F (2 * c) fg)) = blockValues F (2 * c + 1) := by
  funext fg i
  simp only [upper, blockValues]
  congr 1; omega

/-- A 16-bit result coefficient, from `dot`'s block and its pairs. -/
theorem resultW_toNat (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (c : Nat) {e : Nat} (he : e < 8) :
    (resultW terms F G Γ (8 * c + e)).toNat =
      if e % 2 = 0 then evenResult terms (blockValues F c) (blockValues G c) (blockGamma Γ c) (e / 2)
      else oddResult terms (blockValues F c) (blockValues G c) (e / 2) := by
  rw [resultW, result_block terms F G Γ c he, interleave, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split
  · simp only [evenResult]; omega
  · simp only [oddResult]; omega

theorem bodyW_partition (bf bg : Reg) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.DotW.bodyW bf bg terms =
      computeW bf bg terms ++ Impl.MlKem.AArch64.DotW.storeW ++ Impl.MlKem.AArch64.DotW.bumpW := by
  simp only [Impl.MlKem.AArch64.DotW.bodyW, computeW, List.append_assoc]

theorem bumpW_ok (s : State) : WP isa (.block Impl.MlKem.AArch64.DotW.bumpW) s fun s' =>
    Only [.x0, .x3, .x12, .x11] s s' ∧ s'.v = s.v ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 32 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 := by
  refine WP.mono (WP.keepV (Q := fun s' => Only [.x0, .x3, .x12, .x11] s s' ∧
    s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32 ∧
    s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 32 ∧
    s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32 ∧
    s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1) (by decide) ?_) ?_
  · refine wp_addImm (by decide) fun s₁ h₁ e₁ => wp_addImm (by decide) fun s₂ h₂ e₂ =>
      wp_addImm (by decide) fun s₃ h₃ e₃ => wp_subImm (by decide) fun s₄ h₄ e₄ => wp_nil ?_
    exact ⟨(((h₁.trans h₂).trans h₃).trans h₄).mono,
      by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁],
      by rw [h₄.get .x3, h₃.get .x3, e₂, h₁.get .x3],
      by rw [h₄.get .x12, e₃, h₂.get .x12, h₁.get .x12],
      by rw [e₄, h₃.get .x11, h₂.get .x11, h₁.get .x11]⟩
  · intro s' h; exact ⟨h.1.1, h.2, h.1.2⟩

theorem stepW_ok {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {c : Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (hc : c < 16)
    (h : LoopInvW s₀ p t (resultW terms F G Γ) c s) :
    WP isa (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) s fun s' =>
      LoopInvW s₀ p t (resultW terms F G Γ) (c + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ c + 1 ≠ 16) := by
  rw [bodyW_partition, List.append_assoc, WP.block_append_iff]
  refine WP.mono (computeW_ok terms (Γ := blockGamma Γ (2 * c)) (Γ' := blockGamma Γ (2 * c + 1))
    h.constants hd.count (fun _ hf => loop_inputW hd hc h hf)
    (fun i hi => by
      rw [h.keep.rd, h.keep.wr, h.x3, ptr_add, show 32 * c + 16 * i = 16 * (2 * c + i) by omega]
      exact hd.tableRead _ (by omega))
    (by simpa only [Nat.mul_zero, Nat.add_zero] using loop_gammaW hd hc h (i := 0) (by decide))
    (by simpa only [Nat.mul_one] using loop_gammaW hd hc h (i := 1) (by decide))
    (fun e he => show Γ _ < 3329 from hd.tableBound _ (by omega))
    (fun e he => show Γ _ < 3329 from hd.tableBound _ (by omega))) fun s₁ ⟨k₁, c₁, l21, l23, l25, l27⟩ => ?_
  rw [upper_block, upper_block] at l25 l27
  rw [WP.block_append_iff]
  refine WP.mono (storeW_ok (p := p) (j := 16 * c) (O := resultW terms F G Γ)
    (old := fun i => coeffAtW 16 s₀.mem p i) (by rw [k₁.get .x0]; exact h.x0) (by omega)
    (fun i hi => by rw [k₁.wr, h.keep.wr]; exact hd.write _ (by omega)) c₁ l21 l23 l25 l27
    (fun e he => Nat.mod_lt _ (by decide)) (fun e he => Nat.mod_lt _ (by decide))
    (fun e he => Nat.mod_lt _ (by decide)) (fun e he => Nat.mod_lt _ (by decide))
    (by rw [k₁.mem]; exact h.out) fun e he => ?_) fun s₂ ⟨k₂, c₂, f₂, o₂⟩ => ?_
  · unfold outW
    by_cases c8 : e < 8
    · rw [ite_eq_left c8, show 16 * c + e = 8 * (2 * c) + e by omega, resultW_toNat _ _ _ _ _ c8]
    · rw [ite_eq_right c8, show 16 * c + e = 8 * (2 * c + 1) + (e - 8) by omega,
        resultW_toNat _ _ _ _ _ (by omega), show (e - 8) % 2 = e % 2 by omega]
  refine WP.mono (bumpW_ok s₂) fun s₃ ⟨k₃, v₃, e0, e3, e12, e11⟩ => ?_
  have counter : (s₃.gpr .x11).toNat = 16 - (c + 1) := by
    rw [e11, k₂.get .x11, k₁.get .x11, toNat_sub_n (by rw [h.x11]; simp only [BitVec.toNat_ofNat]; omega), h.x11]
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨⟨((h.keep.trans ((k₁.keep.trans k₂).trans k₃.keep)).mono), h.frame.trans ?_,
    ⟨by rw [v₃]; exact c₂.q, by rw [v₃]; exact c₂.m⟩, ?_, ?_, ?_, counter, ?_⟩, by rw [counter]; omega⟩
  · rw [k₃.mem, ← k₁.mem]; exact f₂
  · rw [e0, k₂.get .x0, k₁.get .x0, h.x0, ptr_add, show 2 * (16 * c) + 32 = 2 * (16 * (c + 1)) by omega]
  · rw [e3, k₂.get .x3, k₁.get .x3, h.x3, ptr_add, show 32 * c + 32 = 32 * (c + 1) by omega]
  · rw [e12, k₂.get .x12, k₁.get .x12, h.x12, ← BitVec.ofNat_add, show 32 * c + 32 = 32 * (c + 1) by omega]
  · rw [k₃.mem, show 16 * (c + 1) = 16 * c + 16 by omega]; exact o₂

theorem loopW_ok {s₀ s : State} {bf bg : Reg} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat}
    (hd : LoopDataW s₀ bf bg p t terms F G Γ) (h : LoopInvW s₀ p t (resultW terms F G Γ) 0 s) :
    WP isa (.loop (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) (.nonzero .x .x11)) s
      (LoopInvW s₀ p t (resultW terms F G Γ) 16) :=
  count_loop (by decide) (LoopInvW s₀ p t (resultW terms F G Γ)) (fun _ hc _ hi => stepW_ok hd hc hi) h

end VG.Proof.MlKem.AArch64.DotW
