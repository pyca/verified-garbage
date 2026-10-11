import VerifiedGarbage.Proof.Modes.AArch64.Copy

/-!
# Unchaining CBC blocks on AArch64

`unchainBlocks_wp`: the loop `unchainBlocks` turns `nb ≥ 1` decrypted
blocks of `L = 8 bw` bytes at `T` (the core's buffer, in `x14`) and their
ciphertext blocks at `A` (the data, in `x15`) into the plaintext blocks:
block `j` at `A` becomes the decrypted block `j` XORed with the chaining
value (the `L` bytes at `H`) for `j = 0`, and with ciphertext block `j - 1`
otherwise; the chaining value becomes the last ciphertext block. Each block
is a XOR and two copies (`xorN_wp`, `copyN_wp`).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb)

variable {c : Core}

/-- Unchaining, after `j` of `nb` blocks: the decryptions at `T`, the
ciphertexts at `A`, the chaining value at `H`. -/
structure UInv (c : Core) (T A H : Addr) (nb : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  out : ∀ t < 8 * c.bw * j, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (T + BitVec.ofNat 64 t) ^^^
    (if t < 8 * c.bw then s₀.mem (H + BitVec.ofNat 64 t) else s₀.mem (A + BitVec.ofNat 64 (t - 8 * c.bw)))
  rest : ∀ t, 8 * c.bw * j ≤ t → t < 8 * c.bw * nb → s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  bufRest : ∀ t, 8 * c.bw * j ≤ t → t < 8 * c.bw * nb →
    s.mem (T + BitVec.ofNat 64 t) = s₀.mem (T + BitVec.ofNat 64 t)
  chain : ∀ u < 8 * c.bw, s.mem (H + BitVec.ofNat 64 u) =
    if j = 0 then s₀.mem (H + BitVec.ofNat 64 u) else s₀.mem (A + BitVec.ofNat 64 (8 * c.bw * (j - 1) + u))
  frame : Frame [⟨T, 8 * c.bw * nb⟩, ⟨A, 8 * c.bw * nb⟩, ⟨H, 8 * c.bw⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ .x8 → r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem unchainBlocks_wp {B T A H : Addr} {nb : Nat} {s₀ : State} (hbw : 0 < c.bw) (hL : 8 * c.bw < 4096)
    (hH8 : 8 * c.hiSlot + 8 * c.bw ≤ 32768)    (hn : 0 < nb) (hfit : 8 * c.bw * nb < 2 ^ 63) (hB : s₀.gpr sb = B) (hH : B + BitVec.ofNat 64 (8 * c.hiSlot) = H)
    (inT : ∀ t < c.bw * nb, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (inA : ∀ t < c.bw * nb, InRegions s₀.wr (A + BitVec.ofNat 64 (8 * t)) 8)
    (inH : ∀ w < c.bw, InRegions s₀.wr (H + BitVec.ofNat 64 (8 * w)) 8)
    (dTA : Region.Disjoint ⟨T, 8 * c.bw * nb⟩ ⟨A, 8 * c.bw * nb⟩)
    (dTH : Region.Disjoint ⟨T, 8 * c.bw * nb⟩ ⟨H, 8 * c.bw⟩) (dAH : Region.Disjoint ⟨A, 8 * c.bw * nb⟩ ⟨H, 8 * c.bw⟩)
    (ha : s₀.gpr .x14 = T) (hb : s₀.gpr .x15 = A) (hc : s₀.gpr .x17 = BitVec.ofNat 64 nb) :
    WP isa c.unchainBlocks s₀ fun s => UInv c T A H nb s₀ nb s ∧ s.gpr .x15 = A + BitVec.ofNat 64 (8 * c.bw * nb) := by
  have hn64 : nb ≤ 8 * c.bw * nb := Nat.le_mul_of_pos_left nb (by omega)
  have hLn : 8 * c.bw ≤ 8 * c.bw * nb := Nat.le_mul_of_pos_right _ hn
  unfold Core.unchainBlocks
  refine WP.mono (blockLoop_wp (c := c) _ (UInv c T A H nb s₀) hL hn (by omega)
    (fun j s s' h hm hrd hwr hg => ⟨fun t ht => by rw [hm]; exact h.out t ht,
      fun t h1 h2 => by rw [hm]; exact h.rest t h1 h2, fun t h1 h2 => by rw [hm]; exact h.bufRest t h1 h2,
      fun u hu => by rw [hm]; exact h.chain u hu, by rw [hm]; exact h.frame,
      fun r h1 h2 h3 h4 h5 => by rw [hg r h1 h2 h3, h.regs r h1 h2 h3 h4 h5], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩)
    (fun j hj s hi hax hbx => ?_)
    ⟨fun t ht => by omega, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => by rw [ite_eq_left rfl], Frame.refl _ _,
      fun _ _ _ _ _ _ => rfl, rfl, rfl⟩ ha hb hc) fun _ h => ⟨h.1, h.2.2⟩
  have hlt := idx_lt (L := 8 * c.bw) hj
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * nb := fun w hw' => by have := idx_lt (L := c.bw) hj; omega
  let Tj := T + BitVec.ofNat 64 (8 * c.bw * j)
  let Aj := A + BitVec.ofNat 64 (8 * c.bw * j)
  have subT : Region.Sub ⟨Tj, 8 * c.bw⟩ ⟨T, 8 * c.bw * nb⟩ := VG.Offset.sub_base T (by omega)
  have subA : Region.Sub ⟨Aj, 8 * c.bw⟩ ⟨A, 8 * c.bw * nb⟩ := VG.Offset.sub_base A (by omega)
  have wT : ∀ w < c.bw, InRegions s.wr (Tj + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' => by
    rw [hi.wr, addr_add, hw w]; exact inT _ (hbj w hw')
  have wA : ∀ w < c.bw, InRegions s.wr (Aj + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' => by
    rw [hi.wr, addr_add, hw w]; exact inA _ (hbj w hw')
  have wH : ∀ w < c.bw, InRegions s.wr (H + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' => by
    rw [hi.wr]; exact inH w hw'
  have base : s.gpr sb = B := by rw [hi.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), hB]
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  have dTjH : Region.Disjoint ⟨Tj, 8 * c.bw⟩ ⟨H, 8 * c.bw⟩ := dTH.sub_left subT
  have dHAj : Region.Disjoint ⟨H, 8 * c.bw⟩ ⟨Aj, 8 * c.bw⟩ := dAH.symm.sub_right subA
  have dAjTj : Region.Disjoint ⟨Aj, 8 * c.bw⟩ ⟨Tj, 8 * c.bw⟩ := (dTA.symm.sub_left subA).sub_right subT
  refine WP.block_append (WP.block_append (WP.mono (xorN_wp (k := c.bw) (P := Tj) (Q := H) (u := .x9)
    ⟨by rw [hax, p0], by rw [base, hH], by decide, by decide, by decide, by decide, by decide, by omega,
      by omega, by omega, wT, fun w hw' => inRd (wH w hw'), dTjH, by omega⟩ (by decide)) fun s₁ h₁ => ?_))
  have base₁ : s₁.gpr sb = B := by rw [h₁.regs _ (by decide) (by decide), base]
  have ax₁ : s₁.gpr .x14 = Tj := by rw [h₁.regs _ (by decide) (by decide), hax]
  have bx₁ : s₁.gpr .x15 = Aj := by rw [h₁.regs _ (by decide) (by decide), hbx]
  refine WP.mono (copyN_wp (k := c.bw) (P := H) (Q := Aj) (u := .x8)
    ⟨by rw [base₁, hH], by rw [bx₁, p0], by decide, by decide, by decide, by decide, by omega, by decide,
      by omega, by omega, fun w hw' => by rw [h₁.wr]; exact wH w hw',
      fun w hw' => by rw [h₁.rd, h₁.wr]; exact inRd (wA w hw'), dHAj, by omega⟩) fun s₂ h₂ => ?_
  have ax₂ : s₂.gpr .x14 = Tj := by rw [h₂.regs _ (by decide) (by decide), ax₁]
  have bx₂ : s₂.gpr .x15 = Aj := by rw [h₂.regs _ (by decide) (by decide), bx₁]
  refine WP.mono (copyN_wp (k := c.bw) (P := Aj) (Q := Tj) (u := .x8)
    ⟨by rw [bx₂, p0], by rw [ax₂, p0], by decide, by decide, by decide, by decide, by decide, by decide,
      by omega, by omega, fun w hw' => by rw [h₂.wr, h₁.wr]; exact wA w hw',
      fun w hw' => by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact inRd (wT w hw'), dAjTj, by omega⟩) fun s₃ h₃ => ?_
  -- Where each step leaves the bytes of the three regions.
  have hN : 8 * c.bw * nb ≤ 2 ^ 64 := by omega
  have dHT : Region.Disjoint ⟨H, 8 * c.bw⟩ ⟨T, 8 * c.bw * nb⟩ := dTH.symm
  have dHA : Region.Disjoint ⟨H, 8 * c.bw⟩ ⟨A, 8 * c.bw * nb⟩ := dAH.symm
  have A₁ : ∀ t < 8 * c.bw * nb, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [h₁.mem]; exact over_sep (dTA.sub_left subT) ht hN
  have A₂ : ∀ t < 8 * c.bw * nb, s₂.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [h₂.mem, over_sep dHA ht hN, A₁ t ht]
  have T₂ : ∀ t < 8 * c.bw * nb, s₂.mem (T + BitVec.ofNat 64 t) = if 8 * c.bw * j ≤ t ∧ t < 8 * c.bw * j + 8 * c.bw
      then s.mem (T + BitVec.ofNat 64 t) ^^^ s.mem (H + BitVec.ofNat 64 (t - 8 * c.bw * j))
      else s.mem (T + BitVec.ofNat 64 t) := fun t ht => by
    rw [h₂.mem, over_sep dHT ht hN, h₁.mem, over_off _ _ _ (by omega) (by omega) (by omega)]
    split
    · rename_i h; rw [addr_add, Nat.add_sub_cancel' h.1]
    · rfl
  have T₃ : ∀ t < 8 * c.bw * nb, s₃.mem (T + BitVec.ofNat 64 t) = s₂.mem (T + BitVec.ofNat 64 t) := fun t ht => by
    rw [h₃.mem]; exact over_sep (dTA.symm.sub_left subA) ht hN
  have A₃ : ∀ t < 8 * c.bw * nb, s₃.mem (A + BitVec.ofNat 64 t) = if 8 * c.bw * j ≤ t ∧ t < 8 * c.bw * j + 8 * c.bw
      then s₂.mem (T + BitVec.ofNat 64 t) else s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [h₃.mem, over_off _ _ _ (by omega) (by omega) (by omega)]
    split
    · rename_i h; rw [addr_add, Nat.add_sub_cancel' h.1]
    · exact A₂ t ht
  have rax₃ : s₃.gpr .x14 = s.gpr .x14 := by rw [h₃.regs _ (by decide) (by decide), h₂.regs _ (by decide) (by decide), h₁.regs _ (by decide) (by decide)]
  have rbx₃ : s₃.gpr .x15 = s.gpr .x15 := by rw [h₃.regs _ (by decide) (by decide), h₂.regs _ (by decide) (by decide), h₁.regs _ (by decide) (by decide)]
  have rcx₃ : s₃.gpr .x17 = s.gpr .x17 := by rw [h₃.regs _ (by decide) (by decide), h₂.regs _ (by decide) (by decide), h₁.regs _ (by decide) (by decide)]
  refine ⟨⟨fun t ht => ?_, fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun u hu => ?_, hi.frame.trans fun x hx => ?_,
    fun r h1 h2 h3 h4 h5 => by rw [h₃.regs r h4 h4, h₂.regs r h4 h4, h₁.regs r h4 h5, hi.regs r h1 h2 h3 h4 h5],
    by rw [h₃.rd, h₂.rd, h₁.rd, hi.rd], by rw [h₃.wr, h₂.wr, h₁.wr, hi.wr]⟩, rax₃, rbx₃, rcx₃⟩
  · rw [A₃ t (by omega)]
    split
    · rename_i h
      rw [T₂ t (by omega), ite_eq_left h, hi.bufRest t h.1 (by omega), hi.chain _ (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.mul_zero, Nat.sub_zero]
      · have : 8 * c.bw * (j - 1) = 8 * c.bw * j - 8 * c.bw := Nat.mul_sub_one _ _
        have : 8 * c.bw ≤ 8 * c.bw * j := Nat.le_mul_of_pos_right _ (by omega)
        rw [ite_eq_right hj0, ite_eq_right (by omega),
          show 8 * c.bw * (j - 1) + (t - 8 * c.bw * j) = t - 8 * c.bw by omega]
    · exact hi.out t (by omega)
  · rw [A₃ t h2, ite_eq_right (by omega)]; exact hi.rest t (by omega) h2
  · rw [T₃ t h2, T₂ t h2, ite_eq_right (by omega)]; exact hi.bufRest t (by omega) h2
  · rw [h₃.mem, over_sep dHAj.symm hu (by omega), h₂.mem, over_at hu (by omega), addr_add, A₁ _ (by omega),
      hi.rest _ (by omega) (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
  · have hx' : ∀ {R : Region}, R ∈ [(⟨T, 8 * c.bw * nb⟩ : Region), ⟨A, 8 * c.bw * nb⟩, ⟨H, 8 * c.bw⟩] →
        ∀ {P : Addr}, Region.Sub ⟨P, 8 * c.bw⟩ R → ¬ (x - P).toNat < 8 * c.bw := fun hR P hs h =>
      hx _ hR (hs x (by simp only [Region.Contains]; omega))
    rw [h₃.mem, over_out (hx' (by simp) subA), h₂.mem, over_out (hx' (by simp) (fun _ h => h)), h₁.mem,
      over_out (hx' (by simp) subT)]

end VG.Proof.Modes.AArch64
