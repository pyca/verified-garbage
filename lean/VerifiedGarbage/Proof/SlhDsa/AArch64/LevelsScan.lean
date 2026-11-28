module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: the scan, built in parallel with the groups' module.

/-!
# SLH-DSA on AArch64: `levels`, the scan of a height

As on x86-64 (`Proof/SlhDsa/X86_64/LevelsScan.lean`): one pass of
`scanBody`, node `i` of the height XORed into the authentication path's node
if its index in its tree, `⌊capBase / 2^z⌋ + i`, is the sibling's
(`scanBody_ok`), and the scan of a height (`scan_ok`), as `pick`
(`scan_pick`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Levels

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks VG.Proof.SlhDsa.AArch64.Wots4
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64

/-! ## The masked XOR -/

/-- What the masked XOR of `len` bytes from `nd` into `au` does. -/
structure XorPost (s s' : State) (b : Bool) (au nd : Addr) (len : Nat) : Prop where
  gpr : ∀ r, r ≠ .x12 → r ≠ .x14 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : ∀ q < len, s'.mem (au + BitVec.ofNat 64 q) =
    (if b then s.mem (nd + BitVec.ofNat 64 q) else 0) ^^^ s.mem (au + BitVec.ofNat 64 q)
  frame : Frame [⟨au, len⟩] s.mem s'.mem

theorem XorPost.trans {s s₁ s₂ : State} {b : Bool} {D Sr : Addr} {a c : Nat} (h₁ : XorPost s s₁ b D Sr a)
    (h₂ : XorPost s₁ s₂ b (D + BitVec.ofNat 64 a) (Sr + BitVec.ofNat 64 a) c)
    (hdis : Region.Disjoint ⟨D, a + c⟩ ⟨Sr, a + c⟩) (hac : a + c < 2 ^ 64) : XorPost s s₂ b D Sr (a + c) := by
  refine ⟨fun r h h' => by rw [h₂.gpr r h h', h₁.gpr r h h'], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], fun q hq => ?_, ?_⟩
  · by_cases cq : q < a
    · rw [h₂.frame.bytes (R := ⟨D, a⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint D (Nat.le_refl a) (by omega_using [hac])) (by show a ≤ 2 ^ 64; omega_using [hac]) cq,
        h₁.bytes q cq]
    · have e₁ : D + BitVec.ofNat 64 q = D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) := by
        rw [ofNat_add', Nat.add_sub_cancel' (by omega_using [cq])]
      have e₂ : Sr + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) = Sr + BitVec.ofNat 64 q := by
        rw [ofNat_add', Nat.add_sub_cancel' (by omega_using [cq])]
      have fs : s₁.mem (Sr + BitVec.ofNat 64 q) = s.mem (Sr + BitVec.ofNat 64 q) :=
        h₁.frame.bytes (R := ⟨Sr, a + c⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hdis.symm.sub_right (Region.sub_prefix (Nat.le_add_right a c))) (by show a + c ≤ 2 ^ 64; omega_using [hac]) hq
      have fd : s₁.mem (D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a)) =
          s.mem (D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a)) :=
        h₁.frame.bytes (R := ⟨D + BitVec.ofNat 64 a, c⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (Nat.le_refl a) (by omega_using [hac])) (by show c ≤ 2 ^ 64; omega_using [hac])
          (by show q - a < c; omega_using [hq, cq])
      rw [e₁, h₂.bytes _ (by omega_using [hq, cq]), e₂, fs, fd]
  · refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (Nat.le_add_right a c)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base D (Nat.le_refl _)⟩

/-- The masked XOR of word `w`, with the mask in `x11`, the node at `x10`
and the path's node at `x21`. -/
def xorWord (w : Nat) : List Instr :=
  [.ldr .x .x12 .x10 (8 * w), .logic .and .x .x12 .x12 .x11, .ldr .x .x14 .x21 (8 * w),
    .logic .eor .x .x14 .x14 .x12, .str .x .x14 .x21 (8 * w)]

theorem and_mask (v : BitVec 64) (b : Bool) :
    v &&& (if b then BitVec.allOnes 64 else 0) = if b then v else 0 := by
  cases b
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

section
variable {s : State}

theorem xor8_ok {b : Bool} (hm : s.gpr .x11 = if b then BitVec.allOnes 64 else 0) {w : Nat} (hw : 8 * w < 32768)
    (hnd : InRegions (s.rd ++ s.wr) (s.gpr .x10 + BitVec.ofNat 64 (8 * w)) 8)
    (hau : InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 (8 * w)) 8) :
    WP isa (.block (xorWord w)) s
      (fun s' => XorPost s s' b (s.gpr .x21 + BitVec.ofNat 64 (8 * w)) (s.gpr .x10 + BitVec.ofNat 64 (8 * w)) 8) := by
  have hau' : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (8 * w)) 8 := by
    obtain ⟨r, h, c⟩ := hau; exact ⟨r, List.mem_append_right _ h, c⟩
  simp only [xorWord]
  refine wp_ldr ⟨by omega_using [], hw⟩ rfl hnd fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  refine wp_ldr ⟨by omega_using [], hw⟩ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hau') fun s₃ u₃ => wp_eor fun s₄ u₄ => ?_
  refine wp_str ⟨by omega_using [], hw⟩ (by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hau) fun s₅ u₅ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hv : s₄.gpr .x14 = s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (8 * w)) 64 ^^^
      (if b then s.mem.readW (s.gpr .x10 + BitVec.ofNat 64 (8 * w)) 64 else 0) := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hm, and_mask, u₂.mem, u₁.mem]
  refine ⟨fun r h h' => by
      rw [u₅.gpr, u₄.other _ h', u₃.other _ h', u₂.other _ h, u₁.other _ h],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], fun q hq => ?_, ?_⟩
  · rw [u₅.mem, hm₄, writeW64_in _ _ _ hq, hv, BitVec.extractLsb'_xor, byte_readW64 _ _ hq, BitVec.xor_comm]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show ((0 : BitVec 64).extractLsb' (8 * q) 8) = 0 from BitVec.eq_of_toNat_eq (by simp)]
    · simp only [↓reduceIte]; rw [byte_readW64 _ _ hq]
  · rw [u₅.mem, hm₄]
    exact frame_writeW (w := 64) _ _ _ (by decide)

/-- The masked XOR of `W` words. -/
theorem xorWords_ok {b : Bool} (hm : s.gpr .x11 = if b then BitVec.allOnes 64 else 0) {W : Nat}
    (hf : 8 * W ≤ 32768)
    (hnd : InRegions (s.rd ++ s.wr) (s.gpr .x10) (8 * W)) (hau : InRegions s.wr (s.gpr .x21) (8 * W))
    (hdis : Region.Disjoint ⟨s.gpr .x21, 8 * W⟩ ⟨s.gpr .x10, 8 * W⟩) :
    WP isa (.block ((List.range W).flatMap xorWord)) s
      (fun s' => XorPost s s' b (s.gpr .x21) (s.gpr .x10) (8 * W)) := by
  refine WP.mono (wp_range_flatMap (P := fun j t => j ≤ W → XorPost s t b (s.gpr .x21) (s.gpr .x10) (8 * j))
    W (fun _ => ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩)
    fun j hj t ht => ?_) fun t h => h (Nat.le_refl _)
  have c := ht (by omega_using [hj])
  have h10 : t.gpr .x10 = s.gpr .x10 := c.gpr _ (by decide) (by decide)
  have h21 : t.gpr .x21 = s.gpr .x21 := c.gpr _ (by decide) (by decide)
  have off : ∀ {rs : List Region} {A : Addr}, InRegions rs A (8 * W) → InRegions rs (A + BitVec.ofNat 64 (8 * j)) 8 :=
    fun h => inRegions_off h (by omega_using [hj])
  refine WP.mono (xor8_ok (s := t) (b := b) (by rw [c.gpr _ (by decide) (by decide), hm]) (by omega_using [hf, hj])
      (by rw [h10, c.rd, c.wr]; exact off hnd) (by rw [h21, c.wr]; exact off hau)) fun t' c' _ => ?_
  rw [h10, h21] at c'
  have := XorPost.trans c c' (by
      rw [show 8 * j + 8 = 8 * (j + 1) by omega_using []]
      exact (hdis.sub_left (Region.sub_prefix (by omega_using [hj]))).sub_right (Region.sub_prefix (by omega_using [hj])))
    (by omega_using [hf, hj])
  rwa [show 8 * j + 8 = 8 * (j + 1) by omega_using []] at this

end

/-! ## One pass of the scan -/

/-- The value whose zero `scanBody`'s mask tests. -/
theorem scan_key {A V : Nat} {i : Nat} (hA : A < 2 ^ 32) (hV : V < 2 ^ 33) (hi : i < 2 ^ 32) :
    ((BitVec.ofNat 64 A + BitVec.ofNat 64 i) ^^^ BitVec.ofNat 64 V).toNat < 2 ^ 63 ∧
      (((BitVec.ofNat 64 A + BitVec.ofNat 64 i) ^^^ BitVec.ofNat 64 V) = 0 ↔ A + i = V) := by
  have e : (BitVec.ofNat 64 A + BitVec.ofNat 64 i).toNat = A + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := A) (by omega_using [hA]),
      Nat.mod_eq_of_lt (a := i) (by omega_using [hi]), Nat.mod_eq_of_lt (by omega_using [hA, hi])]
  have eV : (BitVec.ofNat 64 V).toNat = V := by rw [BitVec.toNat_ofNat]; omega_using [hV]
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_xor, e, eV]
    exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 34) (by omega_using [hi, hA]) (by omega_using [hV]))
      (Nat.pow_le_pow_right (by decide) (by decide))
  · show _ = 0#64 ↔ _
    rw [BitVec.xor_eq_zero_iff]
    exact ⟨fun h => by rw [← e, h, eV], fun h => BitVec.eq_of_toNat_eq (by rw [e, eV, h])⟩

theorem scanBody_eq (L : Layout) : Tree.scanBody L =
    ([.add .x .x11 .x26 .x24, .logic .eor .x .x11 .x11 .x13] : List Instr) ++ maskZero .x11 .x12 ++
      (List.range (L.n / 8)).flatMap xorWord ++
      ([.addImm .x .x10 .x10 L.n, .addImm .x .x24 .x24 1, .sub .x .x9 .x24 .x23] : List Instr) := rfl

/-- What the scan keeps of the registers. -/
abbrev SR : List Reg := [.x9, .x10, .x11, .x12, .x14, .x24]

/-- One pass of the scan, from node `i` of `c` at `ND + i·n` (`x10`), the path's
node at `AP` (`x21`), the sibling `V` in `x13`, and `⌊capBase / 2^z⌋ = A`
in `x26`. -/
theorem scanBody_ok {p : Params} (hz : Sz p) {ND AP : Addr} {i c A V : Nat} {t : State}
    (h10 : t.gpr .x10 = ND + BitVec.ofNat 64 (i * p.n)) (h21 : t.gpr .x21 = AP)
    (h23 : t.gpr .x23 = BitVec.ofNat 64 c) (h24 : t.gpr .x24 = BitVec.ofNat 64 i)
    (h26 : t.gpr .x26 = BitVec.ofNat 64 A) (h13 : t.gpr .x13 = BitVec.ofNat 64 V)
    (hic : i < c) (hc : c < 2 ^ 32) (hA : A < 2 ^ 32) (hV : V < 2 ^ 33)
    (hnd : InRegions (t.rd ++ t.wr) (ND + BitVec.ofNat 64 (i * p.n)) p.n)
    (hau : InRegions t.wr AP p.n)
    (hdis : Region.Disjoint ⟨AP, p.n⟩ ⟨ND + BitVec.ofNat 64 (i * p.n), p.n⟩) :
    WP isa (.block (Tree.scanBody ⟨p.n, p.len⟩)) t fun t' =>
      (∀ g ∉ SR, t'.gpr g = t.gpr g) ∧ t'.sp = t.sp ∧
      t'.gpr .x24 = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .x10 = ND + BitVec.ofNat 64 ((i + 1) * p.n) ∧
      t'.gpr .x9 = BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 c ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ j < p.n, t'.mem (AP + BitVec.ofNat 64 j) =
        (if A + i = V then t.mem (ND + BitVec.ofNat 64 (i * p.n) + BitVec.ofNat 64 j) else 0) ^^^
          t.mem (AP + BitVec.ofNat 64 j)) ∧
      Frame [⟨AP, p.n⟩] t.mem t'.mem := by
  have hn := hz.n32
  have e8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega_using [this]
  have hi32 : i < 2 ^ 32 := by omega_using [hic, hc]
  obtain ⟨hk63, hkey⟩ := scan_key hA hV hi32
  rw [scanBody_eq]
  simp only [maskZero, List.cons_append, List.append_assoc]
  refine wp_add fun s₁ u₁ => wp_eor fun s₂ u₂ => wp_subImm (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => wp_sub fun s₆ u₆ => ?_
  have hm₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg₆ : ∀ g, g ≠ .x11 → g ≠ .x12 → s₆.gpr g = t.gpr g := fun g h₁ h₂ => by
    rw [u₆.other _ h₁, u₅.other _ h₂, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₁]
  have hmask : s₆.gpr .x11 = if decide (A + i = V) then BitVec.allOnes 64 else 0 := by
    have a2 : s₂.gpr .x11 = (BitVec.ofNat 64 A + BitVec.ofNat 64 i) ^^^ BitVec.ofNat 64 V := by
      rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h26, h24, h13]
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, a2]
    refine (mask_zero hk63).trans ?_
    by_cases hc' : A + i = V
    · rw [ite_eq_left (hkey.mpr hc'), decide_eq_true hc']; rfl
    · rw [ite_eq_right (fun h => hc' (hkey.mp h)), decide_eq_false hc']; rfl
  rw [List.nil_append]
  refine WP.block_append (WP.mono (xorWords_ok (s := s₆) (b := decide (A + i = V)) (W := p.n / 8) hmask
    (by omega_using [e8, hn]) (by rw [hg₆ _ (by decide) (by decide), h10, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd,
      u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, e8]; exact hnd)
    (by rw [hg₆ _ (by decide) (by decide), h21, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, e8]; exact hau)
    (by rw [hg₆ _ (by decide) (by decide), hg₆ _ (by decide) (by decide), h21, h10, e8]; exact hdis))
    fun s₇ c₇ => ?_)
  rw [hg₆ _ (by decide) (by decide), hg₆ _ (by decide) (by decide), h21, h10, e8] at c₇
  refine wp_addImm (by omega_using [hn]) fun s₈ u₈ => wp_addImm (by decide) fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ =>
    WP.block_nil ?_
  have hx24 : s₉.gpr .x24 = BitVec.ofNat 64 (i + 1) := by
    rw [u₉.gpr, u₈.other _ (by decide), c₇.gpr _ (by decide) (by decide), hg₆ _ (by decide) (by decide), h24,
      ← BitVec.ofNat_add]
  refine ⟨fun g hg => ?_, by rw [u₁₀.sp, u₉.sp, u₈.sp, c₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
    by rw [u₁₀.other _ (by decide), hx24], ?_, ?_, by rw [u₁₀.rd, u₉.rd, u₈.rd, c₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₁₀.wr, u₉.wr, u₈.wr, c₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], fun j hj => ?_, ?_⟩
  · have n9 : g ≠ .x9 := fun e => hg (e ▸ by decide)
    have n10 : g ≠ .x10 := fun e => hg (e ▸ by decide)
    have n11 : g ≠ .x11 := fun e => hg (e ▸ by decide)
    have n12 : g ≠ .x12 := fun e => hg (e ▸ by decide)
    have n14 : g ≠ .x14 := fun e => hg (e ▸ by decide)
    have n24 : g ≠ .x24 := fun e => hg (e ▸ by decide)
    rw [u₁₀.other _ n9, u₉.other _ n24, u₈.other _ n10, c₇.gpr _ n12 n14, hg₆ _ n11 n12]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, c₇.gpr _ (by decide) (by decide),
      hg₆ _ (by decide) (by decide), h10, ofNat_add', Nat.succ_mul]
  · rw [u₁₀.gpr, hx24, u₉.other _ (by decide), u₈.other _ (by decide), c₇.gpr _ (by decide) (by decide),
      hg₆ _ (by decide) (by decide), h23]
  · rw [u₁₀.mem, u₉.mem, u₈.mem, c₇.bytes j (by omega_using [hj, e8]), hm₆]
    by_cases hc' : A + i = V
    · rw [decide_eq_true hc', ite_eq_left rfl, ite_eq_left hc']
    · rw [decide_eq_false hc', ite_eq_right (by decide), ite_eq_right hc']
  · rw [u₁₀.mem, u₉.mem, u₈.mem, ← hm₆]
    exact c₇.frame

/-! ## The scan of a height -/

theorem nt' {g : Reg} (hg : g ∉ SR) (r : Reg) (hr : r ∈ SR := by decide) : g ≠ r := fun e => hg (e ▸ hr)

/-- The bytes XORed into the path's node after `i` passes of the scan: byte
`j` of node `sib - first`, if it is among the first `i`. -/
def acc (m : Mem) (ND : Addr) (n first sib i j : Nat) : Byte :=
  if first ≤ sib ∧ sib < first + i then m (ND + BitVec.ofNat 64 ((sib - first) * n) + BitVec.ofNat 64 j) else 0

theorem acc_zero (m : Mem) (ND : Addr) (n first sib j : Nat) : acc m ND n first sib 0 j = 0 := by
  simp only [acc, Nat.add_zero]; exact ite_eq_right (fun h => absurd h.2 (by omega_using [h.1]))

theorem acc_succ (m : Mem) (ND : Addr) (n first sib i j : Nat) :
    (if first + i = sib then m (ND + BitVec.ofNat 64 (i * n) + BitVec.ofNat 64 j) else 0) ^^^ acc m ND n first sib i j =
      acc m ND n first sib (i + 1) j := by
  simp only [acc]
  by_cases h : first + i = sib
  · rw [ite_eq_left h, ite_eq_right (by omega_using [h]), ite_eq_left (by omega_using [h]),
      show sib - first = i by omega_using [h]]
    simp
  · rw [ite_eq_right h]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor]
    by_cases h' : first ≤ sib ∧ sib < first + i
    · rw [ite_eq_left h', ite_eq_left (by omega_using [h'])]
    · rw [ite_eq_right h', ite_eq_right (by omega_using [h, h'])]

theorem ofNat_xor1 {I : Nat} (hI : I < 2 ^ 32) : BitVec.ofNat 64 I ^^^ (1 : BitVec 16).setWidth 64 =
    BitVec.ofNat 64 (I ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show ((1 : BitVec 16).setWidth 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega_using [hI]), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 33)
      (by omega_using [hI]) (by decide)) (by decide))]

/-- The scan of a height (`scanInit`, then the loop of `scanBody`): the `c`
nodes at `ND` (`x20`), the path's node at `AP` (`x21`), `⌊idx / 2^z⌋ = I` in
`x25` and `⌊capBase / 2^z⌋ = A` in `x26`. Byte `j` of the path's node is
XORed with byte `j` of the node whose index in its tree, `A + i`, is the
sibling `I ⊕ 1`, if one is. -/
theorem scan_ok {p : Params} (hz : Sz p) {ND AP : Addr} {c I A : Nat} {t : State} {Q : State → Prop}
    (h20 : t.gpr .x20 = ND) (h21 : t.gpr .x21 = AP) (h23 : t.gpr .x23 = BitVec.ofNat 64 c)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 I) (h26 : t.gpr .x26 = BitVec.ofNat 64 A)
    (hc0 : 1 ≤ c) (hc : c < 2 ^ 32) (hI : I < 2 ^ 32) (hA : A < 2 ^ 32)
    (hnd : ∀ i < c, InRegions (t.rd ++ t.wr) (ND + BitVec.ofNat 64 (i * p.n)) p.n)
    (hau : InRegions t.wr AP p.n)
    (hdis : ∀ i < c, Region.Disjoint ⟨AP, p.n⟩ ⟨ND + BitVec.ofNat 64 (i * p.n), p.n⟩)
    (k : ∀ t', (∀ g ∉ SR, g ≠ .x13 → t'.gpr g = t.gpr g) → t'.sp = t.sp → t'.rd = t.rd → t'.wr = t.wr →
      (∀ j < p.n, t'.mem (AP + BitVec.ofNat 64 j) = acc t.mem ND p.n A (I ^^^ 1) c j ^^^ t.mem (AP + BitVec.ofNat 64 j)) →
      Frame [⟨AP, p.n⟩] t.mem t'.mem → Q t') :
    WP isa (.seq (.block Tree.scanInit) (.loop (.block (Tree.scanBody ⟨p.n, p.len⟩)) (.nonzero .x .x9))) t Q := by
  have hn := hz.n32
  have hV : I ^^^ 1 < 2 ^ 33 := Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 33) (by omega_using [hI]) (by decide))
    (by decide)
  simp only [Tree.scanInit, Thash4.mov]
  refine WP.seq (wp_movz fun s₁ u₁ => wp_eor fun s₂ u₂ => wp_movz fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    WP.block_nil ?_)
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = c - i ∧ i < c ∧
    (∀ g ∉ SR, g ≠ .x13 → s.gpr g = t.gpr g) ∧ s.gpr .x13 = BitVec.ofNat 64 (I ^^^ 1) ∧
    s.gpr .x24 = BitVec.ofNat 64 i ∧ s.gpr .x10 = ND + BitVec.ofNat 64 (i * p.n) ∧
    s.sp = t.sp ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
    (∀ j < p.n, s.mem (AP + BitVec.ofNat 64 j) = acc t.mem ND p.n A (I ^^^ 1) i j ^^^ t.mem (AP + BitVec.ofNat 64 j)) ∧
    Frame [⟨AP, p.n⟩] t.mem s.mem
  have hm₄ : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.loop (M := isa) Inv (fun m s hI' => ?_) c s₄ ⟨0, by omega_using [], hc0, fun g hg h13 => ?_, ?_, ?_, ?_,
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    fun j hj => by rw [acc_zero, hm₄]; simp, by rw [hm₄]; exact Frame.refl _ _⟩
  rotate_left
  · rw [u₄.other _ (nt' hg .x10), u₃.other _ (nt' hg .x24), u₂.other _ h13, u₁.other _ (nt' hg .x9)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h25, ofNat_xor1 hI]
  · rw [u₄.other _ (by decide), u₃.gpr]; rfl
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h20, add0, Nat.zero_mul, add0]
  obtain ⟨i, rfl, hic, hg, h13, h24, h10, hsp, hrd, hwr, hacc, hf⟩ := hI'
  have hnode : ∀ j < p.n, s.mem (ND + BitVec.ofNat 64 (i * p.n) + BitVec.ofNat 64 j) =
      t.mem (ND + BitVec.ofNat 64 (i * p.n) + BitVec.ofNat 64 j) :=
    fun j hj => hf.bytes (R := ⟨ND + BitVec.ofNat 64 (i * p.n), p.n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hdis i hic).symm) (by show p.n ≤ 2 ^ 64; omega_using [hn]) hj
  refine WP.mono (scanBody_ok hz (ND := ND) (AP := AP) (i := i) (c := c) (A := A) (V := I ^^^ 1) h10
    (by rw [hg _ (by decide) (by decide), h21]) (by rw [hg _ (by decide) (by decide), h23]) h24
    (by rw [hg _ (by decide) (by decide), h26]) h13 hic hc hA hV (by rw [hrd, hwr]; exact hnd i hic)
    (by rw [hwr]; exact hau) (hdis i hic)) fun s' ⟨g', sp', x24', x10', x9', rd', wr', by', f'⟩ => ?_
  have hI'' : ∀ j < p.n, s'.mem (AP + BitVec.ofNat 64 j) =
      acc t.mem ND p.n A (I ^^^ 1) (i + 1) j ^^^ t.mem (AP + BitVec.ofNat 64 j) := by
    intro j hj
    rw [by' j hj, hacc j hj, hnode j hj, ← BitVec.xor_assoc, acc_succ]
  have hf' : Frame [⟨AP, p.n⟩] t.mem s'.mem := hf.trans f'
  have hg' : ∀ g ∉ SR, g ≠ .x13 → s'.gpr g = t.gpr g := fun g h₁ h₂ => by rw [g' g h₁, hg g h₁ h₂]
  have ev := eval_nz x9' (by omega_using [hic, hc]) (by omega_using [hc])
  by_cases he : i + 1 = c
  · refine .inl ⟨by rw [ev, decide_eq_true he]; rfl, k s' hg' (by rw [sp', hsp]) (by rw [rd', hrd])
      (by rw [wr', hwr]) ?_ hf'⟩
    rw [← he]; exact hI''
  · refine .inr ⟨by rw [ev, decide_eq_false he]; rfl, c - (i + 1), by omega_using [hic, he], i + 1, rfl,
      by omega_using [hic, he], hg', by rw [g' _ (by decide), h13], x24', x10', by rw [sp', hsp], by rw [rd', hrd],
      by rw [wr', hwr], hI'', hf'⟩

theorem getD_xorB {a b : List Byte} {j : Nat} (ha : j < a.length) (hb : j < b.length) :
    (xorB a b).getD j 0 = a.getD j 0 ^^^ b.getD j 0 := by
  simp [xorB, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem length_pick {n : Nat} {L : List (List Byte)} (hL : ∀ i < L.length, (L.getD i []).length = n)
    (first idx z : Nat) : (pick n L first idx z).length = n := by
  simp only [pick]
  by_cases h : first ≤ idx / 2 ^ z ^^^ 1 ∧ idx / 2 ^ z ^^^ 1 < first + L.length
  · rw [ite_eq_left h]; exact hL _ (by omega_using [h])
  · rw [ite_eq_right h]; exact Proof.SlhDsa.length_toByte 0 n

theorem getD_bytesAt (m : Mem) (a : Addr) {L i : Nat} (hi : i < L) : (bytesAt m a L).getD i 0 = m (a + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem bytesAt_eq {m : Mem} {a : Addr} {L : Nat} {l : List Byte} (hl : l.length = L)
    (h : ∀ i < L, m (a + BitVec.ofNat 64 i) = l.getD i 0) : bytesAt m a L = l :=
  Proof.SlhDsa.ext_getD (by simp [bytesAt, hl]) fun i hi => by
    simp only [bytesAt, List.length_map, List.length_range] at hi
    rw [getD_bytesAt _ _ hi, h i hi]

/-- The scan's bytes are those of `pick`. -/
theorem scan_pick {m m' : Mem} {ND AP : Addr} {n first idx z c : Nat} {L : List (List Byte)}
    (hlen : L.length = c) (hL : ∀ i < c, bytesAt m (ND + BitVec.ofNat 64 (i * n)) n = L.getD i [])
    (h : ∀ j < n, m' (AP + BitVec.ofNat 64 j) =
      acc m ND n first (idx / 2 ^ z ^^^ 1) c j ^^^ m (AP + BitVec.ofNat 64 j)) :
    bytesAt m' AP n = xorB (bytesAt m AP n) (pick n L first idx z) := by
  have hl : ∀ i < L.length, (L.getD i []).length = n := fun i hi => by
    rw [← hL i (by omega_using [hi, hlen])]; simp [bytesAt]
  refine bytesAt_eq (by simp [xorB, bytesAt, length_pick hl]) fun j hj => ?_
  rw [h j hj, getD_xorB (by simp [bytesAt]; omega_using [hj]) (by rw [length_pick hl]; exact hj), getD_bytesAt _ _ hj,
    BitVec.xor_comm]
  congr 1
  simp only [pick, acc]
  by_cases hc : first ≤ idx / 2 ^ z ^^^ 1 ∧ idx / 2 ^ z ^^^ 1 < first + c
  · rw [ite_eq_left hc, ite_eq_left (by rw [hlen]; exact hc), ← hL _ (by omega_using [hc]), getD_bytesAt _ _ hj]
  · rw [ite_eq_right hc, ite_eq_right (by rw [hlen]; exact hc), Proof.SlhDsa.getD_toByte_zero]

end VG.Proof.SlhDsa.AArch64.Levels
