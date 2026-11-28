module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, the scan of a height

One pass of `scanBody`: node `i` of the height XORed into the
authentication path's node if its index in its tree, `⌊capBase / 2^z⌋ + i`,
is the sibling's (`scanBody_ok`).
-/

-- separate module: the scan, built in parallel with the chain of the groups' modules.

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Tree
open VG.Proof.Sha3.X86_64 (Upd ea_at wp_mov wp_movm wp_xorm wp_xori wp_subi wp_mov32i wp_addi)

/-- The value whose zero `scanBody`'s mask tests. -/
theorem scan_key {V5 V3 : BitVec 64} {z i : Nat} (hV5 : V5.toNat < 2 ^ 32) (hV3 : V3.toNat < 2 ^ 33)
    (hi : i < 2 ^ 32) :
    ((V5 >>> z + BitVec.ofNat 64 i) ^^^ V3).toNat < 2 ^ 63 ∧
      (((V5 >>> z + BitVec.ofNat 64 i) ^^^ V3) = 0 ↔ V5.toNat / 2 ^ z + i = V3.toNat) := by
  have e : (V5 >>> z + BitVec.ofNat 64 i).toNat = V5.toNat / 2 ^ z + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    have : V5.toNat / 2 ^ z ≤ V5.toNat := Nat.div_le_self _ _
    rw [Nat.mod_eq_of_lt (a := i) (by omega_using [hi]), Nat.mod_eq_of_lt (by omega_using [hi, this, hV5])]
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_xor, e]
    have : V5.toNat / 2 ^ z ≤ V5.toNat := Nat.div_le_self _ _
    exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 34) (by omega_using [hi, this, hV5]) (by omega_using [hV3]))
      (Nat.pow_le_pow_right (by decide) (by decide))
  · show _ = 0#64 ↔ _
    rw [BitVec.xor_eq_zero_iff, ← e]
    exact ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩

/-- One pass of the scan, from node `i` of `c` at `ND` (`r12`), the path's
node at `AP` (`r13`), the height `z` in `r14`, the sibling `V3` in variable
3 and `capBase` `V5` in variable 5. -/
theorem scanBody_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S ND AP : Addr} {z i c : Nat}
    {V3 V5 : BitVec 64} {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = ND) (h13 : t.gpr .r13 = AP)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 z) (h15 : t.gpr .r15 = BitVec.ofNat 64 c)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 i) (hz : z < 64) (hic : i < c) (hc : c < 2 ^ 32)
    (h3 : t.mem.readW (at' S (Layout.oVar 4 3)) 64 = V3) (h5 : t.mem.readW (at' S (Layout.oVar 4 5)) 64 = V5)
    (hV3 : V3.toNat < 2 ^ 33) (hV5 : V5.toNat < 2 ^ 32)
    (hv3 : InRegions (t.rd ++ t.wr) (at' S (Layout.oVar 4 3)) 8)
    (hv5 : InRegions (t.rd ++ t.wr) (at' S (Layout.oVar 4 5)) 8)
    (hnd : ∀ w < p.n / 8, InRegions (t.rd ++ t.wr) (ND + BitVec.ofNat 64 (i * p.n) + BitVec.ofNat 64 (8 * w)) 8)
    (hau : ∀ w < p.n / 8, InRegions t.wr (AP + BitVec.ofNat 64 (8 * w)) 8)
    (hdis : Region.Disjoint ⟨ND + BitVec.ofNat 64 (i * p.n), p.n⟩ ⟨AP, p.n⟩) :
    WP isa (.block (scanBody ⟨p.n, p.len⟩)) t fun t' =>
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → g ≠ .rdx → g ≠ .rbp → t'.gpr g = t.gpr g) ∧
      t'.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧ isa.eval .ne t' = some (!decide (i + 1 = c)) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ j < p.n, t'.mem (AP + BitVec.ofNat 64 j) =
        (if V5.toNat / 2 ^ z + i = V3.toNat then t.mem (ND + BitVec.ofNat 64 (i * p.n) + BitVec.ofNat 64 j) else 0) ^^^
          t.mem (AP + BitVec.ofNat 64 j)) ∧
      Frame [⟨AP, p.n⟩] t.mem t'.mem := by
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hi32 : i < 2 ^ 32 := by omega_using [hic, hc]
  obtain ⟨hk63, hkey⟩ := scan_key (z := z) hV5 hV3 hi32
  simp only [scanBody, var, List.cons_append, List.append_assoc]
  refine wp_movm (by rw [ea_at, hbx]) hv5 fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_shrcl fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_xorm (a := at' S (Layout.oVar 4 3)) ?_ ?_ fun s₅ u₅ => wp_subi fun s₆ u₆ _ =>
    wp_shr (by decide) (by decide) fun s₇ u₇ => wp_mov32i fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_mov fun s₁₀ u₁₀ => mulN_ok hn (by decide) fun s₁₁ g₁₁ o₁₁ m₁₁ r₁₁ w₁₁ => wp_add fun s₁₂ u₁₂ => ?_
  · rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx]
  · rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hv3
  -- the registers the rest reads
  have hm : s₁₂.mem = t.mem := by
    rw [u₁₂.mem, m₁₁, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₁₂.rd = t.rd := by
    rw [u₁₂.rd, r₁₁, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₁₂.wr = t.wr := by
    rw [u₁₂.wr, w₁₁, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hkeep : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → g ≠ .rdx → s₁₂.gpr g = t.gpr g := fun g h1 h2 h3 h4 => by
    rw [u₁₂.other _ h4, o₁₁ _ h4 h2, u₁₀.other _ h4, u₉.other _ h3, u₈.other _ h3, u₇.other _ h1, u₆.other _ h1,
      u₅.other _ h1, u₄.other _ h1, u₃.other _ h1, u₂.other _ h2, u₁.other _ h1]
  have hrdx : s₁₂.gpr .rdx = ND + BitVec.ofNat 64 (i * p.n) := by
    rw [u₁₂.gpr, g₁₁, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbp, o₁₁ _ (by decide) (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h12, BitVec.add_comm, ← BitVec.ofNat_mul_ofNat]
  have hkey' : s₄.gpr .rax = V5 >>> z + BitVec.ofNat 64 i := by
    rw [u₄.gpr, u₃.gpr, u₃.other .rbp (by decide), u₂.other .rax (by decide), u₂.other .rbp (by decide), u₂.gpr,
      u₁.gpr, u₁.other .r14 (by decide), u₁.other .rbp (by decide), h5, h14, hbp, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hz]), Nat.mod_eq_of_lt (by omega_using [hz])]
  have hmask : s₁₂.gpr .rdi = if V5.toNat / 2 ^ z + i = V3.toNat then BitVec.allOnes 64 else 0 := by
    rw [u₁₂.other _ (by decide), o₁₁ _ (by decide) (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.gpr,
      u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, hkey', u₄.mem, u₃.mem, u₂.mem, u₁.mem, h3,
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, show (0 : BitVec 32).setWidth 64 = 0 by decide,
      mask_eq hk63]
    by_cases hc' : V5.toNat / 2 ^ z + i = V3.toNat
    · rw [ite_eq_left hc', ite_eq_left (hkey.mpr hc')]
    · rw [ite_eq_right hc', ite_eq_right (fun h => hc' (hkey.mp h))]
  have hnd' := hnd
  rw [← hrd, ← hwr] at hnd'
  rw [← hwr] at hau
  rw [List.nil_append]
  refine WP.block_append (WP.mono (xorWords_ok (c := V5.toNat / 2 ^ z + i = V3.toNat) (au := AP) (p.n / 8) s₁₂ hrdx
      (by rw [hkeep .r13 (by decide) (by decide) (by decide) (by decide), h13]) hmask hnd' hau
      (by rw [e8]; exact hdis) (by omega_using [hn])) fun s₁₃ ⟨g₁₃, r₁₃, w₁₃, c₁₃, f₁₃⟩ => ?_)
  refine wp_addi fun s₁₄ u₁₄ => wp_cmpr fun s₁₅ g₁₅ m₁₅ r₁₅ w₁₅ z₁₅ _ => WP.block_nil ?_
  have hbp₁₅ : s₁₅.gpr .rbp = BitVec.ofNat 64 (i + 1) := by
    rw [g₁₅, u₁₄.gpr, g₁₃ _ (by decide), hkeep _ (by decide) (by decide) (by decide) (by decide), hbp,
      show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add_ofNat]
  have h15' : s₁₅.gpr .r15 = BitVec.ofNat 64 c := by
    rw [g₁₅, u₁₄.other _ (by decide), g₁₃ _ (by decide), hkeep _ (by decide) (by decide) (by decide) (by decide), h15]
  refine ⟨fun g h1 h2 h3 h4 h5 => ?_, hbp₁₅, ?_, by rw [r₁₅, u₁₄.rd, r₁₃, hrd], by rw [w₁₅, u₁₄.wr, w₁₃, hwr],
    fun j hj => ?_, ?_⟩
  · rw [g₁₅, u₁₄.other _ h5, g₁₃ _ h1, hkeep _ h1 h2 h3 h4]
  · simp only [eval, z₁₅, Option.map_some]
    rw [g₁₅] at hbp₁₅ h15'
    rw [hbp₁₅, h15']
    congr 1
    by_cases he : i + 1 = c
    · subst he; simp
    · have : BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 c ≠ 0#64 := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i + 1) (by omega_using [hc, hic]),
          Nat.mod_eq_of_lt (a := c) (by omega_using [hc]), show (0#64).toNat = 0 from rfl] at this
        omega_using [this, he, hic, hc]
      simp [this, he]
  · rw [m₁₅, u₁₄.mem, c₁₃ j (by omega_using [e8, hj]), hm]
  · rw [m₁₅, u₁₄.mem, ← hm]
    rw [← e8] at f₁₃ ⊢
    rw [show 8 * (8 * (p.n / 8) / 8) = 8 * (p.n / 8) by omega_using [hn]] at f₁₃
    exact f₁₃

/-- The bytes XORed into the path's node after `i` passes of the scan: byte
`j` of node `sib - first`, if it is among the first `i`. -/
def acc (m : Mem) (S : Addr) (no n first sib i j : Nat) : Byte :=
  if first ≤ sib ∧ sib < first + i then m (at' S (no + (sib - first) * n + j)) else 0

theorem acc_zero (m : Mem) (S : Addr) (no n first sib j : Nat) : acc m S no n first sib 0 j = 0 := by
  simp only [acc, Nat.add_zero]; exact ite_eq_right (fun h => absurd h.2 (by omega_using [h.1]))

theorem acc_succ (m : Mem) (S : Addr) (no n first sib i j : Nat) :
    (if first + i = sib then m (at' S (no + i * n + j)) else 0) ^^^ acc m S no n first sib i j =
      acc m S no n first sib (i + 1) j := by
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

/-- `Layout.oVar 4 i`. -/
theorem oVar4 (i : Nat) : Layout.oVar 4 i = 2960 + 8 * i := by
  simp only [Layout.oVar, Layout.oFrame, Layout.oVars]

/-- The scan of a height (`scanInit`, then the loop of `scanBody`): the `c`
nodes at `nodes = S + no` (`r12`) of height `z` (`r14`), the path's node at
`AP` (`r13`), `idx` in variable 0 and `capBase` in variable 5. Byte `j` of
the path's node is XORed with byte `j` of the node whose index in its tree,
`⌊capBase / 2^z⌋ + i`, is the sibling `⌊idx / 2^z⌋ ⊕ 1`, if one is. -/
theorem scan_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S AP : Addr} {no z c : Nat}
    {V0 V5 : BitVec 64} {t : State} {Q : State → Prop}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (h13 : t.gpr .r13 = AP)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 z) (h15 : t.gpr .r15 = BitVec.ofNat 64 c)
    (hz : z < 64) (hc0 : 1 ≤ c) (hc : c < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hno : 3808 ≤ no) (hnoc' : no + c * p.n ≤ Layout.oSigTmp)
    (h0 : t.mem.readW (at' S (Layout.oVar 4 0)) 64 = V0) (h5 : t.mem.readW (at' S (Layout.oVar 4 5)) 64 = V5)
    (hV0 : V0.toNat < 2 ^ 32) (hV5 : V5.toNat < 2 ^ 32)
    (hau : ∀ w < p.n / 8, InRegions t.wr (AP + BitVec.ofNat 64 (8 * w)) 8)
    (hAd : Region.Disjoint ⟨AP, p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (k : ∀ t', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → g ≠ .rdx → g ≠ .rbp → t'.gpr g = t.gpr g) →
      t'.rd = t.rd → t'.wr = t.wr →
      (∀ j < p.n, t'.mem (AP + BitVec.ofNat 64 j) =
        acc t.mem S no p.n (V5.toNat / 2 ^ z) (V0.toNat / 2 ^ z ^^^ 1) c j ^^^ t.mem (AP + BitVec.ofNat 64 j)) →
      Frame [⟨AP, p.n⟩, ⟨at' S (Layout.oVar 4 3), 8⟩] t.mem t'.mem → Q t') :
    WP isa (.seq (.block scanInit) (.loop (.block (scanBody ⟨p.n, p.len⟩)) .ne)) t Q := by
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eT : Layout.oSigTmp = 31648 := rfl
  have hnoc : no + c * p.n ≤ 2 ^ 16 := by omega_using [hnoc', eT]
  have v0 := oVar4 0
  have v3 := oVar4 3
  have v5 := oVar4 5
  simp only [Nat.mul_zero, Nat.add_zero] at v0
  simp only [scanInit, var]
  refine WP.seq (wp_mov fun s₁ u₁ => wp_movm (by rw [ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.rd, u₁.wr, v0]; exact in_scr' hw (by omega_using [])) fun s₂ u₂ => wp_shrcl fun s₃ u₃ =>
    wp_xori fun s₄ u₄ => Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 3))
      (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
      (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, v3]; exact in_scr hw (by omega_using []))
      fun s₅ g₅ m₅ r₅ w₅ => wp_mov32i fun s₆ u₆ => WP.block_nil ?_)
  -- the sibling
  have hV3 : (V0 >>> z ^^^ 1).toNat = V0.toNat / 2 ^ z ^^^ 1 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have hV3lt : (V0 >>> z ^^^ 1).toNat < 2 ^ 33 := by
    rw [hV3]
    have : V0.toNat / 2 ^ z ≤ V0.toNat := Nat.div_le_self _ _
    exact Nat.xor_lt_two_pow (by omega_using [this, hV0]) (by decide)
  -- the loop's invariant: `i` passes done
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = c - i ∧ i < c ∧
    (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → g ≠ .rdx → g ≠ .rbp → s.gpr g = t.gpr g) ∧
    s.gpr .rbp = BitVec.ofNat 64 i ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
    s.mem.readW (at' S (Layout.oVar 4 3)) 64 = V0 >>> z ^^^ 1 ∧
    (∀ j < p.n, s.mem (AP + BitVec.ofNat 64 j) =
      acc t.mem S no p.n (V5.toNat / 2 ^ z) (V0.toNat / 2 ^ z ^^^ 1) i j ^^^ t.mem (AP + BitVec.ofNat 64 j)) ∧
    Frame [⟨AP, p.n⟩, ⟨at' S (Layout.oVar 4 3), 8⟩] t.mem s.mem
  -- the regions
  have hd3A : Region.Disjoint ⟨at' S (Layout.oVar 4 3), 8⟩ ⟨AP, p.n⟩ :=
    (hAd.sub_right (Offset.sub_base S (by rw [v3, eT]; omega_using []))).symm
  have hd5A : Region.Disjoint ⟨at' S (Layout.oVar 4 5), 8⟩ ⟨AP, p.n⟩ :=
    (hAd.sub_right (Offset.sub_base S (by rw [v5, eT]; omega_using []))).symm
  have hd53 : Region.Disjoint ⟨at' S (Layout.oVar 4 5), 8⟩ ⟨at' S (Layout.oVar 4 3), 8⟩ :=
    Offset.disjoint S (by rw [v3, v5]; omega_using []) (by rw [v5]; omega_using []) (by rw [v3]; omega_using [])
  have hdN3 : ∀ i < c, Region.Disjoint ⟨at' S (no + i * p.n), p.n⟩ ⟨at' S (Layout.oVar 4 3), 8⟩ := fun i hi => by
    have : i * p.n + p.n ≤ c * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    exact Offset.disjoint S (by rw [v3]; omega_using [hno]) (by omega_using [this, hnoc]) (by rw [v3]; omega_using [])
  have hdNA : ∀ i < c, Region.Disjoint ⟨at' S (no + i * p.n), p.n⟩ ⟨AP, p.n⟩ := fun i hi => by
    have : i * p.n + p.n ≤ c * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    exact (hAd.sub_right (Offset.sub_base S (by omega_using [this, hnoc']))).symm
  -- the state after `scanInit`
  have hm₆ : s₆.mem = t.mem.writeW (at' S (Layout.oVar 4 3)) (V0 >>> z ^^^ 1) := by
    rw [u₆.mem, m₅, u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h0, h14,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hz]), Nat.mod_eq_of_lt (by omega_using [hz]),
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide]
  have f₆ : Frame [⟨at' S (Layout.oVar 4 3), 8⟩] t.mem s₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.loop (M := isa) Inv (fun m s hI => ?_) c s₆ ⟨0, by omega_using [], hc0, fun g h1 h2 h3 h4 h5 => ?_, ?_,
    by rw [u₆.rd, r₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, w₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [hm₆, Mem.readW_writeW_self64], fun j hj => ?_, f₆.mono fun r hr => by simp at hr; simp [hr]⟩
  rotate_left
  · rw [u₆.other _ h5, g₅, u₄.other _ h1, u₃.other _ h1, u₂.other _ h1, u₁.other _ h2]
  · rw [u₆.gpr]; decide
  · rw [acc_zero, f₆.bytes (R := ⟨AP, p.n⟩) (fun r hr => by simp at hr; subst hr; exact hd3A.symm)
      (by show p.n ≤ 2 ^ 64; omega_using [hn32]) hj]
    simp
  -- one pass
  obtain ⟨i, rfl, hic, hg, hbp, hrd, hwr, h3, hacc, hf⟩ := hI
  have hin : i * p.n + p.n ≤ c * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hic
  have hnode : ∀ j < p.n, s.mem (at' S (no + i * p.n) + BitVec.ofNat 64 j) = t.mem (at' S (no + i * p.n) + BitVec.ofNat 64 j) :=
    fun j hj => hf.bytes (R := ⟨at' S (no + i * p.n), p.n⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdNA i hic
      · exact hdN3 i hic) (by show p.n ≤ 2 ^ 64; omega_using [hn32]) hj
  have h5s : s.mem.readW (at' S (Layout.oVar 4 5)) 64 = V5 := by
    rw [← h5]
    refine hf.readW (r := ⟨at' S (Layout.oVar 4 5), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd5A
    · exact hd53
  have hgs : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → g ≠ .rdx → g ≠ .rbp → s.gpr g = t.gpr g := hg
  refine WP.mono (scanBody_ok (p := p) hn (S := S) (ND := at' S no) (AP := AP) (z := z) (i := i) (c := c)
    (V3 := V0 >>> z ^^^ 1) (V5 := V5)
    (by rw [hgs .rbx (by decide) (by decide) (by decide) (by decide) (by decide), hbx])
    (by rw [hgs .r12 (by decide) (by decide) (by decide) (by decide) (by decide), h12])
    (by rw [hgs .r13 (by decide) (by decide) (by decide) (by decide) (by decide), h13])
    (by rw [hgs .r14 (by decide) (by decide) (by decide) (by decide) (by decide), h14])
    (by rw [hgs .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h15])
    hbp hz hic hc h3 h5s hV3lt hV5
    (by rw [hrd, hwr, v3]; exact in_scr' hw (by omega_using []))
    (by rw [hrd, hwr, v5]; exact in_scr' hw (by omega_using []))
    (fun w hw' => by
      rw [hrd, hwr, add_add, add_add]
      exact in_scr' hw (by omega_using [hin, hnoc, hw', e8]))
    (by rw [hwr]; exact hau) (by rw [add_add]; exact hdNA i hic)) fun s' ⟨g', bp', ev', rd', wr', by', f'⟩ => ?_
  have hI' : ∀ j < p.n, s'.mem (AP + BitVec.ofNat 64 j) =
      acc t.mem S no p.n (V5.toNat / 2 ^ z) (V0.toNat / 2 ^ z ^^^ 1) (i + 1) j ^^^ t.mem (AP + BitVec.ofNat 64 j) := by
    intro j hj
    rw [by' j hj, hacc j hj, add_add S no (i * p.n), hnode j hj, hV3, ← BitVec.xor_assoc, add_add, ← acc_succ]
  have hf' : Frame [⟨AP, p.n⟩, ⟨at' S (Layout.oVar 4 3), 8⟩] t.mem s'.mem :=
    hf.trans (f'.mono fun r hr => by simp at hr; simp [hr])
  have hg' : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → g ≠ .rdx → g ≠ .rbp → s'.gpr g = t.gpr g :=
    fun g h1 h2 h3 h4 h5 => by rw [g' g h1 h2 h3 h4 h5, hgs g h1 h2 h3 h4 h5]
  by_cases he : i + 1 = c
  · refine .inl ⟨by rw [ev']; simp [he], k s' hg' (by rw [rd', hrd]) (by rw [wr', hwr]) ?_ hf'⟩
    rw [← he]; exact hI'
  · refine .inr ⟨by rw [ev']; simp [he], c - (i + 1), by omega_using [hic, he], i + 1, rfl, by omega_using [hic, he], hg',
      bp', by rw [rd', hrd], by rw [wr', hwr], ?_, hI', hf'⟩
    rw [← h3]
    refine f'.readW (r := ⟨at' S (Layout.oVar 4 3), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr; exact hd3A

end VG.Proof.SlhDsa.X86_64.Levels
