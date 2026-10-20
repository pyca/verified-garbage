module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Writing the derived key: p||q||g, y and x under the final mask -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- What one masked copy of `n` bytes from `src` to `dst` leaves. -/
def PieceCopied (R : State → Prop) (rs : List Reg) (s : State) (src dst : Addr) (n : Nat) (valid : Bool)
    (t : State) : Prop :=
  (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
  (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
  t.gpr .x8 = mask valid ∧ R t ∧ Keep (rs ++ [.x3, .x1, .x2, .x9]) s t

theorem copyPiece_ok {s : State} {head : List Instr} {R : State → Prop} {rs : List Reg} {src dst : Addr}
    {n : Nat} {valid : Bool}
    (hR : ∀ t t', R t → Keep [.x3, .x1, .x2, .x9] t t' → R t')
    (hh : WP isa (.block head) s fun t => t.gpr .x1 = src ∧ t.gpr .x2 = dst ∧
      t.gpr .x9 = BitVec.ofNat 64 n ∧ t.gpr .x8 = mask valid ∧ t.mem = s.mem ∧ Keep rs s t ∧ R t)
    (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    WP isa (.seq (.block head) Generate.copyMasked) s (PieceCopied R rs s src dst n valid) := by
  refine WP.seq (WP.mono hh fun u ⟨husi, hudx, hucx, hu8, hum, hku, hRu⟩ => ?_)
  refine WP.mono (copyMasked_ok husi hudx hucx hu8 h1 h64
    (fun i hi => by rw [hku.rd, hku.wr]; exact hr i hi)
    (fun i hi => by rw [hku.wr]; exact hw i hi) hsep) fun t ⟨htb, htf, hkt⟩ => ?_
  exact ⟨by rw [hum] at htb; exact htb, fun x hx => (htf x hx).trans (congrFun hum x),
    (hkt.gpr .x8 (by decide)).trans hu8, hR u t hRu hkt, hku.trans hkt⟩

/-- The key's fields, read from the scratch's first words. -/
structure KeyFields (s : State) (B O P Y X : Addr) (p q : Nat) (valid : Bool) : Prop where
  out : word s.mem B Field.out.offset = O
  params : word s.mem B Field.p.offset = P
  publicValue : word s.mem B Field.y.offset = Y
  scalar : word s.mem B Field.x.offset = X
  pLen : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p
  qLen : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q
  mask : word s.mem B Field.mask.offset = mask valid

/-- The registers the key's copies compute addresses from. -/
structure KeyRegs (t : State) (O Y X : Addr) (p q : Nat) : Prop where
  out : t.gpr .x10 = O
  publicValue : t.gpr .x11 = Y
  scalar : t.gpr .x12 = X
  pLen : t.gpr .x13 = BitVec.ofNat 64 p
  qLen : t.gpr .x14 = BitVec.ofNat 64 q

abbrev keyRegs : List Reg := [.x1, .x2, .x9, .x8, .x11, .x12, .x13, .x14, .x10]

theorem KeyRegs.keep {s t : State} {O Y X : Addr} {p q : Nat} (h : KeyRegs s O Y X p q)
    {rs : List Reg} (hk : Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x10) :
    KeyRegs t O Y X p q :=
  ⟨(hk.gpr .x10 fun h' => (hrs _ h').2.2.2.2 rfl).trans h.out, (hk.gpr .x11 fun h' => (hrs _ h').1 rfl).trans h.publicValue,
    (hk.gpr .x12 fun h' => (hrs _ h').2.1 rfl).trans h.scalar, (hk.gpr .x13 fun h' => (hrs _ h').2.2.1 rfl).trans h.pLen,
    (hk.gpr .x14 fun h' => (hrs _ h').2.2.2.1 rfl).trans h.qLen⟩

theorem keyHead_ok {s : State} {B O P Y X : Addr} {Z p q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hf : KeyFields s B O P Y X p q valid) :
    WP isa (.block Generate.keyHead) s fun t =>
      t.gpr .x1 = P ∧ t.gpr .x2 = O ∧ t.gpr .x9 = BitVec.ofNat 64 (2 * p + q) ∧
      t.gpr .x8 = mask valid ∧ t.mem = s.mem ∧ Keep keyRegs s t ∧ KeyRegs t O Y X p q := by
  refine WP.mono (WP.keep keyRegs (Q := fun t =>
      t.gpr .x1 = P ∧ t.gpr .x2 = O ∧ t.gpr .x9 = BitVec.ofNat 64 (2 * p + q) ∧
      t.gpr .x8 = mask valid ∧ t.mem = s.mem ∧ KeyRegs t O Y X p q) ?_ rfl rfl rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, hk, h6⟩
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold Generate.keyHead
  brun [Core.field, field_enc .mask, field_enc .out, field_enc .y, field_enc .x, field_enc .p, field_enc .pLen, field_enc .qLen, fieldAddress, hdi, hl .mask, hl .out, hl .y, hl .x, hl .p, hl .pLen, hl .qLen,
    hf.mask, hf.out, hf.publicValue, hf.scalar, hf.params, hf.pLen, hf.qLen]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [BitVec.ofNat_add_ofNat]
  congr 1
  omega

theorem keyHead₂_ok {s : State} {O Y X : Addr} {p q : Nat} {valid : Bool}
    (hr : KeyRegs s O Y X p q) (h8 : s.gpr .x8 = mask valid) :
    WP isa (.block [.add .x .x2 .x10 .x13, .add .x .x2 .x2 .x13,
      .add .x .x2 .x2 .x14, mov .x1 .x11, mov .x9 .x13]) s fun t =>
      t.gpr .x1 = Y ∧ t.gpr .x2 = O + BitVec.ofNat 64 (2 * p + q) ∧ t.gpr .x9 = BitVec.ofNat 64 p ∧
      t.gpr .x8 = mask valid ∧ t.mem = s.mem ∧ Keep [.x1, .x2, .x9] s t ∧ KeyRegs t O Y X p q := by
  refine WP.mono (WP.keep [.x1, .x2, .x9] (Q := fun t =>
      t.gpr .x1 = Y ∧ t.gpr .x2 = O + BitVec.ofNat 64 (2 * p + q) ∧ t.gpr .x9 = BitVec.ofNat 64 p ∧
      t.gpr .x8 = mask valid ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk, hr.keep hk (by decide)⟩
  brun [hr.out, hr.publicValue, hr.pLen, hr.qLen, h8]
  dsimp only [off]
  congr 2
  omega

theorem keyHead₃_ok {s : State} {O Y X : Addr} {p q : Nat} {valid : Bool}
    (hr : KeyRegs s O Y X p q) (h8 : s.gpr .x8 = mask valid) :
    WP isa (.block [.add .x .x2 .x10 .x13, .add .x .x2 .x2 .x13,
      .add .x .x2 .x2 .x13, .add .x .x2 .x2 .x14, mov .x1 .x12, mov .x9 .x14]) s fun t =>
      t.gpr .x1 = X ∧ t.gpr .x2 = O + BitVec.ofNat 64 (3 * p + q) ∧ t.gpr .x9 = BitVec.ofNat 64 q ∧
      t.gpr .x8 = mask valid ∧ t.mem = s.mem ∧ Keep [.x1, .x2, .x9] s t ∧ KeyRegs t O Y X p q := by
  refine WP.mono (WP.keep [.x1, .x2, .x9] (Q := fun t =>
      t.gpr .x1 = X ∧ t.gpr .x2 = O + BitVec.ofNat 64 (3 * p + q) ∧ t.gpr .x9 = BitVec.ofNat 64 q ∧
      t.gpr .x8 = mask valid ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk, hr.keep hk (by decide)⟩
  brun [hr.out, hr.scalar, hr.pLen, hr.qLen, h8]
  dsimp only [off]
  congr 2
  omega

/-- A source of `n` bytes the copies may read: readable, and apart from the
output. -/
def KeySource (s : State) (src O : Addr) (n k : Nat) : Prop :=
  (∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1) ∧
  (∀ i < n, ∀ j < k, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j)

theorem writeKey_ok {s : State} {B O P Y X : Addr} {Z p q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hf : KeyFields s B O P Y X p q valid) (hp : 0 < p) (hq : 0 < q) (hk : 3 * p + 2 * q < 2 ^ 64)
    (hP : KeySource s P O (2 * p + q) (3 * p + 2 * q)) (hY : KeySource s Y O p (3 * p + 2 * q))
    (hX : KeySource s X O q (3 * p + 2 * q))
    (hw : ∀ i < 3 * p + 2 * q, InRegions s.wr (O + BitVec.ofNat 64 i) 1) :
    WP isa Generate.writeKey s fun t =>
      (∀ i < 2 * p + q, t.mem (O + BitVec.ofNat 64 i) = if valid then s.mem (P + BitVec.ofNat 64 i) else 0) ∧
      (∀ i < p, t.mem (O + BitVec.ofNat 64 (2 * p + q + i)) =
        if valid then s.mem (Y + BitVec.ofNat 64 i) else 0) ∧
      (∀ i < q, t.mem (O + BitVec.ofNat 64 (3 * p + q + i)) =
        if valid then s.mem (X + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep (.x3 :: keyRegs) s t := by
  have shift (d i : Nat) : O + BitVec.ofNat 64 d + BitVec.ofNat 64 i = O + BitVec.ofNat 64 (d + i) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hrange (d n : Nat) (hd : d + n ≤ 3 * p + 2 * q) :
      ∀ i < n, InRegions s.wr (O + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1 :=
    fun i hi => by rw [shift]; exact hw _ (by omega)
  have hapart (src : Addr) (n d m : Nat) (hd : d + m ≤ 3 * p + 2 * q)
      (h : ∀ i < n, ∀ j < 3 * p + 2 * q, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j) :
      ∀ i < n, ∀ j < m, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 d + BitVec.ofNat 64 j :=
    fun i hi j hj => by rw [shift]; exact h i hi _ (by omega)
  have hregs : ∀ r ∈ [Reg.x1, .x2, .x9, .x3], r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x10 := by
    decide
  unfold Generate.writeKey seqs
  have hRk : ∀ t t', KeyRegs t O Y X p q → Keep [.x3, .x1, .x2, .x9] t t' → KeyRegs t' O Y X p q :=
    fun t t' h hk => h.keep hk (by decide)
  -- p||q||g
  apply WP.assoc
  refine WP.seq (WP.mono (copyPiece_ok (n := 2 * p + q) (rs := keyRegs) hRk (keyHead_ok hs hdi hZ hf)
    (by omega) (by omega)
    hP.1 (fun i hi => by simpa using hrange 0 (2 * p + q) (by omega) i hi)
    (fun i hi j hj => by simpa using hapart P _ 0 (2 * p + q) (by omega) hP.2 i hi j hj)) fun s₁ h₁ => ?_)
  obtain ⟨hb₁, hfr₁, h8₁, hR₁, k₁⟩ := h₁
  have hfr₁' : ∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → s₁.mem x = s.mem x :=
    fun x hx => hfr₁ x fun i hi => hx i (by omega)
  -- y
  apply WP.assoc
  refine WP.seq (WP.mono (copyPiece_ok (n := p) (rs := [.x1, .x2, .x9]) hRk (keyHead₂_ok hR₁ h8₁) hp (by omega)
    (fun i hi => by rw [k₁.rd, k₁.wr]; exact hY.1 i hi)
    (fun i hi => by rw [k₁.wr]; exact hrange (2 * p + q) p (by omega) i hi)
    (hapart Y p (2 * p + q) p (by omega) hY.2)) fun s₂ h₂ => ?_)
  obtain ⟨hb₂, hfr₂, h8₂, hR₂, k₂⟩ := h₂
  have hfr₂' : ∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → s₂.mem x = s.mem x :=
    fun x hx => (hfr₂ x fun i hi => by rw [shift]; exact hx _ (by omega)).trans (hfr₁' x hx)
  have k₁₂ := k₁.trans k₂
  -- x
  refine WP.mono (copyPiece_ok (n := q) (rs := [.x1, .x2, .x9]) hRk (keyHead₃_ok hR₂ h8₂) hq (by omega)
    (fun i hi => by rw [k₁₂.rd, k₁₂.wr]; exact hX.1 i hi)
    (fun i hi => by rw [k₁₂.wr]; exact hrange (3 * p + q) q (by omega) i hi)
    (hapart X q (3 * p + q) q (by omega) hX.2)) fun t ⟨hb₃, hfr₃, _, _, k₃⟩ => ?_
  have hne (a b : Nat) (ha : a < 3 * p + 2 * q) (hb : b < 3 * p + 2 * q) (h : a ≠ b) :
      O + BitVec.ofNat 64 a ≠ O + BitVec.ofNat 64 b := out_ne (by omega) (by omega) h
  refine ⟨?_, ?_, ?_, ?_, ((k₁₂.trans k₃).mono (by decide))⟩
  · intro i hi
    rw [hfr₃ _ fun j hj => by rw [shift]; exact hne _ _ (by omega) (by omega) (by omega),
      hfr₂ _ fun j hj => by rw [shift]; exact hne _ _ (by omega) (by omega) (by omega)]
    simpa using hb₁ i hi
  · intro i hi
    rw [hfr₃ _ fun j hj => by rw [shift]; exact hne _ _ (by omega) (by omega) (by omega), ← shift, hb₂ i hi,
      hfr₁' _ fun j hj => hY.2 i hi j hj]
  · intro i hi
    rw [← shift, hb₃ i hi, hfr₂' _ fun j hj => hX.2 i hi j hj]
  · intro x hx
    exact (hfr₃ x fun i hi => by rw [shift]; exact hx _ (by omega)).trans (hfr₂' x hx)

end VG.Proof.Dsa.AArch64
