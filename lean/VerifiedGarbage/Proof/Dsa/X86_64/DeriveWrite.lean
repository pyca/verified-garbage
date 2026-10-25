module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! # Writing the derived key: p||q||g, y and x under the final mask -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- What one masked copy of `n` bytes from `src` to `dst` leaves. -/
def PieceCopied (R : State → Prop) (rs : List Reg) (s : State) (src dst : Addr) (n : Nat) (valid : Bool)
    (t : State) : Prop :=
  (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
  (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
  t.gpr .r8 = mask valid ∧ R t ∧ Keep (rs ++ [.rax, .rsi, .rdx, .rcx]) s t

theorem copyPiece_ok {s : State} {head : List Instr} {R : State → Prop} {rs : List Reg} {src dst : Addr}
    {n : Nat} {valid : Bool}
    (hR : ∀ t t', R t → Keep [.rax, .rsi, .rdx, .rcx] t t' → R t')
    (hh : WP isa (.block head) s fun t => t.gpr .rsi = src ∧ t.gpr .rdx = dst ∧
      t.gpr .rcx = BitVec.ofNat 64 n ∧ t.gpr .r8 = mask valid ∧ t.mem = s.mem ∧ Keep rs s t ∧ R t)
    (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    WP isa (.seq (.block head) Generate.copyMasked) s (PieceCopied R rs s src dst n valid) := by
  refine WP.seq (WP.mono hh fun u ⟨husi, hudx, hucx, hu8, hum, hku, hRu⟩ => ?_)
  refine WP.mono (copyMasked_ok husi hudx hucx hu8 h1 h64
    (fun i hi => by rw [hku.2.1, hku.2.2]; exact hr i hi)
    (fun i hi => by rw [hku.2.2]; exact hw i hi) hsep) fun t ⟨htb, htf, hkt⟩ => ?_
  exact ⟨by rw [hum] at htb; exact htb, fun x hx => (htf x hx).trans (congrFun hum x),
    (hkt.gpr (by decide)).trans hu8, hR u t hRu hkt, hku.trans hkt⟩

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
  out : t.gpr .r13 = O
  publicValue : t.gpr .r9 = Y
  scalar : t.gpr .r10 = X
  pLen : t.gpr .r11 = BitVec.ofNat 64 p
  qLen : t.gpr .r12 = BitVec.ofNat 64 q

abbrev keyRegs : List Reg := [.rsi, .rdx, .rcx, .r8, .r9, .r10, .r11, .r12, .r13]

theorem KeyRegs.keep {s t : State} {O Y X : Addr} {p q : Nat} (h : KeyRegs s O Y X p q)
    {rs : List Reg} (hk : Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧ r ≠ .r13) :
    KeyRegs t O Y X p q :=
  ⟨(hk.gpr fun h' => (hrs _ h').2.2.2.2 rfl).trans h.out, (hk.gpr fun h' => (hrs _ h').1 rfl).trans h.publicValue,
    (hk.gpr fun h' => (hrs _ h').2.1 rfl).trans h.scalar, (hk.gpr fun h' => (hrs _ h').2.2.1 rfl).trans h.pLen,
    (hk.gpr fun h' => (hrs _ h').2.2.2.1 rfl).trans h.qLen⟩

theorem keyHead_ok {s : State} {B O P Y X : Addr} {Z p q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hf : KeyFields s B O P Y X p q valid) :
    WP isa (.block Generate.keyHead) s fun t =>
      t.gpr .rsi = P ∧ t.gpr .rdx = O ∧ t.gpr .rcx = BitVec.ofNat 64 (2 * p + q) ∧
      t.gpr .r8 = mask valid ∧ t.mem = s.mem ∧ Keep keyRegs s t ∧ KeyRegs t O Y X p q := by
  refine WP.mono (WP.keep keyRegs (Q := fun t =>
      t.gpr .rsi = P ∧ t.gpr .rdx = O ∧ t.gpr .rcx = BitVec.ofNat 64 (2 * p + q) ∧
      t.gpr .r8 = mask valid ∧ t.mem = s.mem ∧ KeyRegs t O Y X p q) ?_ rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, hk, h6⟩
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold Generate.keyHead
  xrun [State.ea, Core.field, fieldAddress, hdi, hl .mask, hl .out, hl .y, hl .x, hl .p, hl .pLen, hl .qLen,
    hf.mask, hf.out, hf.publicValue, hf.scalar, hf.params, hf.pLen, hf.qLen]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [BitVec.ofNat_add_ofNat]
  congr 1
  omega_arith

theorem keyHead₂_ok {s : State} {O Y X : Addr} {p q : Nat} {valid : Bool}
    (hr : KeyRegs s O Y X p q) (h8 : s.gpr .r8 = mask valid) :
    WP isa (.block [.mov .rdx (.reg .r13), .alu .add .rdx (.reg .r11), .alu .add .rdx (.reg .r11),
      .alu .add .rdx (.reg .r12), .mov .rsi (.reg .r9), .mov .rcx (.reg .r11)]) s fun t =>
      t.gpr .rsi = Y ∧ t.gpr .rdx = O + BitVec.ofNat 64 (2 * p + q) ∧ t.gpr .rcx = BitVec.ofNat 64 p ∧
      t.gpr .r8 = mask valid ∧ t.mem = s.mem ∧ Keep [.rsi, .rdx, .rcx] s t ∧ KeyRegs t O Y X p q := by
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx] (Q := fun t =>
      t.gpr .rsi = Y ∧ t.gpr .rdx = O + BitVec.ofNat 64 (2 * p + q) ∧ t.gpr .rcx = BitVec.ofNat 64 p ∧
      t.gpr .r8 = mask valid ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk, hr.keep hk (by decide)⟩
  xrun [hr.out, hr.publicValue, hr.pLen, hr.qLen, h8]
  simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega_arith

theorem keyHead₃_ok {s : State} {O Y X : Addr} {p q : Nat} {valid : Bool}
    (hr : KeyRegs s O Y X p q) (h8 : s.gpr .r8 = mask valid) :
    WP isa (.block [.mov .rdx (.reg .r13), .alu .add .rdx (.reg .r11), .alu .add .rdx (.reg .r11),
      .alu .add .rdx (.reg .r11), .alu .add .rdx (.reg .r12), .mov .rsi (.reg .r10), .mov .rcx (.reg .r12)]) s fun t =>
      t.gpr .rsi = X ∧ t.gpr .rdx = O + BitVec.ofNat 64 (3 * p + q) ∧ t.gpr .rcx = BitVec.ofNat 64 q ∧
      t.gpr .r8 = mask valid ∧ t.mem = s.mem ∧ Keep [.rsi, .rdx, .rcx] s t ∧ KeyRegs t O Y X p q := by
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx] (Q := fun t =>
      t.gpr .rsi = X ∧ t.gpr .rdx = O + BitVec.ofNat 64 (3 * p + q) ∧ t.gpr .rcx = BitVec.ofNat 64 q ∧
      t.gpr .r8 = mask valid ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk, hr.keep hk (by decide)⟩
  xrun [hr.out, hr.scalar, hr.pLen, hr.qLen, h8]
  simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega_arith

/-- A source of `n` bytes the copies may read: readable, and apart from the
output. -/
def KeySource (s : State) (src O : Addr) (n k : Nat) : Prop :=
  (∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1) ∧
  (∀ i < n, ∀ j < k, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j)

theorem writeKey_ok {s : State} {B O P Y X : Addr} {Z p q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
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
      Keep (.rax :: keyRegs) s t := by
  have shift (d i : Nat) : O + BitVec.ofNat 64 d + BitVec.ofNat 64 i = O + BitVec.ofNat 64 (d + i) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hrange (d n : Nat) (hd : d + n ≤ 3 * p + 2 * q) :
      ∀ i < n, InRegions s.wr (O + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1 :=
    fun i hi => by rw [shift]; exact hw _ (by omega_arith)
  have hapart (src : Addr) (n d m : Nat) (hd : d + m ≤ 3 * p + 2 * q)
      (h : ∀ i < n, ∀ j < 3 * p + 2 * q, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j) :
      ∀ i < n, ∀ j < m, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 d + BitVec.ofNat 64 j :=
    fun i hi j hj => by rw [shift]; exact h i hi _ (by omega_arith)
  have hregs : ∀ r ∈ [Reg.rsi, .rdx, .rcx, .rax], r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧ r ≠ .r13 := by
    decide
  unfold Generate.writeKey seqs
  have hRk : ∀ t t', KeyRegs t O Y X p q → Keep [.rax, .rsi, .rdx, .rcx] t t' → KeyRegs t' O Y X p q :=
    fun t t' h hk => h.keep hk (by decide)
  -- p||q||g
  apply WP.assoc
  refine WP.seq (WP.mono (copyPiece_ok (n := 2 * p + q) (rs := keyRegs) hRk (keyHead_ok hs hdi hZ hf)
    (by omega_arith) (by omega_arith)
    hP.1 (fun i hi => by simpa using hrange 0 (2 * p + q) (by omega_arith) i hi)
    (fun i hi j hj => by simpa using hapart P _ 0 (2 * p + q) (by omega_arith) hP.2 i hi j hj)) fun s₁ h₁ => ?_)
  obtain ⟨hb₁, hfr₁, h8₁, hR₁, k₁⟩ := h₁
  have hfr₁' : ∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → s₁.mem x = s.mem x :=
    fun x hx => hfr₁ x fun i hi => hx i (by omega_arith)
  -- y
  apply WP.assoc
  refine WP.seq (WP.mono (copyPiece_ok (n := p) (rs := [.rsi, .rdx, .rcx]) hRk (keyHead₂_ok hR₁ h8₁) hp (by omega_arith)
    (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact hY.1 i hi)
    (fun i hi => by rw [k₁.2.2]; exact hrange (2 * p + q) p (by omega_arith) i hi)
    (hapart Y p (2 * p + q) p (by omega_arith) hY.2)) fun s₂ h₂ => ?_)
  obtain ⟨hb₂, hfr₂, h8₂, hR₂, k₂⟩ := h₂
  have hfr₂' : ∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → s₂.mem x = s.mem x :=
    fun x hx => (hfr₂ x fun i hi => by rw [shift]; exact hx _ (by omega_arith)).trans (hfr₁' x hx)
  have k₁₂ := k₁.trans k₂
  -- x
  refine WP.mono (copyPiece_ok (n := q) (rs := [.rsi, .rdx, .rcx]) hRk (keyHead₃_ok hR₂ h8₂) hq (by omega_arith)
    (fun i hi => by rw [k₁₂.2.1, k₁₂.2.2]; exact hX.1 i hi)
    (fun i hi => by rw [k₁₂.2.2]; exact hrange (3 * p + q) q (by omega_arith) i hi)
    (hapart X q (3 * p + q) q (by omega_arith) hX.2)) fun t ⟨hb₃, hfr₃, _, _, k₃⟩ => ?_
  have hne (a b : Nat) (ha : a < 3 * p + 2 * q) (hb : b < 3 * p + 2 * q) (h : a ≠ b) :
      O + BitVec.ofNat 64 a ≠ O + BitVec.ofNat 64 b := out_ne (by omega_arith) (by omega_arith) h
  refine ⟨?_, ?_, ?_, ?_, ((k₁₂.trans k₃).mono (by decide))⟩
  · intro i hi
    rw [hfr₃ _ fun j hj => by rw [shift]; exact hne _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      hfr₂ _ fun j hj => by rw [shift]; exact hne _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    simpa using hb₁ i hi
  · intro i hi
    rw [hfr₃ _ fun j hj => by rw [shift]; exact hne _ _ (by omega_arith) (by omega_arith) (by omega_arith), ← shift, hb₂ i hi,
      hfr₁' _ fun j hj => hY.2 i hi j hj]
  · intro i hi
    rw [← shift, hb₃ i hi, hfr₂' _ fun j hj => hX.2 i hi j hj]
  · intro x hx
    exact (hfr₃ x fun i hi => by rw [shift]; exact hx _ (by omega_arith)).trans (hfr₂' x hx)

end VG.Proof.Dsa.X86_64
