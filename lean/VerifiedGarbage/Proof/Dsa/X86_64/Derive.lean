module

public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.Execution
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import Mathlib.Order.RelClasses

/-! ### `Dsa.X86_64.DeriveWrite`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.X86_64.DeriveCopy`, which this module and modules that import it used -/

section

/-! # Copying the derived y past the signer's layout

Writes above the workspaces keep them, and the fields, ready. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem child_of_outside {mem mem' : Mem} {B : Addr} {o wx m d k : Nat} {minv : BitVec 64}
    (child : ChildReady mem B o wx m minv) (hf : Outside B d k mem mem')
    (hd : o + slot wx 8 ≤ d) (hbound : o + slot wx 8 ≤ 2 ^ 64) : ChildReady mem' B o wx m minv := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  have he : ∀ e, e + 8 ≤ slot wx 8 → word mem' (off B o) e = word mem (off B o) e := by
    intro e he
    rw [word_off, word_off]
    exact hf.word (Or.inl (by omega_using [hd, he])) (by omega_using [hbound, he])
  refine ⟨child.header.of_words (fun i hi => he _ (by omega_using [hslot, hi])), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega_using [hN, hi]))]
    exact child.modulus
  · rw [he _ (by omega_using [hN])]
    exact child.inverse

/-- Writes at or above the workspaces' end keep a ready state ready. -/
theorem Ready.of_outside {L : ExecutionLayout} {s t : State} {d k : Nat} (h : Ready L s)
    (hf : Outside L.base d k s.mem t.mem) (hd : activeBytes ≤ d)
    (hdi : t.gpr .rdi = L.base) (hwr : t.wr = s.wr) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have he : ∀ i < 32, word t.mem L.base (8 * i) = word s.mem L.base (8 * i) := fun i hi =>
    hf.word (Or.inl (by have : 256 ≤ activeBytes := (by decide); omega_using [hd, hi, this])) (by omega_using [hi])
  have hg := h.parent
  refine ⟨⟨hg.scr.congr hwr, hdi, ⟨(he _ (by decide)).trans hg.hdr.hw, (he _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (he _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩⟩,
    h.scratch.congr hwr, ?_, child_of_outside h.pChild hf (by omega_using [hd, hpHi, hqHi]) (by have : activeBytes < 2 ^ 64 := (by decide); omega_using [hpHi, hqHi, this]),
    child_of_outside h.qChild hf (by omega_using [hd, hqHi]) (by have : activeBytes < 2 ^ 64 := (by decide); omega_using [hqHi, this])⟩
  intro f hm
  exact (hf.word (Or.inl (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by
    have : 368 ≤ activeBytes := (by decide)
    omega_using [hd, hpHi, hqHi]))) (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))).trans (h.fields f hm)

theorem minusOne_mask : BitVec.signExtend 64 (-1 : BitVec 32) = mask true := by decide

theorem scr_byte_rd {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (hd : d < Z) :
    InRegions (s.rd ++ s.wr) (off B d) 1 :=
  let ⟨r, hr, hc⟩ := hs.region (d := d) (n := 1) (by omega_using [hd]) (by decide)
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem off_add (B : Addr) (d i : Nat) : off B d + BitVec.ofNat 64 i = off B (d + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The scalar workspace's register setup for copying y. -/
theorem copyHead_ok {L : ExecutionLayout} {s : State} (h : Ready L s) :
    WP isa (.block [.mov .rsi (.reg .rdi), .alu .add .rsi (.imm (BitVec.ofNat 32 t2)),
      .mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 derivedY)),
      .mov .rcx (.mem (Core.field .pLen)), .mov .r8 (.imm (-1))]) s fun t =>
      t.gpr .rsi = off L.base t2 ∧ t.gpr .rdx = off L.base derivedY ∧
      t.gpr .rcx = BitVec.ofNat 64 L.pLen ∧ t.gpr .r8 = mask true ∧ t.mem = s.mem ∧
      Keep [.rsi, .rdx, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8] (Q := fun t =>
      t.gpr .rsi = off L.base t2 ∧ t.gpr .rdx = off L.base derivedY ∧
      t.gpr .rcx = BitVec.ofNat 64 L.pLen ∧ t.gpr .r8 = mask true ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, hk⟩
  xrun [State.ea, Core.field, fieldAddress, h.parent.rdi,
    sx_ofNat (show t2 < 2 ^ 31 by decide), sx_ofNat (show derivedY < 2 ^ 31 by decide),
    h.scratch.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 (by decide)),
    h.fields .pLen (by decide), L.pLength, minusOne_mask]

/-- y, computed at t2, copied to `derivedY`, past the signer's layout,
where the checks read it as an input. -/
theorem copyY_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (hs : Scr s L.base (derivedY + 384)) :
    WP isa Generate.copyY s fun t =>
      Ready L t ∧
      (∀ i < L.pLen, t.mem (off L.base derivedY + BitVec.ofNat 64 i) = s.mem (off L.base t2 + BitVec.ofNat 64 i)) ∧
      Outside L.base derivedY L.pLen s.mem t.mem ∧ Keep coreRegs s t := by
  have hn := hs.nowrap
  unfold Generate.copyY seqs
  refine WP.seq (WP.mono (copyHead_ok h) fun u ⟨husi, hudx, hucx, hu8, hum, hku⟩ => ?_)
  have hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    have hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  have hp1 := hp384.1
  replace hp384 := hp384.2
  have ht2 : t2 = 15328 := rfl
  have hdy : derivedY = 15712 := rfl
  have hr : ∀ i < L.pLen, InRegions (u.rd ++ u.wr) (off L.base t2 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hku.2.1, hku.2.2, off_add]
    exact scr_byte_rd hs (by rw [ht2, hdy]; omega_using [hi, hp384])
  have hw : ∀ i < L.pLen, InRegions u.wr (off L.base derivedY + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hku.2.2, off_add]
    exact (hs.region (d := derivedY + i) (n := 1) (by omega_using [hi, hp384]) (by decide)).elim
      fun r hr => ⟨r, hr.1, hr.2⟩
  have hsep : ∀ i < L.pLen, ∀ j < L.pLen, off L.base t2 + BitVec.ofNat 64 i ≠ off L.base derivedY + BitVec.ofNat 64 j :=
    fun i hi => scr_ne_out (Z := derivedY) (fun j hj => by
      rw [ofs_off _ (by rw [hdy]; omega_using [hj, hp384])]; omega_using [])
      (by rw [ht2, hdy]; omega_using [hi, hp384]) (by rw [hdy]; omega_using [])
  refine WP.mono (copyMasked_ok husi hudx hucx hu8 (by omega_using [hp1]) (by omega_using [hp384]) hr hw hsep)
    fun t ⟨htb, htf, hkt⟩ => ?_
  have hk := hku.trans hkt
  have hframe : Outside L.base derivedY L.pLen s.mem t.mem := by
    intro x hx
    refine (htf x fun i hi he => ?_).trans (congrFun hum x)
    subst he
    rw [ofs_off _ (by rw [hdy]; omega_using [hi, hp384])] at hx
    omega_using [hx, hi]
  refine ⟨h.of_outside hframe (by decide) ((hk.gpr (by decide)).trans h.parent.rdi) hk.2.2,
    fun i hi => by rw [htb i hi, ← hum]; rfl, hframe, hk.mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.DeriveFailure`, which this module and modules that import it used -/

section

/-! # Zeroing the derived key and restoring registers on public domain rejection -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

theorem deriveFailure_ok {s : State} {B : Addr} {Z k q : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : pWorkspace ≤ Z) {p : Nat} (hkq : k = 3 * p + 2 * q) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B Field.out.offset = op)
    (hP : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p) (hK : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) :
    WP isa Generate.deriveFailure s fun t =>
      (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp 0 k ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h256 : 256 ≤ Z := Nat.le_trans (by decide) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
  unfold Generate.deriveFailure seqs
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, Core.field, hdi, fieldAddress,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ), hO, hP, hK]
    simp only [BitVec.ofNat_add_ofNat, hkq]
    congr 1
    omega_using []) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := k) (by omega_using [hk1]) (FailInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun t₂ hI => ?_)
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = k))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ k - j by omega_using [hj]) (by omega_using [hk']), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega_using [hk'])]
      exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega_using []], decide_eq_decide.mpr (by omega_using [hj])⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
        exact hI.bytes i (by omega_using [hi, hij])
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
      exact hI.frame x fun i hi => hx i (by omega_using [hi])
  -- The saved registers.
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hI.frame _ (fun j hj => scr_ne_out hsep (d := 8 * i) (i := b) (by omega_using [h256, hi, hb]) (by omega_using [hn]) j (by omega_using [hj])), hm₁]
  have k12 := k₁.trans hI.keep
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  rw [exit_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide),
      hw₂ 2 (by decide), hw₂ 3 (by decide), hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨?_, ?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [i2osp_zero]
    exact List.map_congr_left fun i hi => by rw [hm]; exact hI.bytes i (List.mem_range.mp hi)
  · rw [k₃.gpr (by decide), hI.keep.gpr (by decide), hax]
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x hx
    rw [hm, hI.frame x hx, hm₁]


end VG.Proof.Dsa.X86_64

end

end

/-! # Functional correctness of x86-64 DSA key derivation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The scratch derivation uses: the signer's layout and the derived y. -/
abbrev deriveExtent : Nat := derivedY + 384

structure DeriveInput extends ParametersInput where
  x : List Byte
  xLength : x.length = qLen

namespace DeriveInput

variable (p : DeriveInput)

abbrev outLen : Nat := 3 * p.pLen + 2 * p.qLen

def layout (original : State) (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.pb
  subgroup := Spec.Dsa.decodeBE p.qb
  pInverse := 0
  qInverse := 0
  fields := deriveFieldValues original (BitVec.ofNat 64 p.qLen) p.base p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := rfl

/-- The derived public value. -/
abbrev y : Nat := Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.x) (Spec.Dsa.decodeBE p.pb)

abbrev yb : List Byte := Spec.Dsa.encodeBE p.pLen p.y

end DeriveInput

structure DerivePre (p : DeriveInput) (s : State) : Prop where
  scratch : Scr s p.base deriveExtent
  stackRead : ∀ j, 1 ≤ j → j ≤ 2 → InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * j)) 8
  stackSeparate : ∀ j, 1 ≤ j → j ≤ 2 → ∀ i < 8,
    usedBytes ≤ ofs p.base (off (s.gpr .rsp) (8 * j) + BitVec.ofNat 64 i)
  qLength : word s.mem (s.gpr .rsp) 8 = BitVec.ofNat 64 p.qLen
  base : word s.mem (s.gpr .rsp) 16 = p.base
  pLength : s.gpr .r8 = BitVec.ofNat 64 p.pLen
  paramsSource : Src s p.base deriveExtent (s.gpr .rdx) p.params
  xSource : Src s p.base deriveExtent (s.gpr .r9) p.x
  outWrite : ∀ i < p.outLen, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i) 1
  outSeparate : ∀ i < p.outLen, deriveExtent ≤ ofs p.base (s.gpr .rdi + BitVec.ofNat 64 i)
  paramsOut : ∀ i < 2 * p.pLen + p.qLen, ∀ j < p.outLen,
    s.gpr .rdx + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  xOut : ∀ i < p.qLen, ∀ j < p.outLen, s.gpr .r9 + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem DerivePre.sources {p : DeriveInput} {original s : State} (h : DerivePre p original)
    (hm : InScr p.base deriveExtent original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base deriveExtent (original.gpr .rdx) p.pb ∧
    Src s p.base deriveExtent (original.gpr .rdx + original.gpr .r8) p.qb ∧
    Src s p.base deriveExtent (original.gpr .rdx + original.gpr .r8 + BitVec.ofNat 64 p.qLen) p.gb ∧
    Src s p.base deriveExtent (original.gpr .r9) p.x := by
  obtain hsrc := h.paramsSource.congrK hm hk
  refine ⟨source_take hsrc, ?_, ?_, h.xSource.congrK hm hk⟩
  · rw [h.pLength]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_arith)
  · rw [h.pLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_arith)

structure DeriveShapePost (p : DeriveInput) (original : State)
    (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) (s : State) : Prop where
  scratch : Scr s p.base deriveExtent
  rdi : s.gpr .rdi = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp).fields f
  branch : s.zf = some (!p.accepted)
  saved : ∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)
  frame : InScr p.base deriveExtent original.mem s.mem
  keep : Keep coreRegs original s

theorem deriveShape_ok {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (.seq (.block Generate.deriveEntry) Checks.domainShape) s0
      (DeriveShapePost p s0 h.pLength) := by
  obtain hsu : Scr s0 p.base usedBytes := scratch_prefix h.scratch (by decide) (by decide)
  refine WP.seq (WP.mono (deriveEntry_ok hsu rfl h.stackRead h.stackSeparate h.qLength h.base)
    fun s1 he => ?_)
  obtain hinside : InScr p.base deriveExtent s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _, _⟩ := h.sources hinside (he.keep.mono (by decide))
  obtain hp64 : p.pb.length < 2 ^ 64 := by
    rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  obtain hq64 : p.qb.length < 2 ^ 64 := by
    rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  refine WP.mono (domainShape_ok (n := 0) (hsu.congr he.keep.2.2) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.pbLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.qbLength]; rfl))
    (source_shrink hps (by decide)) (source_shrink hqs (by decide)) p.pPositive hp64 p.qPositive hq64
    rfl rfl (by decide) (he.fields .digestLen (by decide) (by decide)))
    fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  obtain hall := he.keep.trans hk
  obtain hft : InScr p.base deriveExtent s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.2.2, (hk.gpr (by decide)).trans he.base,
    he.shapeFields hf ?_ (by rw [hprefix]; rfl) hmask, hbranch,
    fun i hi => (shape_saved hf hi).trans (he.saved i hi), hinside.trans hft, hall.mono (by decide)⟩
  intro f h1 h2
  cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

/-- The output and frame of a derivation. -/
def DerivePost (p : DeriveInput) (original t : State) : Prop :=
  let res := Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x
  t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
  Spec.Rsa.bytesAt t.mem (original.gpr .rdi) p.outLen = res.getD (List.replicate p.outLen 0) ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  (∀ x, deriveExtent ≤ ofs p.base x → (∀ j < p.outLen, x ≠ original.gpr .rdi + BitVec.ofNat 64 j) →
    t.mem x = original.mem x) ∧
  Keep coreRegs original t

theorem DeriveInput.derive_eq (p : DeriveInput) :
    Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if p.accepted && (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb)
          (Spec.Dsa.decodeBE p.pb) = 1) &&
        (decide ((Spec.Dsa.decodeBE p.pb - 1) % Spec.Dsa.decodeBE p.qb = 0) &&
        (decide (1 < p.y ∧ p.y < Spec.Dsa.decodeBE p.pb) &&
        (decide (1 < Spec.Dsa.decodeBE p.gb ∧ Spec.Dsa.decodeBE p.gb < Spec.Dsa.decodeBE p.pb) &&
        (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < Spec.Dsa.decodeBE p.qb) && true)))))
      then some (p.params ++ p.yb ++ p.x) else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq p.lengths p.paramsLength p.xLength, ParametersInput.accepted,
    shapeAccepted_spec]
  rfl

theorem bytesAt_zero_list (mem : Mem) (O : Addr) (n : Nat)
    (h : ∀ i < n, mem (O + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt mem O n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  exact h i h1

theorem deriveRejected_ok {p : DeriveInput} {original s : State} (h : DerivePre p original)
    (hs : DeriveShapePost p original h.pLength s) (ha : p.accepted = false) :
    WP isa Generate.deriveFailure s (DerivePost p original) := by
  have hf := hs.fields
  obtain hq1 : 1 ≤ p.qLen := by have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  obtain hk31 : p.outLen < 2 ^ 31 := by
    have := p.lengths; unfold Spec.Dsa.lengthsValid at this; unfold DeriveInput.outLen; omega_arith
  refine WP.mono (deriveFailure_ok (k := p.outLen) (q := p.qLen) (p := p.pLen) hs.scratch hs.rdi (by decide) rfl
    (by unfold DeriveInput.outLen; omega_arith) hk31 (hf .out) (hf .pLen |>.trans h.pLength) (hf .qLen)
    (fun j hj => by rw [hs.keep.2.2]; exact h.outWrite j hj) h.outSeparate)
    fun t ⟨hbytes, hret, hsave, hframe, hk⟩ => ?_
  obtain hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x = none := by
    rw [p.derive_eq, ha, Bool.false_and]; rfl
  refine ⟨by rw [hret, hres]; rfl, ?_, fun i hi => (hsave i hi).trans (hs.saved i hi), ?_,
    (hs.keep.trans hk).mono (by decide)⟩
  · rw [hres, Option.getD_none]
    apply bytesAt_zero_list
    intro i hi
    have := congrArg (fun l => l[i]?) hbytes
    simp only [i2osp_zero, List.getElem?_map, List.getElem?_range hi, Option.map_some] at this
    exact Option.some.inj this
  · intro x hx hout
    exact (hframe x hout).trans (hs.frame x hx)

theorem OperandBytes.frame {L : ExecutionLayout} {s t : State} (hs : Ready L s) (ht : Ready L t)
    (hf : Outside L.base 128 (deriveExtent - 128) s.mem t.mem) (hk : Keep coreRegs s t)
    {a : Operand} {bytes : List Byte} (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (hb : OperandBytes s L.base deriveExtent a bytes) : OperandBytes t L.base deriveExtent a bytes := by
  refine ⟨(ht.fields a.length ha).trans ((hs.fields a.length ha).symm.trans hb.length), ?_⟩
  rw [hs.pointer_eq ht a.pointer hp]
  exact hb.source.congrK (InScr.of_outside hf (by decide)) hk

theorem OperandBytes.shrink {s : State} {B : Addr} {Z n : Nat} {a : Operand} {bs : List Byte}
    (h : OperandBytes s B Z a bs) (hn : n ≤ Z) : OperandBytes s B n a bs :=
  ⟨h.length, source_shrink h.source hn⟩

/-- What derivation computes before writing the key: x's range, y = g^x
copied past the signer's layout, and the signer's checks with that y. -/
theorem deriveBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hql : qb.length = L.qLen) (hxl : xb.length = L.qLen)
    (hqv : Spec.Dsa.decodeBE qb = L.subgroup) (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, Checks.signingKey Sq.mm M.mm]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (signingKeyAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
        (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && true)) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  intro y
  obtain ⟨hql1, hqu, hqp, hpu⟩ := L.widths
  obtain hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    obtain hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  obtain hend : t2 + L.pLen ≤ usedBytes := by unfold t2 usedBytes; omega_using [hp384]
  unfold seqs
  -- 0 < x < q
  refine WP.seq (WP.mono (readyRange_ok hr .q Core.privateScalar (by trivial) (hx.shrink (by decide)).active
    (by rw [hxl]; omega_using [hql1]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hf1 : Outside L.base 128 (deriveExtent - 128) s.mem s1.mem := h1.frame.mono (by decide) (by decide)
  obtain hg1 := hg.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq1 := hqb.frame hr h1.ready hf1 h1.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hx1 := hx.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.privateScalar])
  -- y = g^x mod p, at t2
  obtain step2 := readyPow_ok M Sq h1.ready .p hp hpo Core.generator Core.privateScalar (by trivial) (by trivial)
    (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active (by rw [hgl]; omega_using [hp384])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu]) t2 (by decide) hend
  obtain step2' : WP isa (Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) s1
      (CallResult L .p t2 y s1) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value] using step2
  refine WP.seq (WP.mono step2' fun s2 h2 => ?_)
  obtain hf2 : Outside L.base 128 (deriveExtent - 128) s1.mem s2.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  obtain hg2 := hg1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq2 := hq1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm2 := (h2.fields (by decide) hend .mask).trans h1.mask
  obtain hs2 : Scr s2 L.base deriveExtent := hs.congr (h1.keep.trans h2.keep).2.2
  -- y, copied past the signer's layout
  refine WP.seq (WP.mono (copyY_ok h2.ready hs2) fun s3 ⟨h3, hy3, hf3o, hk3⟩ => ?_)
  obtain hf3 : Outside L.base 128 (deriveExtent - 128) s2.mem s3.mem :=
    hf3o.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain hg3 := hg2.frame h2.ready h3 hf3 hk3 (by decide) (by simp [stablePointer, Core.generator])
  obtain hq3 := hq2.frame h2.ready h3 hf3 hk3 (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm3 : word s3.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    refine (hf3o.word (Or.inl (by decide)) (by decide)).trans ?_
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using hm2
  obtain hyb : ∀ i (hi : i < L.pLen), s3.mem (off L.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    rw [hy3 i hi]
    obtain hb := congrArg (fun l => l[i]?) h2.bytes
    simp only [ModulusSide.length, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at hb
    rw [List.getElem?_eq_getElem (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)] at hb
    exact Option.some.inj hb
  obtain hys : OperandBytes s3 L.base usedBytes Core.publicValue (Spec.Dsa.encodeBE L.pLen y) := by
    refine ⟨(h3.fields .pLen (by decide)).trans (by rw [VG.Proof.Dsa.encodeBE_length]; exact L.pLength), ?_⟩
    simp only [Core.publicValue, pointerValue, h3.fields .y (by decide), hy]
    refine ⟨fun i hi => ?_, fun i hi => hyb i (by rwa [VG.Proof.Dsa.encodeBE_length] at hi), fun i hi => ?_⟩
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [off_add]
      exact scr_byte_rd (hs.congr (h1.keep.trans (h2.keep.trans hk3)).2.2)
        (by unfold deriveExtent; omega_using [hi, hp384])
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [ofs_off _ (by have := hs.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
      exact Nat.le_add_right _ _
  -- the signer's checks of the domain and y
  refine WP.mono (signingKey_ok M Sq h3 hp hq hpo hqo hpf hqf (hg3.shrink (by decide)) hys (hq3.shrink (by decide))
    hgl (VG.Proof.Dsa.encodeBE_length _ _) hql hqv hm3) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  refine ⟨ht, hmt, fun i hi => (hft _ (Or.inr ?_)).trans (hyb i hi), ?_,
    (((h1.keep.trans h2.keep).trans hk3).trans hkt).mono (by decide)⟩
  · rw [ofs_off _ (by have := hs.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
    exact Nat.le_trans (by decide) (Nat.le_add_right _ _)
  · exact ((hf1.trans hf2).trans hf3).trans (hft.mono (by decide) (by decide))

theorem bytesAt_key (mem : Mem) (O : Addr) (l₁ l₂ l₃ : List Byte)
    (h₁ : ∀ i (hi : i < l₁.length), mem (O + BitVec.ofNat 64 i) = l₁[i])
    (h₂ : ∀ i (hi : i < l₂.length), mem (O + BitVec.ofNat 64 (l₁.length + i)) = l₂[i])
    (h₃ : ∀ i (hi : i < l₃.length), mem (O + BitVec.ofNat 64 (l₁.length + l₂.length + i)) = l₃[i]) :
    Spec.Rsa.bytesAt mem O (l₁.length + l₂.length + l₃.length) = l₁ ++ l₂ ++ l₃ := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt, Nat.add_assoc])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  by_cases a : i < l₁.length
  · rw [List.getElem_append_left (by simp only [List.length_append]; omega_arith), List.getElem_append_left a]
    exact h₁ i a
  by_cases b : i < l₁.length + l₂.length
  · rw [List.getElem_append_left (by simp only [List.length_append]; omega_arith),
      List.getElem_append_right (by omega_arith)]
    have := h₂ (i - l₁.length) (by omega_arith)
    rwa [show l₁.length + (i - l₁.length) = i by omega_arith] at this
  · rw [List.getElem_append_right (by simp only [List.length_append]; omega_arith)]
    have := h₃ (i - (l₁ ++ l₂).length) (by simp only [List.length_append]; omega_arith)
    simp only [List.length_append] at this ⊢
    rwa [show l₁.length + l₂.length + (i - (l₁.length + l₂.length)) = i by omega_arith] at this

structure DeriveOperands (L : ExecutionLayout) (p : DeriveInput) (s : State) : Prop where
  generator : OperandBytes s L.base deriveExtent Core.generator p.gb
  subgroup : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ p.qb
  scalar : OperandBytes s L.base deriveExtent Core.privateScalar p.x

def DeriveInitialized (p : DeriveInput) (original : State)
    (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp).withInverses pi qi) s ∧
    DeriveOperands ((p.layout original hp).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    (∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)) ∧
    InScr p.base deriveExtent original.mem s.mem ∧ Keep coreRegs original s

theorem deriveInitialize_ok {p : DeriveInput} {original st : State} (h : DerivePre p original)
    (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (DeriveInitialized p original h.pLength) := by
  let L := p.layout original h.pLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) (scratch_prefix hs.scratch (by decide) (by decide)) hs.rdi
    hs.fields (source_shrink hps (by decide)) (source_shrink hqs (by decide))
    p.pbLength p.qbLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  let L' := L.withInverses pi qi
  have hr' : Ready L' t := hr
  obtain hframe : InScr p.base deriveExtent original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  obtain hkeep := hs.keep.trans hk
  obtain ⟨_, hqs', hgs', hxs'⟩ := h.sources hframe (hkeep.mono (by decide))
  have operand (f len : Field) (hf : f ≠ .mask) (hl : len ≠ .mask) {bs : List Byte}
      (hsrc : Src t L'.base deriveExtent (L'.fields f) bs) (hlen : L'.fields len = BitVec.ofNat 64 bs.length) :
      OperandBytes t L'.base deriveExtent ⟨.input f, len⟩ bs := by
    refine ⟨(hr'.fields len hl).trans hlen, ?_⟩
    simpa only [pointerValue, hr'.fields f hf] using hsrc
  refine ⟨pi, qi, hr', ⟨operand .g .pLen (by decide) (by decide) hgs' (by rw [p.gbLength]; exact h.pLength),
    operand .q .qLen (by decide) (by decide) hqs' (by rw [p.qbLength]; rfl),
    operand .x .qLen (by decide) (by decide) hxs' (by rw [p.xLength]; rfl)⟩,
    hm.trans ((hs.fields .mask).trans (congrArg mask ha)),
    fun i hi => (hf.word (Or.inl (by omega_arith)) (by omega_arith)).trans (hs.saved i hi),
    hframe, hkeep.mono (by decide)⟩

theorem deriveSuccess_ok (M : Mont) (Sq : MontS) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey Sq.mm M.mm, Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  have hl := p.lengths
  unfold Spec.Dsa.lengthsValid at hl
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hsv, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.2.2
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, Checks.signingKey Sq.mm M.mm]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveBody_ok (L := L) M Sq hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.qbLength p.xLength rfl rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  obtain hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  obtain hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  obtain hsv' : Scr v p.base deriveExtent := h.scratch.congr hkeep'.2.2
  obtain ⟨_, _, _, hxs⟩ := h.sources hframe' hkeep'
  obtain hparams := h.paramsSource.congrK hframe' hkeep'
  set valid := signingKeyAccepted L p.gb p.yb
    (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true) with hvalid
  obtain hfields : KeyFields v p.base (original.gpr .rdi) (original.gpr .rdx) (off p.base derivedY)
      (original.gpr .r9) p.pLen p.qLen valid :=
    ⟨hv.fields .out (by decide), hv.fields .p (by decide), hv.fields .y (by decide),
      hv.fields .x (by decide), (hv.fields .pLen (by decide)).trans h.pLength,
      hv.fields .qLen (by decide), hmv⟩
  have hn := hsv'.nowrap
  obtain hp384 : p.pLen ≤ 384 := by omega_using [hl]
  obtain hpq : 0 < p.pLen ∧ 0 < p.qLen := by omega_using [hl]
  have hreg : v.rd = original.rd ∧ v.wr = original.wr := hkeep'.2
  unfold seqs
  refine WP.seq (WP.mono (writeKey_ok hsv' hv.parent.rdi (by decide) hfields hpq.1 hpq.2 (by omega_using [hl])
    ⟨fun i hi => hparams.rd i (by rw [p.paramsLength]; exact hi), h.paramsOut⟩
    ⟨fun i hi => by
      rw [off_add]; exact scr_byte_rd hsv' (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]),
     fun i hi j hj => scr_ne_out h.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]) (by omega_using [hn]) j hj⟩
    ⟨fun i hi => hxs.rd i (by rw [p.xLength]; exact hi), h.xOut⟩
    (fun i hi => by rw [hreg.2]; exact h.outWrite i hi))
    fun w ⟨hw₁, hw₂, hw₃, hwf, hkw⟩ => ?_)
  obtain hwv : ∀ d, d + 8 ≤ deriveExtent → word w.mem p.base d = word v.mem p.base d := fun d hd =>
    Mem.readW_congr fun b hb => hwf _ (scr_ne_out h.outSeparate (d := d) (i := b) (by omega_using [hd, hb]) (by omega_using [hn]))
  refine WP.mono (result_ok (hsv'.congr hkw.2.2) ((hkw.gpr (by decide)).trans hv.parent.rdi) (by decide)
    ((hwv _ (by decide)).trans hmv)) fun t ⟨hret, hsave, hmem, hkt⟩ => ?_
  obtain hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  obtain hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if valid then some (p.params ++ p.yb ++ p.x) else none := by
    rw [p.derive_eq, ha, Bool.true_and, hvalid]
    unfold signingKeyAccepted
    rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
    rfl
  obtain hlen : p.outLen = p.params.length + p.yb.length + p.x.length := by
    rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length, p.xLength]; unfold DeriveInput.outLen; omega_arith
  refine ⟨?_, ?_, fun i hi => (hsave i hi).trans ((hwv _ (by unfold deriveExtent derivedY usedBytes; omega_using [hi])).trans
      ((hfv.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (hsv i hi))), ?_,
    ((hkeep'.trans hkw).trans hkt).mono (by decide)⟩
  · rw [hret]
    change BitVec.ofNat 64 valid.toNat = _
    rw [hres]
    cases valid <;> rfl
  · rw [hmem, hres]
    cases hvb : valid
    · apply bytesAt_zero_list
      intro i hi
      by_cases h1 : i < 2 * p.pLen + p.qLen
      · rw [hw₁ i h1, hvb]; rfl
      by_cases h2 : i < 3 * p.pLen + p.qLen
      · have := hw₂ (i - (2 * p.pLen + p.qLen)) (by omega_arith)
        rw [show 2 * p.pLen + p.qLen + (i - (2 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
      · have := hw₃ (i - (3 * p.pLen + p.qLen)) (by unfold DeriveInput.outLen at hi; omega_arith)
        rw [show 3 * p.pLen + p.qLen + (i - (3 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
    · simp only [↓reduceIte, Option.getD_some]
      rw [hlen]
      apply bytesAt_key
      · intro i hi
        rw [p.paramsLength] at hi
        rw [hw₁ i hi, hvb]
        simp only [↓reduceIte]
        exact hparams.val i (by rw [p.paramsLength]; exact hi)
      · intro i hi
        rw [VG.Proof.Dsa.encodeBE_length] at hi
        rw [p.paramsLength, hw₂ i hi, hvb]
        simp only [↓reduceIte]
        exact hyv i hi
      · intro i hi
        rw [p.xLength] at hi
        rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length,
          show 2 * p.pLen + p.qLen + p.pLen = 3 * p.pLen + p.qLen by omega_arith, hw₃ i hi, hvb]
        simp only [↓reduceIte]
        exact hxs.val i (by rw [p.xLength]; exact hi)
  · intro x hx hout
    rw [hmem, hwf x hout]
    exact hframe' x hx

theorem deriveMain_ok (M : Mont) (Sq : MontS) {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (Generate.deriveKey Sq.mm M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64
