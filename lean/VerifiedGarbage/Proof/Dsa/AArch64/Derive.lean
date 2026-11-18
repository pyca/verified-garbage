module

public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution

/-! ### `Dsa.AArch64.DeriveCopy`, which this module and modules that import it used -/

section

/-! # Copying the derived y past the signer's layout

Writes above the workspaces keep them, and the fields, ready. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

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
    (hdi : t.gpr .x0 = L.base) (hwr : t.wr = s.wr) : Ready L t := by
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

theorem scr_byte_rd {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (hd : d < Z) :
    InRegions (s.rd ++ s.wr) (off B d) 1 :=
  let ⟨r, hr, hc⟩ := hs.region (d := d) (n := 1) (by omega_using [hd]) (by decide)
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem off_add (B : Addr) (d i : Nat) : off B d + BitVec.ofNat 64 i = off B (d + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The scalar workspace's register setup for copying y. -/
theorem copyHead_ok {L : ExecutionLayout} {s : State} (h : Ready L s) :
    WP isa (.block [movi .x3 t2, .add .x .x1 .x0 .x3,
      movi .x3 derivedY, .add .x .x2 .x0 .x3, Core.field .x9 .pLen,
      movi .x8 0, .subImm .x .x8 .x8 1]) s fun t =>
      t.gpr .x1 = off L.base t2 ∧ t.gpr .x2 = off L.base derivedY ∧
      t.gpr .x9 = BitVec.ofNat 64 L.pLen ∧ t.gpr .x8 = mask true ∧ t.mem = s.mem ∧
      Keep [.x1, .x2, .x3, .x9, .x8] s t := by
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x9, .x8] (Q := fun t =>
      t.gpr .x1 = off L.base t2 ∧ t.gpr .x2 = off L.base derivedY ∧
      t.gpr .x9 = BitVec.ofNat 64 L.pLen ∧ t.gpr .x8 = mask true ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, hk⟩
  brun [Core.field, field_enc .pLen, fieldAddress, h.parent.x0,
    h.scratch.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 (by decide)),
    h.fields .pLen (by decide), L.pLength]
  exact ⟨rfl, rfl⟩

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
    rw [hku.rd, hku.wr, off_add]
    exact scr_byte_rd hs (by rw [ht2, hdy]; omega_using [hi, hp384])
  have hw : ∀ i < L.pLen, InRegions u.wr (off L.base derivedY + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hku.wr, off_add]
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
  refine ⟨h.of_outside hframe (by decide) ((hk.gpr .x0 (by decide)).trans h.parent.x0) hk.wr,
    fun i hi => by rw [htb i hi, ← hum]; rfl, hframe, hk.mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.DeriveWrite`, which this module and modules that import it used -/

section

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
  omega_using []

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
  omega_using []

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
  omega_using []

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
    fun i hi => by rw [shift]; exact hw _ (by omega_using [hd, hi])
  have hapart (src : Addr) (n d m : Nat) (hd : d + m ≤ 3 * p + 2 * q)
      (h : ∀ i < n, ∀ j < 3 * p + 2 * q, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j) :
      ∀ i < n, ∀ j < m, src + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 d + BitVec.ofNat 64 j :=
    fun i hi j hj => by rw [shift]; exact h i hi _ (by omega_using [hd, hj])
  have hregs : ∀ r ∈ [Reg.x1, .x2, .x9, .x3], r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x10 := by
    decide
  unfold Generate.writeKey seqs
  have hRk : ∀ t t', KeyRegs t O Y X p q → Keep [.x3, .x1, .x2, .x9] t t' → KeyRegs t' O Y X p q :=
    fun t t' h hk => h.keep hk (by decide)
  -- p||q||g
  apply WP.assoc
  refine WP.seq (WP.mono (copyPiece_ok (n := 2 * p + q) (rs := keyRegs) hRk (keyHead_ok hs hdi hZ hf)
    (by omega_using [hp]) (by omega_using [hk])
    hP.1 (fun i hi => by simpa using hrange 0 (2 * p + q) (by omega_using []) i hi)
    (fun i hi j hj => by simpa using hapart P _ 0 (2 * p + q) (by omega_using []) hP.2 i hi j hj)) fun s₁ h₁ => ?_)
  obtain ⟨hb₁, hfr₁, h8₁, hR₁, k₁⟩ := h₁
  have hfr₁' : ∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → s₁.mem x = s.mem x :=
    fun x hx => hfr₁ x fun i hi => hx i (by omega_using [hi])
  -- y
  apply WP.assoc
  refine WP.seq (WP.mono (copyPiece_ok (n := p) (rs := [.x1, .x2, .x9]) hRk (keyHead₂_ok hR₁ h8₁) hp (by omega_using [hk])
    (fun i hi => by rw [k₁.rd, k₁.wr]; exact hY.1 i hi)
    (fun i hi => by rw [k₁.wr]; exact hrange (2 * p + q) p (by omega_using []) i hi)
    (hapart Y p (2 * p + q) p (by omega_using []) hY.2)) fun s₂ h₂ => ?_)
  obtain ⟨hb₂, hfr₂, h8₂, hR₂, k₂⟩ := h₂
  have hfr₂' : ∀ x, (∀ i < 3 * p + 2 * q, x ≠ O + BitVec.ofNat 64 i) → s₂.mem x = s.mem x :=
    fun x hx => (hfr₂ x fun i hi => by rw [shift]; exact hx _ (by omega_using [hi])).trans (hfr₁' x hx)
  have k₁₂ := k₁.trans k₂
  -- x
  refine WP.mono (copyPiece_ok (n := q) (rs := [.x1, .x2, .x9]) hRk (keyHead₃_ok hR₂ h8₂) hq (by omega_using [hk])
    (fun i hi => by rw [k₁₂.rd, k₁₂.wr]; exact hX.1 i hi)
    (fun i hi => by rw [k₁₂.wr]; exact hrange (3 * p + q) q (by omega_using []) i hi)
    (hapart X q (3 * p + q) q (by omega_using []) hX.2)) fun t ⟨hb₃, hfr₃, _, _, k₃⟩ => ?_
  have hne (a b : Nat) (ha : a < 3 * p + 2 * q) (hb : b < 3 * p + 2 * q) (h : a ≠ b) :
      O + BitVec.ofNat 64 a ≠ O + BitVec.ofNat 64 b := out_ne (by omega_using [hk, ha]) (by omega_using [hk, hb]) h
  refine ⟨?_, ?_, ?_, ?_, ((k₁₂.trans k₃).mono (by decide))⟩
  · intro i hi
    rw [hfr₃ _ fun j hj => by rw [shift]; exact hne _ _ (by omega_using [hi]) (by omega_using [hj]) (by omega_using [hi]),
      hfr₂ _ fun j hj => by rw [shift]; exact hne _ _ (by omega_using [hi]) (by omega_using [hj]) (by omega_using [hi])]
    simpa using hb₁ i hi
  · intro i hi
    rw [hfr₃ _ fun j hj => by rw [shift]; exact hne _ _ (by omega_using [hi]) (by omega_using [hj]) (by omega_using [hi]), ← shift, hb₂ i hi,
      hfr₁' _ fun j hj => hY.2 i hi j hj]
  · intro i hi
    rw [← shift, hb₃ i hi, hfr₂' _ fun j hj => hX.2 i hi j hj]
  · intro x hx
    exact (hfr₃ x fun i hi => by rw [shift]; exact hx _ (by omega_using [hi])).trans (hfr₂' x hx)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.DeriveEntry`, which only this module used -/

section

/-! # AAPCS64 argument capture for DSA key derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def deriveFieldValues (original : State) (qlen B : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .x2
  | .q => original.gpr .x2 + original.gpr .x4
  | .g => original.gpr .x2 + original.gpr .x4 + qlen
  | .y => B + BitVec.ofNat 64 derivedY
  | .x => original.gpr .x5
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => original.gpr .x0
  | .pLen => original.gpr .x4
  | .qLen => qlen
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

abbrev deriveFields := Generate.deriveFields

def deriveFieldMem (mem : Mem) (B out p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW
    (off B Field.digest.offset) (0#64)).writeW (off B Field.digestLen.offset) (0#64)).writeW
    (off B Field.out.offset) out).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem deriveFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block deriveFields) s fun t =>
      t.mem = deriveFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold deriveFields Generate.deriveFields
  brun [SignVerify.initial, h11, fieldAddress,
    field_enc .signature, field_enc .nonce, field_enc .digest, field_enc .digestLen,
    field_enc .out, field_enc .p, field_enc .pLen, field_enc .qLen,
    hw .signature, hw .nonce, hw .digest, hw .digestLen, hw .out, hw .p, hw .pLen, hw .qLen]
  rfl

theorem deriveTail_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block [SignVerify.initial .x5 .x, movi .x3 derivedY,
      .add .x .x3 .x11 .x3, SignVerify.initial .x3 .y]) s fun t =>
      t.mem = (s.mem.writeW (off B Field.x.offset) (s.gpr .x5)).writeW (off B Field.y.offset)
        (B + BitVec.ofNat 64 derivedY) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  brun [SignVerify.initial, h11, fieldAddress, field_enc .x, field_enc .y, hw .x, hw .y]
  rfl

theorem deriveMoveScratch_ok (s : State) :
    WP isa (.block [mov .x11 .x7]) s fun t =>
      t.gpr .x11 = s.gpr .x7 ∧ t.mem = s.mem ∧ Keep [.x11] s t := by
  refine WP.mono (WP.keep [.x11] (Q := fun t => t.gpr .x11 = s.gpr .x7 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  brun []

theorem deriveEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h7 : s0.gpr .x7 = B) :
    WP isa (.block Generate.deriveEntry) s0 (KeygenEntryPost s0 B (deriveFieldValues s0 (s0.gpr .x6) B true)) := by
  unfold Generate.deriveEntry
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (deriveMoveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h7] at h11
  rw [WP.block_append_iff]
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  refine WP.mono (deriveFields_ok (hs.congr hk1.wr) h11 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x4 (by decide), hreg .x6 (by decide)] at hmem3
  have hk123 := hk1.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (deriveFieldMem s1.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x6)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .x2) (pl := s0.gpr .x4) (ql := s0.gpr .x6) (hs.congr hk123.wr) h113 (by decide)
    ((hw3 .p).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .x11 = B := (hk4.gpr .x11 (by decide)).trans h113
  have h5 : s4.gpr .x5 = s0.gpr .x5 := hk1234.gpr .x5 (by decide)
  refine WP.mono (deriveTail_ok (hs.congr hk1234.wr) h114 (by decide)) fun t ⟨hmem5, hk5⟩ => ?_
  rw [h5] at hmem5
  refine ⟨(hk5.gpr .x0 (by decide)).trans hdi4, ?_, ?_,
    ((hk1234.trans hk5).mono (by decide))⟩
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [deriveFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, deriveFieldValues]; try rfl)
  · intro x hx
    have hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega_using [hx]
    rw [hmem5, hmem4, hmem3]
    simp only [deriveFieldMem, keyPointerMem, field_write_frame _ B _ _ x hx']
    rw [hmem1]

end VG.Proof.Dsa.AArch64

end

end

/-! # Functional correctness of AArch64 DSA key derivation -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/DeriveFailure.lean`, which only this module imported.
section

/-! # Zeroing a derived key after domain rejection -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

open VG.Impl.Dsa.Layout

theorem deriveFailure_ok {s : State} {B : Addr} {Z k q : Nat} {op : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : pWorkspace ≤ Z) {p : Nat} (hkq : k = 3 * p + 2 * q) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B Field.out.offset = op) (hK : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hP : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa Generate.deriveFailure s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧
      t.gpr .x0 = 0 ∧ (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep coreRegs s t := by
  have hn := hs.nowrap
  unfold Generate.deriveFailure seqs
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [h0, Core.field, field_enc .out, field_enc .pLen, field_enc .qLen, fieldAddress,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ), hO, hP, hK]
    simp only [BitVec.ofNat_add_ofNat, hkq]
    congr 1
    omega) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega) (by omega) (BInv s₁ op)
    (fun j hj t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨?_, hx, fun x hx' => ?_, ((k₁.trans hI.keep).trans k₃).mono
      (by decide)⟩
  · rw [bytesAt_eq, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hm]
    exact hI.bytes i (List.mem_range.mp hi)
  · rw [hm, hI.frame x hx', hm₁]

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The scratch derivation uses: the signer's layout and the derived y. -/
abbrev deriveExtent : Nat := derivedY + 384

structure DeriveInput extends ParametersInput where
  x : List Byte
  xLength : x.length = qLen

namespace DeriveInput

variable (p : DeriveInput)

abbrev outLen : Nat := 3 * p.pLen + 2 * p.qLen

def layout (original : State) (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) : ExecutionLayout where
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
  qLength : s.gpr .x6 = BitVec.ofNat 64 p.qLen
  base : s.gpr .x7 = p.base
  pLength : s.gpr .x4 = BitVec.ofNat 64 p.pLen
  paramsSource : Src s p.base deriveExtent (s.gpr .x2) p.params
  xSource : Src s p.base deriveExtent (s.gpr .x5) p.x
  outWrite : ∀ i < p.outLen, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 i) 1
  outSeparate : ∀ i < p.outLen, deriveExtent ≤ ofs p.base (s.gpr .x0 + BitVec.ofNat 64 i)
  paramsOut : ∀ i < 2 * p.pLen + p.qLen, ∀ j < p.outLen,
    s.gpr .x2 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j
  xOut : ∀ i < p.qLen, ∀ j < p.outLen, s.gpr .x5 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j

theorem DerivePre.sources {p : DeriveInput} {original s : State} (h : DerivePre p original)
    (hm : InScr p.base deriveExtent original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base deriveExtent (original.gpr .x2) p.pb ∧
    Src s p.base deriveExtent (original.gpr .x2 + original.gpr .x4) p.qb ∧
    Src s p.base deriveExtent (original.gpr .x2 + original.gpr .x4 + BitVec.ofNat 64 p.qLen) p.gb ∧
    Src s p.base deriveExtent (original.gpr .x5) p.x := by
  have hsrc := h.paramsSource.congrK hm hk
  refine ⟨source_take hsrc, ?_, ?_, h.xSource.congrK hm hk⟩
  · rw [h.pLength]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_arith)
  · rw [h.pLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_arith)

structure DeriveShapePost (p : DeriveInput) (original : State)
    (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) (s : State) : Prop where
  scratch : Scr s p.base deriveExtent
  x0 : s.gpr .x0 = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp).fields f
  branch : (s.gpr .x3 == (0#64)) = !p.accepted
  frame : InScr p.base deriveExtent original.mem s.mem
  keep : Keep coreRegs original s

theorem deriveShape_ok {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (.seq (.block Generate.deriveEntry) Checks.domainShape) s0
      (DeriveShapePost p s0 h.pLength) := by
  have hsu : Scr s0 p.base usedBytes := scratch_prefix h.scratch (by decide) (by decide)
  refine WP.seq (WP.mono (deriveEntry_ok hsu h.base)
    fun s1 he => ?_)
  rw [h.qLength] at he
  have hinside : InScr p.base deriveExtent s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _, _⟩ := h.sources hinside (he.keep.mono (by decide))
  have hp64 : p.pb.length < 2 ^ 64 := by
    rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  have hq64 : p.qb.length < 2 ^ 64 := by
    rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  refine WP.mono (domainShape_ok (hsu.congr he.keep.wr) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.pbLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.qbLength]; rfl))
    (source_shrink hps (by decide)) (source_shrink hqs (by decide)) p.pPositive hp64 p.qPositive hq64
    rfl rfl (by decide) (he.fields .digestLen (by decide) (by decide)))
    fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base deriveExtent s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.wr, (hk.gpr .x0 (by decide)).trans he.base,
    he.shapeFields hf ?_ (by rw [hprefix]; rfl) hmask, hbranch,
    hinside.trans hft, hall.mono (by decide)⟩
  intro f h1 h2
  cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

/-- The output and frame of a derivation. -/
def DerivePost (p : DeriveInput) (original t : State) : Prop :=
  let res := Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
  Spec.Rsa.bytesAt t.mem (original.gpr .x0) p.outLen = res.getD (List.replicate p.outLen 0) ∧
  (∀ x, deriveExtent ≤ ofs p.base x → (∀ j < p.outLen, x ≠ original.gpr .x0 + BitVec.ofNat 64 j) →
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
  have hq1 : 1 ≤ p.qLen := by have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  have hk31 : p.outLen < 2 ^ 31 := by
    have := p.lengths; unfold Spec.Dsa.lengthsValid at this; unfold DeriveInput.outLen; omega_arith
  refine WP.mono (deriveFailure_ok (k := p.outLen) (q := p.qLen) (p := p.pLen) hs.scratch hs.x0 (by decide) rfl
    (by unfold DeriveInput.outLen; omega_arith) hk31 (hf .out) (hf .qLen) (hf .pLen |>.trans h.pLength)
    (fun j hj => by rw [hs.keep.wr]; exact h.outWrite j hj))
    fun t ⟨hbytes, hret, hframe, hk⟩ => ?_
  have hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x = none := by
    rw [p.derive_eq, ha, Bool.false_and]; rfl
  refine ⟨by rw [hret, hres]; rfl, ?_, ?_,
    (hs.keep.trans hk).mono (by decide)⟩
  · rw [hres, Option.getD_none]
    exact hbytes
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
    (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp).withInverses pi qi) s ∧
    DeriveOperands ((p.layout original hp).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base deriveExtent original.mem s.mem ∧ Keep coreRegs original s

theorem deriveInitialize_ok {p : DeriveInput} {original st : State} (h : DerivePre p original)
    (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (DeriveInitialized p original h.pLength) := by
  let L := p.layout original h.pLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) (scratch_prefix hs.scratch (by decide) (by decide)) hs.x0
    hs.fields (source_shrink hps (by decide)) (source_shrink hqs (by decide))
    p.pbLength p.qbLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  let L' := L.withInverses pi qi
  have hr' : Ready L' t := hr
  have hframe : InScr p.base deriveExtent original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  have hkeep := hs.keep.trans hk
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
    hframe, hkeep.mono (by decide)⟩

end VG.Proof.Dsa.AArch64
