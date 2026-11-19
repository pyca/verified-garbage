module

import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Dsa.AArch64.Result
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
import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.Call
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSpec
import VerifiedGarbage.Proof.Dsa.AArch64.SignBody
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution

/-! ### `Dsa.AArch64.Derive`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.AArch64.SharedCallCT`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.VerifyingABI`, which the modules that import this one used -/

section

/-! # The shared verification contract as machine-level resources -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem dsaVerifyStackArgs (s : State) : List.map (stackArg s) (List.range 2) =
    [stackArg s 0, stackArg s 1] := rfl

structure VerifyingABI (s : State) : Prop where
  stackBound : s.sp.toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
    ⟨s.gpr .x6, (s.gpr .x7).toNat⟩, ⟨stackArgAddr s 0, 16⟩]
  wr : s.wr = [⟨stackArg s 0, (stackArg s 1).toNat * 8⟩]
  keyScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  signatureScratch : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  digestScratch : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  scratchArgs : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩
  keyBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  signatureBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  digestBound : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  keyLength : (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat + (s.gpr .x3).toNat
  signatureLength : (s.gpr .x5).toNat = 2 * (s.gpr .x3).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x2).toNat ≤ (stackArg s 1).toNat

def VerifyingABI.input {s : State} (h : VerifyingABI s) : VerifyingInput where
  base := stackArg s 0
  digestPointer := s.gpr .x6
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  signature := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  digest := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  signatureLength := (bytesAt_length _ _ _).trans h.signatureLength
  digestBound := by rw [bytesAt_length]; exact (s.gpr .x7).isLt

theorem VerifyingABI.used {s : State} (h : VerifyingABI s) : usedBytes ≤ (stackArg s 1).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

end VG.Proof.Dsa.AArch64

end

end

/-! # The shared exponentiation's call is constant time in the secret exponent -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Proof.Dsa.AArch64

/-- The call's public data, and the public exponent's. -/
structure SCallPublic extends Call3Public where
  qp : Addr
  qb : List Byte
  qlen : qb.length = bytes.len
  wide : 8 ≤ bytes.x.wx
  tiles : bytes.x.wx % 8 = 0

abbrev SCallPublic.body (p : SCallPublic) : SPub :=
  { p.toPowerCallPublic with qp := p.qp, qb := p.qb, qlen := p.qlen, wide := p.wide, tiles := p.tiles }

def SCallPre (a b output : Operand) (p : SCallPublic) (s : State) : Prop :=
  Call3Pre a b output p.toCall3Public s ∧ p.x.o = pWorkspace ∧
  word s.mem p.x.B Field.q.offset = p.qp ∧ Src s p.x.B p.x.Z p.qp p.qb

/-- The call up to its return to the parent workspace. -/
theorem sharedCall_ct (M : Mont) {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (SCallPre a b output))
      (.seq (.block (callHead a b output pWorkspace)) (.seq (SharedPower.power M.mm) (seqs Core.finish)))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (p : SCallPublic) s => SPre p.body s ∧ FinishPre p.result s)
    (two_map SCallPublic.toCall3Public (fun _ _ h => h.1) (callHead_ct hT)) ?_) ?_
  · intro p s ⟨h, heq, hq, hqs⟩
    rw [← heq]
    refine WP.mono (callHead_run ha hb ho h) fun t ⟨⟨hpre, hfin⟩, hf, hk⟩ => ?_
    have hqo : Field.q.offset = 264 := rfl
    have hz : 176 ≤ p.x.Z := Nat.le_trans (by decide) p.extent
    exact ⟨⟨hpre, (hf.word_eq (fun r hr => by
        simp only [argumentRanges, List.mem_singleton] at hr; subst hr; right; omega_using [hqo])
        (by omega_using [hqo, hz])).trans hq, arguments_source hf hk hz hqs⟩, hfin⟩
  refine RelCT.seq (two_post (Ψ := fun (p : SCallPublic) s => FinishPre p.result s)
    (two_map SCallPublic.body (fun _ _ h => h.1) (power_ct M)) ?_)
    (two_map (fun p : SCallPublic => p.result) (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hq, hqs⟩, hf⟩
  exact WP.mono (power_ok M hc p.wide p.width48 p.tiles p.fits p.upper p.greater p.odd
    hm.modulus hm.inverse hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
    hep hel he (helen ▸ p.expPositive) (helen ▸ p.expLimit) hq hqs (p.qlen.trans helen.symm))
    fun t ⟨hct, _, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

/-- The whole call: the bases' and the secret exponent's bytes do not show
in what it leaks. -/
theorem sharedPow_ct (M : Mont) {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (SCallPre a b output)) (SharedPower.pow M.mm a b output) (fun _ _ => True) := by
  unfold SharedPower.pow
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun (p : SCallPublic) s => s.gpr .x0 = p.x.B) (sharedCall_ct M ha hb ho hT) ?_) ?_)
  · intro p s ⟨⟨hg, child, ⟨ba, bb, has, hbs, hbl, hel⟩, hp, hep, hop, hol, hout, hprefix⟩, heq, hq, hqs⟩
    have hlo := p.childLow
    have hhi := p.childHigh
    rw [heq] at hlo hhi child
    refine WP.mono (powCall_ok M hg child p.extent hlo hhi p.wide p.width48 p.tiles p.fits p.upper p.greater
      p.odd a b output ha hb ho has hbs (hq ▸ hqs) (p.qlen.trans hel.symm) (hbl ▸ p.basePositive)
      (hbl ▸ p.baseFits) (hel ▸ p.expPositive) (hel ▸ p.expLimit) hol p.outputPositive p.outputBound
      p.outputWidth (hop ▸ hout) (hop ▸ hprefix)) fun t h => h.1.1.x0
  · simp only [seqs]
    exact x0_ct (fun p : SCallPublic => p.x.B) (fun _ _ h => h) (by unfold Checks.accumulate; taint_decide)

/-! ## In DSA's execution context -/

/-- The call's public data in DSA's execution context: the domain's `q` is
public, of the secret exponent's length. -/
structure ReadySharedPublic (d : Nat) extends ReadyCallPublic .p d where
  qb : List Byte
  qlen : qb.length = exponentLen

theorem pWide (L : ExecutionLayout) : 8 ≤ L.pWords ∧ L.pWords % 8 = 0 := by
  rcases L.lengths with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [ExecutionLayout.pWords, h1] <;> decide

def ReadySharedPublic.call {d : Nat} (p : ReadySharedPublic d) (a b : Operand) : SCallPublic :=
  { p.toReadyCallPublic.call a b with
    qp := p.layout.fields .q, qb := p.qb, qlen := p.qlen, wide := (pWide p.layout).1, tiles := (pWide p.layout).2 }

def ReadySharedPre (d : Nat) (a b : Operand) (p : ReadySharedPublic d) (s : State) : Prop :=
  ReadyCallPre .p d a b p.toReadyCallPublic s ∧ Src s p.layout.base activeBytes (p.layout.fields .q) p.qb

theorem readySharedPow_ct (M : Mont) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer) (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b ⟨.local d, .pLen⟩ pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (ReadySharedPre d a b)) (SharedPower.pow M.mm a b ⟨.local d, .pLen⟩) (fun _ _ => True) :=
  two_map (fun p : ReadySharedPublic d => p.call a b)
    (fun _ _ h => ⟨readyCall_pre hpa hpb h.1, rfl, h.1.1.fields .q (by decide), h.2⟩)
    (sharedPow_ct M ha hb hd hT)

end VG.Proof.Dsa.AArch64.SharedPower

end

end

/-! # Functional correctness of AArch64 DSA key derivation

`Generate.deriveKey` computes y = g^x and checks `g^q mod p = 1` in one
pass over both exponents (`SharedPower.pow`). `Generate.deriveChecked` is
it without that check: for a domain whose check has succeeded, the
remaining checks of the signer accept exactly what the full ones do. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The signer's checks of g and y but `g^q = 1`, as `signingKeyAccepted`. -/
def prefixAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid))

theorem keyPrefix_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (seqs (Checks.publicPrefix M.mm)) s0 fun s6 =>
      Ready L s6 ∧ word s6.mem L.base Field.mask.offset = mask (prefixAccepted L gb yb valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s6.mem ∧ Keep coreRegs s0 s6 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Checks.publicPrefix seqs
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  have hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega)
    t (by decide) ht) fun s3 h3 => ?_)
  have hg3 := h3.external (by decide) ht hg2
  have hq3 := h3.external (by decide) ht hq2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  have step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 16; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega)] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hg4 := h4.external (by decide) hu hg3
  have hq4 := h4.external (by decide) hu hq3
  have hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 16; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_)
  have hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  have hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  have hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega)
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_
  refine ⟨h6.ready, (h6.fields (by decide) hqm .mask).trans hm5, ?_, ?_⟩
  · exact ((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans
      (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans (h6.scheduleFrame (by decide) hqm)
  · exact (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).trans h6.keep).mono (by decide)

/-- After y = g^x at `t2`: y copied past the signer's layout, and the
signer's checks of the domain and that y but `g^q = 1`. -/
theorem deriveCopyPrefix_ok (M : Mont) {L : ExecutionLayout} {s2 : State} (h2 : Ready L s2)
    (hs2 : Scr s2 L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb : List Byte}
    (hg2 : OperandBytes s2 L.base deriveExtent Core.generator gb)
    (hq2 : OperandBytes s2 L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hy : L.fields .y = off L.base derivedY) {y : Nat}
    (hb2 : ∀ i (hi : i < L.pLen), s2.mem (off L.base t2 + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi))
    {v : Bool} (hm2 : word s2.mem L.base Field.mask.offset = mask v) :
    WP isa (seqs [Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s2 fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y) v) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s2.mem t.mem ∧ Keep coreRegs s2 t := by
  obtain hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    obtain hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  unfold seqs
  -- y, copied past the signer's layout
  refine WP.seq (WP.mono (copyY_ok h2 hs2) fun s3 ⟨h3, hy3, hf3o, hk3⟩ => ?_)
  obtain hf3 : Outside L.base 128 (deriveExtent - 128) s2.mem s3.mem :=
    hf3o.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain hg3 := hg2.frame h2 h3 hf3 hk3 (by decide) (by simp [stablePointer, Core.generator])
  obtain hq3 := hq2.frame h2 h3 hf3 hk3 (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm3 : word s3.mem L.base Field.mask.offset = mask v :=
    (hf3o.word (Or.inl (by decide)) (by decide)).trans hm2
  obtain hyb : ∀ i (hi : i < L.pLen), s3.mem (off L.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    rw [hy3 i hi]
    exact hb2 i hi
  obtain hys : OperandBytes s3 L.base usedBytes Core.publicValue (Spec.Dsa.encodeBE L.pLen y) := by
    refine ⟨(h3.fields .pLen (by decide)).trans (by rw [VG.Proof.Dsa.encodeBE_length]; exact L.pLength), ?_⟩
    simp only [Core.publicValue, pointerValue, h3.fields .y (by decide), hy]
    refine ⟨fun i hi => ?_, fun i hi => hyb i (by rwa [VG.Proof.Dsa.encodeBE_length] at hi), fun i hi => ?_⟩
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [off_add]
      exact scr_byte_rd (hs2.congr hk3.wr)
        (by unfold deriveExtent; omega_using [hi, hp384])
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [ofs_off _ (by have := hs2.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
      exact Nat.le_add_right _ _
  -- the signer's checks of the domain and y
  refine WP.mono (keyPrefix_ok M h3 hp hq hpo hqo hpf hqf (hg3.shrink (by decide)) hys (hq3.shrink (by decide))
    hgl (VG.Proof.Dsa.encodeBE_length _ _) hm3) fun t ⟨ht, hmt, hft, hkt⟩ => ?_
  refine ⟨ht, hmt, fun i hi => (hft _ (Or.inr ?_)).trans (hyb i hi), ?_, (hk3.trans hkt).mono (by decide)⟩
  · rw [ofs_off _ (by have := hs2.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
    exact Nat.le_trans (by decide) (Nat.le_add_right _ _)
  · exact hf3.trans (hft.mono (by decide) (by decide))


/-- What domain-checked derivation computes before writing the key: x's
range, y = g^x copied past the signer's layout, and the signer's checks with
that y but `g^q = 1`. -/
theorem deriveCheckedBody_ok (M : Mont) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hxl : xb.length = L.qLen) (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
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
  obtain step2 := readyPow_ok M h1.ready .p hp hpo Core.generator Core.privateScalar (by trivial) (by trivial)
    (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active (by rw [hgl]; omega_using [hp384])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu]) t2 (by decide) hend
  obtain step2' : WP isa (Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) s1
      (CallResult L .p t2 y s1) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value] using step2
  refine WP.seq (WP.mono step2' fun s2 h2 => ?_)
  obtain hf2 : Outside L.base 128 (deriveExtent - 128) s1.mem s2.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  obtain hg2 := hg1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq2 := hq1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm2 := (h2.fields (by decide) hend .mask).trans h1.mask
  obtain hs2 : Scr s2 L.base deriveExtent := hs.congr (h1.keep.trans h2.keep).wr
  obtain hb2 : ∀ i (hi : i < L.pLen), s2.mem (off L.base t2 + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    obtain hb := congrArg (fun l => l[i]?) h2.bytes
    simp only [ModulusSide.length, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at hb
    rw [List.getElem?_eq_getElem (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)] at hb
    exact Option.some.inj hb
  obtain hm2' : word s2.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using hm2
  refine WP.mono (deriveCopyPrefix_ok M h2.ready hs2 hp hq hpo hqo hpf hqf hg2 hq2 hgl hy hb2 hm2')
    fun t ⟨ht, hmt, hyt, hft, hkt⟩ => ?_
  exact ⟨ht, hmt, hyt, (hf1.trans hf2).trans hft, ((h1.keep.trans h2.keep).trans hkt).mono (by decide)⟩

/-- The key written out, or zeros, for the acceptance mask `valid` the
checks left, and y past the signer's layout. -/
theorem deriveOutput_ok {p : DeriveInput} {original v : State} (h : DerivePre p original) (pi qi : BitVec 64)
    {valid : Bool} (hv : Ready ((p.layout original h.pLength).withInverses pi qi) v)
    (hmv : word v.mem p.base Field.mask.offset = mask valid)
    (hyv : ∀ i (hi : i < p.pLen), v.mem (off p.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE p.pLen (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.x)
        (Spec.Dsa.decodeBE p.pb)))[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi))
    (hframe' : InScr p.base deriveExtent original.mem v.mem) (hkeep' : Keep coreRegs original v)
    (hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if valid then some (p.params ++ p.yb ++ p.x) else none) :
    WP isa (seqs [Generate.writeKey, .block SignVerify.result]) v (DerivePost p original) := by
  have hl := p.lengths
  unfold Spec.Dsa.lengthsValid at hl
  obtain hsv' : Scr v p.base deriveExtent := h.scratch.congr hkeep'.wr
  obtain ⟨_, _, _, hxs⟩ := h.sources hframe' hkeep'
  obtain hparams := h.paramsSource.congrK hframe' hkeep'
  obtain hfields : KeyFields v p.base (original.gpr .x0) (original.gpr .x2) (off p.base derivedY)
      (original.gpr .x5) p.pLen p.qLen valid :=
    ⟨hv.fields .out (by decide), hv.fields .p (by decide), hv.fields .y (by decide),
      hv.fields .x (by decide), (hv.fields .pLen (by decide)).trans h.pLength,
      hv.fields .qLen (by decide), hmv⟩
  have hn := hsv'.nowrap
  obtain hp384 : p.pLen ≤ 384 := by omega_using [hl]
  obtain hpq : 0 < p.pLen ∧ 0 < p.qLen := by omega_using [hl]
  obtain hreg : v.rd = original.rd ∧ v.wr = original.wr := ⟨hkeep'.rd, hkeep'.wr⟩
  unfold seqs
  refine WP.seq (WP.mono (writeKey_ok hsv' hv.parent.x0 (by decide) hfields hpq.1 hpq.2 (by omega_using [hl])
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
  refine WP.mono (result_ok (hsv'.congr hkw.wr) ((hkw.gpr .x0 (by decide)).trans hv.parent.x0) (by decide)
    ((hwv _ (by decide)).trans hmv)) fun t ⟨hret, hmem, hkt⟩ => ?_
  obtain hlen : p.outLen = p.params.length + p.yb.length + p.x.length := by
    rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length, p.xLength]; unfold DeriveInput.outLen; omega_arith
  refine ⟨?_, ?_, ?_,
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


theorem deriveCheckedSuccess_ok (M : Mont) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true)
    (hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.wr
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveCheckedBody_ok (L := L) M hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.xLength rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  obtain hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  obtain hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  have hmv' : word v.mem p.base Field.mask.offset = mask (prefixAccepted L p.gb p.yb
      (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true)) := hmv
  refine deriveOutput_ok h pi qi hv hmv' hyv hframe' hkeep' ?_
  obtain hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  obtain hg : Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb) (Spec.Dsa.decodeBE p.pb) = 1 := by
    rw [p.check_eq, ha, Bool.true_and] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1
  rw [p.derive_eq, ha, Bool.true_and, decide_eq_true hg, Bool.true_and]
  unfold prefixAccepted
  rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
  rfl

/-- What derivation computes before writing the key: x's range, y = g^x
with whether `g^q = 1` (one pass over both exponents), y copied past the
signer's layout, and the signer's other checks with that y. -/
theorem deriveBody_ok (M : Mont) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hql : qb.length = L.qLen) (hxl : xb.length = L.qLen)
    (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
        (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE qb) L.modulus = 1) &&
          (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && true))) ∧
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
  obtain hm1 : word s1.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using h1.mask
  -- y = g^x mod p, at t2, and whether g^q mod p = 1
  refine WP.seq (WP.mono (SharedPower.readySharedPow_ok M h1.ready hp hpo Core.generator Core.privateScalar
    (by trivial) (by trivial) (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active
    (hq1.shrink (by decide)).active.source (hql.trans hxl.symm) (by rw [hgl]; omega_using [hp384])
    (by rw [hgl]) (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu])
    t2 (by decide) hend hm1) fun s2 ⟨u, h2, h2c⟩ => ?_)
  obtain hfu : Outside L.base 128 (deriveExtent - 128) s1.mem u.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  obtain hf2 : Outside L.base 128 (deriveExtent - 128) u.mem s2.mem := h2c.frame.mono (by decide) (by decide)
  obtain hg2 := (hg1.frame h1.ready h2.ready hfu h2.keep (by decide) (by simp [stablePointer, Core.generator])).frame
    h2.ready h2c.ready hf2 h2c.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq2 := (hq1.frame h1.ready h2.ready hfu h2.keep (by decide) (by change Field.q ≠ .mask; decide)).frame
    h2.ready h2c.ready hf2 h2c.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hs2 : Scr s2 L.base deriveExtent := hs.congr ((h1.keep.trans h2.keep).trans h2c.keep).wr
  obtain hout := h2c.preserve h2.ready (Nat.le_refl _) (by change Field.pLen ≠ .mask; decide) (by trivial)
    (h2.output (by decide) hend)
  obtain hb2 : ∀ i (hi : i < L.pLen), s2.mem (off L.base t2 + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) :=
    fun i hi => hout.source.val i (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)
  refine WP.mono (deriveCopyPrefix_ok M h2c.ready hs2 hp hq hpo hqo hpf hqf hg2 hq2 hgl hy hb2 h2c.mask)
    fun t ⟨ht, hmt, hyt, hft, hkt⟩ => ?_
  exact ⟨ht, hmt, hyt, ((hf1.trans hfu).trans hf2).trans hft,
    (((h1.keep.trans h2.keep).trans h2c.keep).trans hkt).mono (by decide)⟩

theorem and_rotate (g a b c r : Bool) : (g && (a && (b && (c && r)))) = (a && (b && (c && (g && r)))) := by
  cases g <;> cases a <;> cases b <;> cases c <;> rfl

theorem deriveSuccess_ok (M : Mont) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.wr
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveBody_ok (L := L) M hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.qbLength p.xLength rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  obtain hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  obtain hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  have hmv' : word v.mem p.base Field.mask.offset = mask (prefixAccepted L p.gb p.yb
      (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb) L.modulus = 1) &&
        (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true))) := hmv
  refine deriveOutput_ok h pi qi hv hmv' hyv hframe' hkeep' ?_
  obtain hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  rw [p.derive_eq, ha, Bool.true_and, and_rotate]
  unfold prefixAccepted
  rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
  rfl

/-- Key derivation: the checks of the domain and the key, `g^q = 1` among
them, and the key written out. -/
theorem deriveMain_ok (M : Mont) {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (Generate.deriveKey M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

theorem deriveCheckedMain_ok (M : Mont) {p : DeriveInput} {s0 : State} (h : DerivePre p s0)
    (hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params = true) :
    WP isa (Generate.deriveChecked M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveCheckedSuccess_ok M h hs ha hc)
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

end VG.Proof.Dsa.AArch64
