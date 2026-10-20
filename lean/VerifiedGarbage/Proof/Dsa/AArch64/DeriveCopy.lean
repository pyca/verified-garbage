module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  have he : ∀ e, e + 8 ≤ slot wx 8 → word mem' (off B o) e = word mem (off B o) e := by
    intro e he
    rw [word_off, word_off]
    exact hf.word (Or.inl (by omega)) (by omega)
  refine ⟨child.header.of_words (fun i hi => he _ (by omega)), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega))]
    exact child.modulus
  · rw [he _ (by omega)]
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
    hf.word (Or.inl (by have : 256 ≤ activeBytes := (by decide); omega)) (by omega)
  have hg := h.parent
  refine ⟨⟨hg.scr.congr hwr, hdi, ⟨(he _ (by decide)).trans hg.hdr.hw, (he _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (he _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩,
    h.scratch.congr hwr, ?_, child_of_outside h.pChild hf (by omega) (by have : activeBytes < 2 ^ 64 := (by decide); omega),
    child_of_outside h.qChild hf (by omega) (by have : activeBytes < 2 ^ 64 := (by decide); omega)⟩
  intro f hm
  exact (hf.word (Or.inl (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by
    have : 368 ≤ activeBytes := (by decide)
    omega))) (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))).trans (h.fields f hm)

theorem scr_byte_rd {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (hd : d < Z) :
    InRegions (s.rd ++ s.wr) (off B d) 1 :=
  let ⟨r, hr, hc⟩ := hs.region (d := d) (n := 1) (by omega) (by decide)
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
