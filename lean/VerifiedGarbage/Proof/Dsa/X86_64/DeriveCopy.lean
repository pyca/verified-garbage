module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Proof.Dsa.X86_64.Execution
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut

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
    (hdi : t.gpr .rdi = L.base) (hwr : t.wr = s.wr) : Ready L t := by
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

theorem minusOne_mask : BitVec.signExtend 64 (-1 : BitVec 32) = mask true := by decide

theorem scr_byte_rd {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (hd : d < Z) :
    InRegions (s.rd ++ s.wr) (off B d) 1 :=
  let ⟨r, hr, hc⟩ := hs.region (d := d) (n := 1) (by omega) (by decide)
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
