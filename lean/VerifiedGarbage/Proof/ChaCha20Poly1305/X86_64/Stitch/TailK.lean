module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Chunk
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.StoreRow

/-!
# ChaCha20 and Poly1305 together (x86-64): `tailK`'s rounds

`Stitch.tailKMainS` is a chunk (`chunkMain_ok`) but for its output: the eight
blocks' keystream stored at `kA buf` (`finishK_ok`) rather than XORed into
the data, while the blocks of a schedule at `rsi` are absorbed
(`tailKMainS_ok`): the 512 bytes of the last chunk, the 448 before the first
(`pre`, `tailKMain_ok`), or the first blocks of the bytes left after the
chunks (`tailKO`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds Consts Incs stR bufR slotsR dR5 plus
  setup_ok W2_frame incs_frame hiR_slots slotsR_sub)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The eight blocks of keystream from the state at `st` stored at `kA buf`,
while the `tot` blocks of a schedule at `q` are absorbed. -/
theorem tailKMainS_ok (vl : Bool) {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot) (h10 : fb 10 = tot)
    (htot : tot ≤ 32) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hkr : kR buf ∈ s.wr)
    (hin : ∀ off n, off + n ≤ 16 * tot → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsb : (stR st).Disjoint (bufR buf)) (dsk : (stR st).Disjoint (kR buf))
    (dbk : (bufR buf).Disjoint (kR buf)) (dqs : (⟨q, 16 * tot⟩ : Region).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa (tailKMainS vl bl fb) s fun s' =>
        (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * tot))) s' ∧
        Frame [slotsR buf, kR buf] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold tailKMainS
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  have q₁ : bytesAt s₁.mem q (16 * tot) = bytesAt s.mem q (16 * tot) := by
    have := bytes_frame F₁ dqs (by omega) (j := 0) (n := 16 * tot) (by omega)
    simpa using this
  have h0 : SRS fb buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      rw [sc.first0, show 16 * 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl,
        VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (sroundsForS_ok hk (by rw [g₁, hrsi]) (by rw [rd₁, wr₁]; exact hin) vl sc (Nat.le_refl _)
    htot (by rw [g₁, hrcx]) (by rw [wr₁]; exact hb) c₁.m8 ⟨c₁.lo16, c₁.hi16⟩ dqs h0) fun s₂ h₂ => ?_)
  have F₂ : Frame [slotsR buf] s.mem s₂.mem := F₁.trans h₂.frame
  have hh₂ : Holds buf false (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j)) s₂ := by
    intro k hk' l q' hl hq
    have e := h₂.holds k hk' l q' hl hq
    split
    · rename_i hreg
      simp only [hreg, ite_true] at e
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw] using e
    · rename_i hreg
      simp only [hreg] at e
      exact e
  have gk : ∀ r, r ∉ absorbRegs → s₂.gpr r = s.gpr r := fun r hr => by rw [h₂.gpr r hr, g₁]
  have wr₂ : s₂.wr = s.wr := by rw [h₂.wr, wr₁]
  have inc₂ : Incs buf s₂.mem := incs_frame hc.inc F₂ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.mono (finishK_ok hh₂ (st := st) (by rw [gk _ (by decide), hrdi]) (by rw [gk _ (by decide), hrcx])
    (by rw [wr₂]; exact hst) (by rw [wr₂]; exact hb) (by rw [wr₂]; exact hkr) inc₂ dsb dsk dbk)
    fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have hS : stateAt s₂.mem st = stateAt s.mem st :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using dsb.sub_right (slotsR_sub buf))
  refine ⟨fun k hk' => by rw [d₃ k hk', hS], ?_, (F₂.mono (by simp)).trans f₃,
    fun r hr => by rw [g₃, gk r hr], by rw [rd₃, h₂.rd, rd₁], by rw [wr₃, wr₂]⟩
  have a₂ := h₂.acc
  rw [h10, q₁] at a₂
  exact ⟨by rw [g₃]; exact a₂.r8, by rw [g₃]; exact a₂.r9, by rw [g₃]; exact a₂.r10, by rw [g₃]; exact a₂.h2,
    by simp only [hval, g₃]; exact a₂.val⟩

/-- The eight blocks of keystream from the state at `st` stored at `kA buf`,
while the 512 bytes at `q` (the last chunk), or (`pre`) the 448 there before
the first chunk, are absorbed. -/
theorem tailKMain_ok (vl pre : Bool) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hkr : kR buf ∈ s.wr)
    (hin : ∀ off n, off + n ≤ 16 * total pre → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsb : (stR st).Disjoint (bufR buf)) (dsk : (stR st).Disjoint (kR buf))
    (dbk : (bufR buf).Disjoint (kR buf)) (dqs : (⟨q, 16 * total pre⟩ : Region).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa (tailKMain vl pre) s fun s' =>
        (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * total pre))) s' ∧
        Frame [slotsR buf, kR buf] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  tailKMainS_ok vl (schedOk_pre pre) (firstBlock_ten pre) (total_le pre) hk hrdi hrcx hrsi hst hb hkr hin hc
    dsb dsk dbk dqs hacc

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
