module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: the invariant across a round

`St.call`: `St` survives the shared round, which changes the working space
only where its `Keeps` allows (none of the argument words) and memory
outside it only on the stack below `sp`, apart from the tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

/-- A header word the round keeps. -/
theorem keeps_hdr {m m' : Mem} {B : Addr} {n w i : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B n w m m') (hi : i < 32)
    (hk : i ≠ 1 ∧ i ≠ 23 ∧ i ≠ 26 ∧ i ≠ 29 ∧ i ≠ 30) (hn : 256 ≤ 8 * n) :
    word m' B (8 * i) = word m B (8 * i) :=
  keeps_word h (by omega_arith) fun j h1 h2 => by
    simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;> omega_arith

theorem St.call {p : PP} {s t : State} {w : Nat} (h : St p s)
    (hk : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact p.B p.n w s.mem t.mem)
    (hf : Frame [⟨p.B, p.Z⟩, below p.sp 176] s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.sp = s.sp) (h31 : t.gpr .r31 = p.B) (hw : slot w 28 + saveBytes ≤ p.Z) (h2 : t.gpr .r2 = s.gpr .r2) : St p t := by
  have hn := h.dims.n
  have e : ∀ {i : Nat}, i < 32 → i ≠ 1 ∧ i ≠ 23 ∧ i ≠ 26 ∧ i ≠ 29 ∧ i ≠ 30 →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun hi hk' =>
    keeps_hdr hk hi hk' (by simp only [PP.L] at hn; omega_arith)
  have ha := h.args
  refine ⟨h.scr.congr hwr, h31, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, h.bufs.sepR, ?_, ?_, h.bufs.scrO.congr hwr,
    h.bufs.sepO, h.bufs.scrU.congr hwr, h.bufs.sepU, h.bufs.stkR, h.bufs.stkO, h.bufs.stkU, h.bufs.dOU⟩, h.dims,
    by rw [hwr]; exact h.ws, hsp.trans h.sp, h.stk, h.stkB, fun i hi => ?_, h2.trans h.r2⟩
  · rw [e (by decide) (by decide)]; exact ha.wsLen
  · rw [e (by decide) (by decide)]; exact ha.out
  · rw [e (by decide) (by decide)]; exact ha.len
  · rw [e (by decide) (by decide)]; exact ha.usedP
  · rw [e (by decide) (by decide)]; exact ha.bits
  · rw [e (by decide) (by decide)]; exact ha.gen
  · rw [e (by decide) (by decide)]; exact ha.rand
  · rw [e (by decide) (by decide)]; exact ha.rlen
  · rw [hrd, hwr]; exact h.bufs.rdR
  · refine Eq.trans ?_ h.bufs.bR
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf _ fun r hr => ?_
    have hi' : i < p.r.length := List.mem_range.mp hi
    have hc : (⟨p.rp, p.r.length⟩ : Region).Contains (p.rp + BitVec.ofNat 64 i) 1 := by
      have := h.dims.rl
      have e0 := VG.Proof.Mont.ofs_off0 p.rp (d := i) (by omega_arith)
      simp only [VG.Proof.Mont.ofs, VG.Proof.Mont.off] at e0
      simp only [Region.Contains]; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc'
      have := h.bufs.sepR i hi' (p.rp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains] at hc'; simp only [ofs]; omega_arith)
      exact this rfl
    · exact fun hc' => h.bufs.stkR _ hc' hc
  · refine Eq.trans ?_ h.bufs.bO
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf _ fun r hr => ?_
    have hi' : i < p.L := List.mem_range.mp hi
    have hnw := h.bufs.scrO.nowrap
    have ho : ofs p.op (p.op + BitVec.ofNat 64 i) = i := by simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
    have hc : (⟨p.op, p.L⟩ : Region).Contains (p.op + BitVec.ofNat 64 i) 1 := by
      simp only [Region.Contains]; simp only [ofs] at ho; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc'
      have := h.bufs.sepO _ (by rw [ho]; exact hi')
      simp only [Region.Contains, ofs] at hc' this; omega_arith
    · exact fun hc' => h.bufs.stkO _ hc' hc

  · have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
    have := es 2; have := es 3; have := es 5; have := es 6; have := es 8; have := es 11; have := es 27
    have := es 28
    simp only [PP.Z, saveBytes] at hw
    refine (keeps_word hk (by simp only [saveBytes]; omega_arith) fun j h1 h2 => ?_).trans (h.save i hi)
    simp only [Kept, saveBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1 ⊢
    and_intros <;> omega_arith

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
