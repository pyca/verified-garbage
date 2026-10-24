module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: a witness's octets

`load_ok`: the next `8 w` octets of `rand` (at `R + u`, `u` in header word
`hUsed`, `R` in `hRand`) into array 4, most significant first, and `hUsed`
advanced. `seg_eq`: those octets are `seg r u (8 w)` of `rand`'s octets.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (load)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hRand hUsed hK)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot)

/-- The octets at an offset of `rand`. -/
theorem seg_eq (m : Mem) (R : Addr) {n u L : Nat} (h : u + L ≤ n) :
    VG.Proof.RsaKeyGen.seg (Spec.Rsa.bytesAt m R n) u L = Spec.Rsa.bytesAt m (off R u) L := by
  apply List.ext_getElem
  · simp [VG.Proof.RsaKeyGen.seg, Spec.Rsa.bytesAt]; omega
  · intro i h1 h2
    simp only [VG.Proof.RsaKeyGen.seg, Spec.Rsa.bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range, off]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The registers `load` writes. -/
def ldRegs : List Reg := [.r0, .r3, .r6, .r10, .r12, .r14, .r15, .r16, .r17]

theorem load_ok {s : State} {B R : Addr} {Z w u : Nat} (h : Env s B Z w) (hR : word s.mem B (8 * hRand) = R)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 u) (hk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w))
    (hN : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off R (u + i)) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off R (u + i) ≠ x) :
    WP isa load s fun t =>
      (val32 t.mem B (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)) ∧
        word t.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w) ∧ Env t B Z w ∧
        Outs B [(8 * hUsed, 8), (slot w 4, 8 * w)] s.mem t.mem) ∧ Keep ldRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  unfold load
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r6, .r12] (Q := fun t => t.mem = s.mem.writeW (off B (8 * hUsed))
      (BitVec.ofNat 64 (u + 8 * w)) ∧ t.gpr .r12 = off R u ∧ t.gpr .r6 = BitVec.ofNat 64 (8 * w)) ?_ (by decide))
    fun t₁ ⟨⟨m₁, a12, a6⟩, k₁⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK] at hR hu hk ⊢
    prun [h.h31, hs.ld (d := 136) (n := 8) (by omega), hs.ld (d := 152) (n := 8) (by omega),
      hs.ld (d := 216) (n := 8) (by omega), hs.st (d := 152) (n := 8) (by omega), hR, hu, hk]
    rw [BitVec.ofNat_add_ofNat]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k₁.gpr _ (by decide)).trans h.h10)
    ((k₁.gpr _ (by decide)).trans h.h29) 4) fun t₂ ⟨⟨a10, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (loadN_ok (hs.congr k12.wr) (dA := slot w 4) (N := off R u) a10
    (by rw [k₂.gpr _ (by decide), a12]; exact (BitVec.add_zero _).symm)
    ((k₂.gpr _ (by decide)).trans a6) (by rw [k12.gpr _ (by decide)]; exact h.h11) (by omega) (Nat.le_refl _)
    (by omega) (by rw [slot_lin]; omega) (by rw [slot_lin]; omega)
    (fun i hi => by
      rw [k12.rd, k12.wr]; show InRegions _ (off R u + BitVec.ofNat 64 i) 1; rw [off_add]; exact hN i hi)
    (fun i hi x hx => by show off R u + BitVec.ofNat 64 i ≠ x; rw [off_add]; exact hsep i hi x hx))
    fun v ⟨vv, vout, kv⟩ => ?_)
  have k1v := k12.trans kv
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = v.mem) (by
    prun [(k1v.gpr .r31 (by decide)).trans h.h31, VG.Impl.Bignum.hdrBytes]
    show B + BitVec.ofNat 64 256 = B + BitVec.ofNat 64 (slot w 0)
    rw [slot0]) (by decide)) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
  have K := k1v.trans kt
  rw [m₂, m₁] at vv vout
  have hrm : Spec.Rsa.bytesAt (s.mem.writeW (off B (8 * hUsed)) (BitVec.ofNat 64 (u + 8 * w))) (off R u) (8 * w) =
      Spec.Rsa.bytesAt s.mem (off R u) (8 * w) := by
    apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
    intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    refine writeW_outside s.mem B (d := 8 * hUsed) _ (by simp only [hUsed]; omega) _ ?_
    by_contra hc
    exact hsep i h1 (off R u + BitVec.ofNat 64 i) (by simp only [hUsed, ofs] at hc ⊢; omega) (off_add R u i).symm
  refine ⟨⟨by rw [tm, vv, hrm], ?_, ⟨hs.congr K.wr, t10, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, ?_⟩,
    K.mono (by simp [ldRegs])⟩
  · rw [tm, vout.word (by simp only [hUsed]; rw [slot_lin]; omega) (by simp only [hUsed]; omega)]
    exact word_writeW_self _ _ _ _
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [tm, vout x hx.2, writeW_outside s.mem B (d := 8 * hUsed) _ (by simp only [hUsed]; omega) x hx.1]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
