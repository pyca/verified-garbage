module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptStackWord

/-! # The disjoint state, digest, PRF and hash-working regions in scratch -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

namespace Geometry

theorem Valid.scratchMinimum {g : Geometry} (h : g.Valid) : 8448 ≤ 8 * g.scratchLength := by
  have space := h.space
  have lower := h.minLength
  simp only [Spec.Rsa.scratchWords] at space
  omega

theorem Valid.scratchSub {g : Geometry} (h : g.Valid) {d n : Nat} (fit : d + n ≤ 8448) :
    (g.scratch d n).Sub g.workspaceRegion :=
  Offset.sub_base _ (by have := h.scratchMinimum; omega)

theorem Valid.scratchAddress {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < 8448) :
    byteAddr (g.workspace + BitVec.ofNat 32 d) = (g.scratch d 0).base :=
  byteAddr_add (by have := h.scratchMinimum; have := h.workspaceFit; omega)

theorem Valid.scratchNat {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < 8448) :
    (g.workspace + BitVec.ofNat 32 d).toNat = g.workspace.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
    Nat.mod_eq_of_lt (by have := h.scratchMinimum; have := h.workspaceFit; omega)]

theorem Valid.scratchFit {g : Geometry} (h : g.Valid) {d n : Nat}
    (fit : d + n ≤ 8448) (start : d < 8448) :
    (g.workspace + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  rw [h.scratchNat start]
  have := h.workspaceFit
  have := h.scratchMinimum
  omega

end Geometry

theorem Context.scratchWrite {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {d n : Nat} (fit : d + n ≤ 8448) : InRegions s.wr (g.scratch d n).base n :=
  CallLay.inRegions_sub (off := d) h.workspaceWrite
    (by have := h.valid.scratchMinimum; omega) (by have := h.valid.workspaceFit; omega)

theorem Context.scratchRead {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {d n : Nat} (fit : d + n ≤ 8448) :
    InRegions (s.rd ++ s.wr) (g.scratch d n).base n := by
  obtain ⟨r, hr, hc⟩ := h.scratchWrite fit
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem scratchDisjoint (g : Geometry) {d n e k : Nat} (apart : d + n ≤ e ∨ e + k ≤ d)
    (fit : d + n ≤ 8448) (otherFit : e + k ≤ 8448) :
    (g.scratch d n).Disjoint (g.scratch e k) :=
  Offset.disjoint _ apart (by omega) (by omega)

end VG.Proof.RsaPkcs1Enc.X86.Dec
