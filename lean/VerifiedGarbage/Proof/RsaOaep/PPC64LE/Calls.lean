module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Em
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base

/-!
# RSAES-OAEP encryption on PPC64LE: the calls of the streaming hash functions

Untrusted: everything here is checked by Lean. The calls of a hash
function's `init`, `update` and `finalize` (`HashOK.callInit_ok`, …) on the
streaming state at `S + oSt`, with the working space at `S + oW` and the
digest to `S + oDig`, from a state with `Base`: they keep it, the
callee-saved registers, and the bytes of our part of the working space
outside the ranges they write (`Same`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.Mgf1 (ifp ifn)

/-- Our part of the working space is as in `t` outside the ranges `rgs`. -/
def Same (S : Addr) (t t' : State) (rgs : List (Nat × Nat)) : Prop :=
  ∀ o < oRsa, (∀ p ∈ rgs, o < p.1 ∨ p.1 + p.2 ≤ o) → view t'.mem S o = view t.mem S o

theorem Same.refl (S : Addr) (t : State) (rgs : List (Nat × Nat)) : Same S t t rgs := fun _ _ _ => rfl

theorem Same.trans {S : Addr} {t₁ t₂ t₃ : State} {rgs : List (Nat × Nat)} (h₁ : Same S t₁ t₂ rgs)
    (h₂ : Same S t₂ t₃ rgs) : Same S t₁ t₃ rgs := fun o ho hr => (h₂ o ho hr).trans (h₁ o ho hr)

theorem Same.mono {S : Addr} {t t' : State} {rgs rgs' : List (Nat × Nat)} (h : Same S t t' rgs)
    (hs : ∀ p ∈ rgs, p ∈ rgs') : Same S t t' rgs' := fun o ho hr => h o ho fun p hp => hr p (hs p hp)

theorem Same.of_mem {S : Addr} {t t' : State} (h : t'.mem = t.mem) (rgs : List (Nat × Nat)) : Same S t t' rgs :=
  fun _ _ _ => by simp only [view, h]

/-- The offsets in our part of the working space. -/
theorem offs : oEm = 0 ∧ oSt = 1024 ∧ oDig = 1280 ∧ oCtr = 1344 ∧ oW = 1352 ∧ oRsa = 8192 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The sizes of a hash function's ranges in our part of the working space. -/
theorem hfits {H : Hash} (hH : HashOK H) : H.S ≤ 192 ∧ H.FD ≤ 64 ∧ H.W ≤ 1024 := by
  have := hH.dims.N; have := hH.dims.so; have := hH.dims.B; have := hH.hFD64
  simp only [Hash.S]; omega

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- What a callee writing ranges of our part of the working space and the
48 bytes below the frame keeps of it. -/
theorem same_of_frame {t t' : State} (hsp : t.sp = fb s) {rgs : List (Nat × Nat)}
    (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hf : Frame (rgs.map (fun p => (⟨off (S s) p.1, p.2⟩ : Region)) ++ [below t.sp 48]) t.mem t'.mem) :
    Same (S s) t t' rgs := fun o ho hr => by
  simp only [view]
  refine hf _ fun r hr' hc => ?_
  rcases List.mem_append.mp hr' with h' | h'
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h'
    have := hrg p hp
    rcases hr p hp with h₁ | h₁
    · exact sdis (s := s) (a := o) (n := 1) (b := p.1) (k := p.2) (.inl (by omega)) (by omega) (by omega) _
        (Region.contains_self _ _) hc
    · exact sdis (s := s) (a := o) (n := 1) (b := p.1) (k := p.2) (.inr (by omega)) (by omega) (by omega) _
        (Region.contains_self _ _) hc
  · rw [List.mem_singleton.mp h', hsp] at hc
    exact cR_dis P (o := o) (n := 1) (by omega) _ hc (Region.contains_self _ _)

theorem sp48 {t : State} (h : Base s t) : 48 ≤ t.sp.toNat := by
  rw [h.sp]; have := P.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes]; omega

/-- A call of the streaming `init` on the state at `S + oSt`. -/
theorem init_ok {H : Hash} (hH : HashOK H) {t : State} (h : Base s t) (h3 : t.gpr .r3 = off (S s) oSt) :
    WP isa H.callInit t fun t' => Base s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (S s) oSt) [] := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hc : Covers [⟨off (S s) oSt, H.S⟩] t.wr := by rw [h.wr]; exact sc_cov P (by omega)
  refine hH.callInit_ok h3 ⟨sp48 P h, by rw [h.sp]; exact cR_dis P (by omega)⟩ (Covers.right hc) hc
    fun t' hrd hwr hsp hf hg hr => ⟨h.call P (R := [⟨off (S s) oSt, H.S⟩]) (fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact sc_in (by omega)) hrd hwr hsp hf hg, hg,
      same_of_frame P h.sp (rgs := [(oSt, H.S)]) (by simp; omega) hf, hr⟩

/-- A call of the streaming `update` on the state at `S + oSt`, with the
`len` bytes at `dat`. -/
theorem upd_ok {H : Hash} (hH : HashOK H) {t : State} (h : Base s t) {dat : Addr} {len : Nat}
    (h3 : t.gpr .r3 = off (S s) oSt) (h5 : t.gpr .r5 = dat) (h6 : (t.gpr .r6).toNat = len)
    (h7 : t.gpr .r7 = off (S s) oW) (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr))
    (hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, H.S⟩) (hd₂ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oW, H.W⟩)
    (hd₃ : (cR s).Disjoint ⟨dat, len⟩) :
    WP isa H.callUpd t fun t' => Base s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oW, H.W)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → t.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem dat len) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hc : Covers [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oW, H.W⟩] t.wr := by
    rw [h.wr]; exact Covers.pair (sc_cov P (by omega)) (sc_cov P (by omega))
  refine hH.callUpd_ok h3 h5 h6 h7 (sdis (.inl (by omega)) (by omega) (by omega)) hd₁ hd₂ (sp48 P h)
    (by rw [h.sp]; exact cR_dis P (by omega)) (by rw [h.sp]; exact hd₃) (by rw [h.sp]; exact cR_dis P (by omega))
    (Covers.append_left hdc (Covers.right hc)) hc fun t' hrd hwr hsp hf hg hr => ⟨h.call P
      (R := [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oW, H.W⟩]) (fun r hr' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · exact sc_in (by omega)
        · exact sc_in (by omega)) hrd hwr hsp hf hg, hg,
      same_of_frame P h.sp (rgs := [(oSt, H.S), (oW, H.W)]) (by simp; omega) hf, hr⟩

/-- A call of the streaming `finalize` on the state at `S + oSt`, its digest
to `S + oDig`. -/
theorem fin_ok {H : Hash} (hH : HashOK H) {t : State} (h : Base s t) (h3 : t.gpr .r3 = off (S s) oSt)
    (h5 : t.gpr .r5 = off (S s) oDig) (h6 : t.gpr .r6 = off (S s) oW) :
    WP isa H.callFin t fun t' => Base s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → m.length < 2 ^ 64 → t.gpr .r4 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.FD = hH.fh m := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hc : Covers [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.FD⟩, ⟨off (S s) oW, H.W⟩] t.wr := by
    rw [h.wr]; exact (sc_cov P (by omega)).cons (Covers.pair (sc_cov P (by omega)) (sc_cov P (by omega)))
  refine hH.callFin_ok h3 h5 h6 (sdis (.inl (by omega)) (by omega) (by omega))
    (sdis (.inl (by omega)) (by omega) (by omega)) (sdis (.inl (by omega)) (by omega) (by omega)) (sp48 P h)
    (by rw [h.sp]; exact cR_dis P (by omega)) (by rw [h.sp]; exact cR_dis P (by omega))
    (by rw [h.sp]; exact cR_dis P (by omega)) (Covers.right hc) hc fun t' hrd hwr hsp hf hg hr => ⟨h.call P
      (R := [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.FD⟩, ⟨off (S s) oW, H.W⟩]) (fun r hr' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl
        · exact sc_in (by omega)
        · exact sc_in (by omega)
        · exact sc_in (by omega)) hrd hwr hsp hf hg, hg,
      same_of_frame P h.sp (rgs := [(oSt, H.S), (oDig, H.FD), (oW, H.W)]) (by simp; omega) hf, hr⟩

end

end VG.Proof.RsaOaep.PPC64LE
