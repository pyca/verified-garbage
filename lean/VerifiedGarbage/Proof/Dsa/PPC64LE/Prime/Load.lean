module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Entry
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# DSA's probable-prime test on PPC64LE: the working space and the candidate

`env_of`: after the entry, the registers and the working space at
`B = ws + keyOff` are those of the Montgomery arithmetic (`Env`). `loadC_ok`:
the candidate's `bits / 8` big-endian bytes at `ws` into array 0
(`loadN_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off Outside slot)
open VG.Proof.MillerRabin.PPC64LE (Env arr)

/-- The working space's base. -/
abbrev wsB (σ : State) : Addr := σ.gpr .r3 + BitVec.ofNat 64 keyOff

/-- The working space is writable and does not wrap. -/
theorem scr_of {bits : Nat} {σ s : State} (h : CIn bits σ) (hwr : s.wr = σ.wr) :
    Scr s (wsB σ) (8 * keyWords bits) := by
  have hsz := h.size
  have hfw := h.fw
  refine ⟨⟨σ.gpr .r3, keyOff, (σ.gpr .r4).toNat * 8, by rw [hwr, h.wr]; exact List.mem_cons_self, rfl,
    by omega, by omega⟩, ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((σ.gpr .r3).toNat + keyOff % 2 ^ 64) (2 ^ 64)
  simp only [keyOff] at *
  omega

/-- After the entry, the Montgomery arithmetic's registers. -/
theorem env_of {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    Env s (wsB σ) (8 * keyWords bits) (words bits) :=
  ⟨scr_of h ep.wr, by
    rw [ep.regs.r10]; show _ = σ.gpr .r3 + BitVec.ofNat 64 keyOff + BitVec.ofNat 64 (slot (words bits) 0)
    rw [Offset.add_add]; simp only [slot, Nat.zero_mul, Nat.add_zero], ep.regs.r29, ep.regs.r11, ep.regs.r31, hs.w4,
    by have := hs.w48; omega, by rw [hs.key]; simp only [slot, hdrBytes]; omega⟩

/-- The candidate's bytes lie below the working space. -/
theorem cand_sep {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < 384) {x : Addr}
    (hx : VG.Proof.Bignum.ofs (wsB σ) x < 8 * keyWords bits) : σ.gpr .r3 + BitVec.ofNat 64 i ≠ x := by
  rintro rfl
  have hsz := h.size
  have hfw := h.fw
  simp only [VG.Proof.Bignum.ofs, wsB, keyOff] at hx hsz
  have : (σ.gpr .r3 + BitVec.ofNat 64 i - (σ.gpr .r3 + BitVec.ofNat 64 552)).toNat = 2 ^ 64 - 552 + i := by
    bv_omega
  omega

/-- The candidate's bytes are unchanged by the entry. -/
theorem cand_keep {bits : Nat} {σ s : State} (ep : EntryPost bits σ s) {n : Nat} (hn : n ≤ 384) :
    Spec.Rsa.bytesAt s.mem (σ.gpr .r3) n = Spec.Rsa.bytesAt σ.mem (σ.gpr .r3) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine ep.frame _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [Region.Contains, Offset.add_sub_add_left] <;> intro hc
  · exact Offset.not_lt_sub_ofNat (d := saveOff) (n := 168) (k := i) (Or.inl (by simp only [saveOff]; omega))
      (by omega) (by decide) (by decide) (by omega)
  · exact Offset.not_lt_sub_ofNat (d := keyOff) (n := 256) (k := i) (Or.inl (by simp only [keyOff]; omega))
      (by omega) (by decide) (by decide) (by omega)

/-- The candidate into array 0. -/
theorem loadC_ok {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    WP isa (loadC bits) s fun t =>
      (arr t.mem (wsB σ) (words bits) 0 = Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .r3) ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s.mem t.mem) ∧
      Keep [.r0, .r6, .r12, .r14, .r15, .r16, .r17] s t := by
  have e := env_of hs h ep
  have hlen := hs.hlenw
  have hlen1 := hs.hlen1
  have hl384 : len bits ≤ 384 := by have := hs.w48; omega
  have hfw := h.fw
  have hsz := h.size
  have r3 : s.gpr .r3 = σ.gpr .r3 := ep.other .r3 (by decide) (by decide)
  unfold loadC
  refine WP.seq (WP.mono (Q := fun (u : State) => (u.gpr .r12 = off (σ.gpr .r3) 0 ∧
      u.gpr .r6 = BitVec.ofNat 64 (len bits) ∧ u.mem = s.mem) ∧ Keep [.r6, .r12] s u)
    (WP.keep _ (by prun [r3, show len bits < 2 ^ 15 by omega]) rfl) fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_)
  have eu : Env u (wsB σ) (8 * keyWords bits) (words bits) := e.keep ku (by decide)
  refine WP.mono (VG.Proof.Bignum.PPC64LE.loadN_ok (k := len bits) eu.hs eu.h10 u12 u6 eu.h11 hlen1 hlen
    (by have := hs.w48; omega) (by simp only [slot, hdrBytes]; omega) (by have := eu.hZ; simp only [slot, hdrBytes] at *; omega)
    (fun i hi => ⟨_, by rw [ku.rd, ku.wr, ep.rd, ep.wr, h.wr]; exact List.mem_append_right _ List.mem_cons_self, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; have := hs.key; omega⟩)
    (fun i hi x hx => cand_sep h (by omega) hx)) fun t ⟨tv, to, kt⟩ => ?_
  refine ⟨⟨?_, by rw [← um]; exact to⟩, (ku.trans kt).mono (by decide)⟩
  show VG.Proof.Mont.val32 t.mem (wsB σ) (slot (words bits) 0) (2 * words bits) = _
  rw [tv, um, cand_keep ep hl384]
  simp only [Proof.Dsa.ProbablePrime.candidateAt, layout, BitVec.add_zero, ← hs.hlen]
  rfl

end VG.Proof.Dsa.PPC64LE.Prime
