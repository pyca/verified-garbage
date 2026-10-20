module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Native setup for candidate reduction and the saved generator exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

private theorem candidate_arguments_fit {pLen qLen : Nat} (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) :
    ∀ a ∈ candidateArguments pLen qLen, argumentFits a := by
  intro a ha
  simp only [candidateArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  · decide
  · exact ⟨by decide, by decide, hp⟩
  · decide
  · exact ⟨by decide, by decide, hq⟩
  · decide
  · decide
  · decide

theorem candidateArguments_ok {s : State} {B F : Addr} {Z w pLen qLen : Nat} {W : Nat → BitVec 64}
    (h : Ws s B Z w) (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) (hsp : s.gpr .rsp = F)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8) :
    WP isa (.block (headerArguments (candidateArguments pLen qLen))) s fun t =>
      Ws t B Z w ∧
      word t.mem B 128 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped ∧
      word t.mem B 136 = BitVec.ofNat 64 pLen ∧
      word t.mem B 144 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q ∧
      word t.mem B 152 = BitVec.ofNat 64 qLen ∧
      word t.mem B 160 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.p ∧
      word t.mem B 168 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.exponent ∧
      word t.mem B (8 * Public.sMask) = mask true ∧
      Outside B 128 128 s.mem t.mem ∧ Keep [.rax] s t := by
  have hB : Scr s B 256 := by
    simpa only [off, BitVec.add_zero] using h.scr.sub (o := 0) (n := 256) h.h256 (by decide)
  have fits := candidate_arguments_fit hp hq
  refine WP.mono (headerArguments_ok _ fits hB h.rdi hsp hr hwords hsep) fun t ⟨hm, hk⟩ => ?_
  have hf : Outside B 128 128 s.mem t.mem := by
    rw [hm]; exact argumentWrites_outside _ _ _ _ fits
  have wh (k : Nat) (hk32 : k < 32) : word t.mem B (8 * k) =
      argumentWords W (fun j => word s.mem B (8 * j)) (candidateArguments pLen qLen) k := by
    rw [hm]; exact argumentWrites_word _ _ _ _ fits hk32
  have hh (d : Nat) (hd : d + 8 ≤ 128) : word t.mem B d = word s.mem B d :=
    hf.word (Or.inl hd) (by omega)
  have stride : word t.mem B 224 = word s.mem B 224 := by
    exact wh 28 (by decide)
  have ht : Ws t B Z w := ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi,
    (hh 48 (by decide)).trans h.hw, stride.trans h.hS, fun j hj => (hh (8 * sArr j) (by unfold sArr; omega)).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hf, hk⟩
  · exact wh 16 (by decide)
  · exact wh 17 (by decide)
  · exact wh 18 (by decide)
  · exact wh 19 (by decide)
  · exact wh 20 (by decide)
  · exact wh 21 (by decide)
  · exact wh 22 (by decide)

end VG.Proof.Dsa.X86_64.Generation
