module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrBit
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bind either h or computed g to the native range checker -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

private theorem generator_arguments_fit {len : Nat} (hl : len < 2 ^ 31) (result : Bool) :
    ∀ a ∈ generatorRangeArguments len result, argumentFits a := by
  intro a ha
  cases result <;> simp only [generatorRangeArguments, Bool.false_eq_true, ite_false, ite_true,
    List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  all_goals first | decide | exact ⟨by decide, by decide, hl⟩

theorem generatorArguments_ok {s : State} {B F : Addr} {Z w len : Nat} {W : Nat → BitVec 64}
    (h : Ws s B Z w) (hl : len < 2 ^ 31) (result : Bool) (hsp : s.gpr .rsp = F)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8) :
    WP isa (.block (headerArguments (generatorRangeArguments len result))) s fun t =>
      Ws t B Z w ∧
      word t.mem B 128 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.p ∧
      word t.mem B 136 = BitVec.ofNat 64 len ∧
      word t.mem B 144 = (if result then off (W 5) Impl.Dsa.Generation.Layout.g else W 21) ∧
      word t.mem B 152 = BitVec.ofNat 64 len ∧
      Outside B 128 128 s.mem t.mem ∧ Keep [.rax] s t := by
  have hB : Scr s B 256 := by
    simpa only [off, BitVec.add_zero] using h.scr.sub (o := 0) (n := 256) h.h256 (by decide)
  have fits := generator_arguments_fit hl result
  refine WP.mono (headerArguments_ok _ fits hB h.rdi hsp hr hwords hsep) fun t ⟨hm, hk⟩ => ?_
  have hf : Outside B 128 128 s.mem t.mem := by
    rw [hm]; exact argumentWrites_outside _ _ _ _ fits
  have wh (k : Nat) (hk32 : k < 32) : word t.mem B (8 * k) =
      argumentWords W (fun j => word s.mem B (8 * j)) (generatorRangeArguments len result) k := by
    rw [hm]; exact argumentWrites_word _ _ _ _ fits hk32
  have hh (d : Nat) (hd : d + 8 ≤ 128) : word t.mem B d = word s.mem B d :=
    hf.word (Or.inl hd) (by omega)
  have stride : word t.mem B 224 = word s.mem B 224 := by
    cases result <;> exact wh 28 (by decide)
  have ht : Ws t B Z w := ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi,
    (hh 48 (by decide)).trans h.hw, stride.trans h.hS, fun j hj => (hh (8 * sArr j) (by unfold sArr; omega)).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩
  refine ⟨ht, ?_, ?_, ?_, ?_, hf, hk⟩
  · cases result <;> exact wh 16 (by decide)
  · cases result <;> exact wh 17 (by decide)
  · cases result <;> simpa [argumentWords, generatorRangeArguments, argumentValue] using wh 18 (by decide)
  · cases result <;> exact wh 19 (by decide)

end VG.Proof.Dsa.X86_64.Generation
