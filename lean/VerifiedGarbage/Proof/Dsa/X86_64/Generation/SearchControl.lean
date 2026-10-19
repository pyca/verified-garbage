module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-! # Native counter and seed-offset progression for the bounded search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SearchControl (B : Addr) (counter stride : Nat) (s : State) : Prop where
  scr : Scr s B 24
  rdi : s.gpr .rdi = B
  count : word s.mem B 0 = BitVec.ofNat 64 counter
  offset : word s.mem B 8 = BitVec.ofNat 64 (1 + counter * stride)

theorem searchAdvanceHead_ok {s : State} {B : Addr} {counter stride limit : Nat}
    (h : SearchControl B counter stride s) (hc : counter < limit) (hl : limit ≤ 12288)
    (hs : stride ≤ 12) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.pSearchAdvanceHead limit stride)) s fun t =>
      SearchControl B (counter + 1) stride t ∧ t.cf = some (decide (counter + 1 < limit)) ∧
      Outside B 0 16 s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  have hld : ∀ d, d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (off B d) 8 := fun _ hd => h.scr.ld hd
  have hst : ∀ d, d + 8 ≤ 24 → InRegions s.wr (off B d) 8 := fun _ hd => h.scr.st hd
  have hsmall : ∀ n ≤ 12288, (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n :=
    fun n hn => sx_ofNat (by omega)
  let m := (s.mem.writeW (off B 0) (BitVec.ofNat 64 (counter + 1))).writeW
    (off B 8) (BitVec.ofNat 64 (1 + (counter + 1) * stride))
  have hload : word (s.mem.writeW (off B 0) (BitVec.ofNat 64 (counter + 1))) B 8 =
      BitVec.ofNat 64 (1 + counter * stride) := by
    rw [(writeW_outside s.mem B _ (d := 0) (by decide)).word (Or.inr (by decide)) (by decide)]
    exact h.offset
  have hinc : BitVec.ofNat 64 counter + 1 = BitVec.ofNat 64 (counter + 1) :=
    (BitVec.ofNat_add counter 1).symm
  simp only [VG.Proof.Bignum.word] at hload
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = m ∧
      t.cf = some (decide (counter + 1 < limit))) (by
    xrun [Impl.Dsa.X86_64.Generation.pSearchAdvanceHead, State.ea, hdr, hdrOff, h.rdi,
      hld 0 (by decide), hld 8 (by decide), hst 0 (by decide), hst 8 (by decide),
      h.count, hsmall stride (by omega), hsmall limit hl, hinc, hload, ← BitVec.ofNat_add]
    constructor
    · simp [m, Nat.add_mul, Nat.add_assoc]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : counter + 1 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64)]) rfl) fun t ⟨⟨hm, hcf⟩, hk⟩ => ?_
  have ho : Outside B 0 16 s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ B _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (d := 8) (by decide)).mono (by decide) (by decide))
  refine ⟨⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, ?_, ?_⟩, hcf, ho, hk⟩
  · rw [hm]
    dsimp only [m]
    rw [(writeW_outside _ B _ (d := 8) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hm]; exact word_writeW_self _ _ _ _

end VG.Proof.Dsa.X86_64.Generation
