module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Search
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Native counter and seed-offset progression for the bounded search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SearchControl (B : Addr) (counter stride : Nat) (s : State) : Prop where
  scr : Scr s B 24
  x0 : s.gpr .x0 = B
  count : word s.mem B 0 = BitVec.ofNat 64 counter
  offset : word s.mem B 8 = BitVec.ofNat 64 (1 + counter * stride)

theorem searchAdvanceHead_ok {s : State} {B : Addr} {counter stride limit : Nat}
    (h : SearchControl B counter stride s) (hc : counter < limit) (hl : limit ≤ 12288)
    (hs : stride ≤ 12) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.pSearchAdvanceHead limit stride)) s fun t =>
      SearchControl B (counter + 1) stride t ∧ t.gpr .x5 = (if limit ≤ counter + 1 then 1 else 0) ∧
      Outside B 0 16 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x7] s t := by
  have hld : ∀ d, d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (off B d) 8 := fun _ hd => h.scr.ld hd
  have hst : ∀ d, d + 8 ≤ 24 → InRegions s.wr (off B d) 8 := fun _ hd => h.scr.st hd
  let m := (s.mem.writeW (off B 0) (BitVec.ofNat 64 (counter + 1))).writeW
    (off B 8) (BitVec.ofNat 64 (1 + (counter + 1) * stride))
  have hload : word (s.mem.writeW (off B 0) (BitVec.ofNat 64 (counter + 1))) B 8 =
      BitVec.ofNat 64 (1 + counter * stride) := by
    rw [(writeW_outside s.mem B _ (d := 0) (by decide)).word (Or.inr (by decide)) (by decide)]
    exact h.offset
  have hinc : BitVec.ofNat 64 counter + 1 = BitVec.ofNat 64 (counter + 1) :=
    (BitVec.ofNat_add counter 1).symm
  simp only [VG.Proof.Bignum.word] at hload
  have hlimit : (BitVec.ofNat 16 limit).setWidth 64 = BitVec.ofNat 64 limit := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hcount : s.mem.readW (B + 0#64) 64 = BitVec.ofNat 64 counter := h.count
  have hzero : InRegions (s.rd ++ s.wr) B 8 := by simpa only [off, BitVec.add_zero] using hld 0 (by decide)
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x7] (Q := fun t => t.mem = m ∧
    t.gpr .x5 = (if limit ≤ counter + 1 then 1 else 0)) (by
    unfold Impl.Dsa.AArch64.Generation.pSearchAdvanceHead
    brun [h.x0, hdr_enc (by decide : 0 < 32), hdr_enc (by decide : 1 < 32),
      hld 0 (by decide), hld 8 (by decide), hst 0 (by decide), hst 8 (by decide),
      hcount, hzero, hinc, hload, exec_addImm_x' (show stride < 4096 by omega),
      ← BitVec.ofNat_add, hlimit, VG.Impl.RsaKeyGen.AArch64.Candidate.geFlag,
      subs_ge (show counter + 1 < 2 ^ 64 by omega) (show limit < 2 ^ 64 by omega)]
    constructor
    · simp [m, Nat.add_mul, Nat.add_assoc]
    · simp only [decide_eq_true_eq]
      rfl) rfl rfl rfl) fun t ⟨⟨hm, hflag⟩, hk⟩ => ?_
  have ho : Outside B 0 16 s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ B _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (d := 8) (by decide)).mono (by decide) (by decide))
  refine ⟨⟨h.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.x0, ?_, ?_⟩, hflag, ho, hk⟩
  · rw [hm]
    dsimp only [m]
    rw [(writeW_outside _ B _ (d := 8) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hm]; exact word_writeW_self _ _ _ _

end VG.Proof.Dsa.AArch64.Generation
