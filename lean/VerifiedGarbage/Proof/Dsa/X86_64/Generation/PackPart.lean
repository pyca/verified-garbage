module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset

/-! # Copy one generated domain component while retaining the search frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

theorem packArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src dst len : Nat}
    (hs : src < 2 ^ 31) (hd : dst < 2 ^ 31) (hl : len ≤ 1024) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.packArgs src dst len)) s fun t =>
      t.gpr .rsi = off (W 5) src ∧ t.gpr .rdi = off (W 5) dst ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .rcx, .rdx] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rsi = off (W 5) src ∧ t.gpr .rdi = off (W 5) dst ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.packArgs, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      sx_ofNat hs, sx_ofNat hd, cast len (by omega), cast (8 * len) (by omega)]) rfl)
    fun t ⟨⟨hsi, hdi, hcx, hdx, hm⟩, hk⟩ => ⟨hsi, hdi, hcx, hdx, hm, hk⟩

theorem packPart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src dst : Nat} {bs : List Byte}
    (hs : src < 2 ^ 31) (hd : dst < 2 ^ 31) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (off (W 5) src) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off (off (W 5) dst) i) 1)
    (hb : ∀ i < bs.length, s.mem (off (off (W 5) src) i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      off (off (W 5) src) i ≠ off (off (W 5) dst) j)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨off (W 5) dst, bs.length⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨off (W 5) dst, bs.length⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.packPart src dst bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (W 5) dst) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨off (W 5) dst, bs.length⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.packPart
  refine WP.seq (WP.mono (packArgs_ok L R hs hd hl.2) fun u ⟨hsi, hdi, hcx, hdx, hm, ku⟩ => ?_)
  refine WP.mono (copyBytes_ok hl hsi hdi hcx hdx
    (fun i hi => by rw [ku.2.1, ku.2.2]; exact hrd i hi)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) hsep) fun t ⟨result, ft, kt⟩ => ?_
  have ff : Frame [⟨off (W 5) dst, bs.length⟩] s.mem t.mem := by
    intro a ha
    rw [ft a (by
      intro i hi he
      apply ha ⟨off (W 5) dst, bs.length⟩ (by simp)
      rw [he]
      exact Offset.contains_base _ (by omega) (by omega)), hm]
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl (keep.gpr (by decide)) keep.2.2, Rt, ff, keep.mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
