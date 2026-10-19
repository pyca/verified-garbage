module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Framework.Omega

/-! # Copy accepted packed parameters to the caller and return success -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem outputCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {bs : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 bs.length)
    (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (off (W 5) packed) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off (W 6) i) 1)
    (hb : ∀ i < bs.length, s.mem (off (off (W 5) packed) i) = bs.getD i 0)
    (sep : ∀ i < bs.length, ∀ j < bs.length, off (off (W 5) packed) i ≠ off (W 6) j) :
    WP isa Impl.Dsa.X86_64.Generation.outputCopy s fun t =>
      t.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t.mem (W 6) bs.length = bs ∧
      Frame [⟨W 6, bs.length⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.outputCopy
  refine WP.seq (WP.mono (outputArgs_ok L R hlen) fun u ⟨hsi, hdi, hcx, hdx, hm, ku⟩ => ?_)
  refine WP.seq (WP.mono (copyBytes_ok hl hsi hdi hcx hdx
    (fun i hi => by rw [ku.2.1, ku.2.2]; exact hrd i hi)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) sep) fun v ⟨bytes, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 1 ∧ t.mem = v.mem)
    (by xrun) rfl) fun t ⟨⟨hr, hmem⟩, kt⟩ => ?_
  refine ⟨hr, hmem ▸ bytes, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  intro a ha
  rw [hmem, fv a (by
    intro i hi he
    apply ha ⟨W 6, bs.length⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)), hm]

end VG.Proof.Dsa.X86_64.Generation
