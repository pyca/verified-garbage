import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock

/-! # Loading two prepared powers without per-record conversion -/

namespace VG.Proof.Gcm.X86_64.StitchZR
open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Proof.Gcm.X86_64.Pclmul (ea_at)
open VG.Proof.Gcm.X86_64.Vpclmul (load256_lo load256_hi)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Impl.Gcm.X86_64.StitchZR (cvtPair)

/-- The trusted encoding is exactly the conversion already used by GHASH. -/
theorem preparedPower_eq (v : Spec.Gcm.Block) : Spec.Gcm.preparedPower v = hInvF v := rfl

/-- A complete pair load, including preservation of all other low registers. -/
theorem loadPair_ok (j : Nat) (d : XReg) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16*j : Nat) : Int)) 32) :
    WP isa (.block (cvtPair j d)) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW
        (s.gpr .rdi + BitVec.ofNat 64 (240 + 16*j + 16*l)) 128) ∧ ZFrame [d] s s' := by
  let a := s.gpr .rdi + BitVec.ofInt 64 ((240 + 16*j : Nat) : Int)
  let v := s.mem.readW a 256
  let t := s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [cvtPair, WP.block_cons_iff]
  refine ⟨t, by simp only [isa, exec, State.load256, ea_at, hin, ite_true, Option.map_some]; rfl,
    WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, fun r hr l _ => ?_⟩⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [t, State.lane_setV256, ite_true, v, load256_lo, a,
        BitVec.ofInt_natCast, Nat.mul_zero, Nat.add_zero]
    · simp only [t, State.lane_setV256, ite_true, Nat.one_ne_zero, ite_false,
        v, load256_hi, a, BitVec.ofInt_natCast, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
  · exact State.zlane_setV_ne _ _ (fun h => hr (List.mem_singleton.mpr h)) _ _ _

/-- A valid odd-indexed pair has the same two values as the old conversion. -/
theorem pair_values {m : Mem} {p : Addr} (hp : Spec.Gcm.PreparedPowersRepr m p)
    {j : Nat} (hj : j < 48) (ho : j % 2 = 1) {l : Nat} (hl : l < 2) :
    m.readW (p + BitVec.ofNat 64 (240 + 16*j + 16*l)) 128 =
      hInvF (Spec.Gcm.hpow (Spec.Gcm.ctxH m p) (j + 1 - l)) := by
  obtain ⟨lo, hi⟩ := hp (j / 2) (by omega)
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [show 240 + 16*j + 16*0 = 256 + 32*(j/2) by omega, lo, preparedPower_eq]
    congr 2; omega
  · rw [show 240 + 16*j + 16*1 = 272 + 32*(j/2) by omega, hi, preparedPower_eq]
    congr 2; omega

end VG.Proof.Gcm.X86_64.StitchZR
