module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
public import VerifiedGarbage.Proof.MillerRabin.Contract

import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # The saved round body preserves the reusable caller's workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

theorem body_keeps_ok (M : Mont) {s : State} {B S : Addr} {n w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B (8 * n) w mi c bm) (h : MrDims B (8 * n) w)
    (he : ECtx s.mem B w c) (hodd : c % 2 = 1) (h3 : 3 ≤ c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c)
    (hsp : s.gpr .rsp = S) (hd : Region.Disjoint ⟨B, 8 * n⟩ ⟨S, 112⟩)
    (hl : ∀ d, 8 ≤ d → d + 8 ≤ 112 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 8)
    (hs : ∀ p ∈ restoreSlots, s.mem.readW (S + BitVec.ofNat 64 p.2) 64 = word s.mem B (8 * p.1)) :
    WP isa (VG.Impl.MillerRabin.X86_64.body M.mm) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Proof.MillerRabin.Round.round c b).toNat ∧
      t.gpr .rbx = s.mem.readW (S + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (S + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (S + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (S + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (S + 72#64) 64 ∧ Keep mmRegs s t ∧
      Frame [⟨B, 8 * n⟩] s.mem t.mem ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w s.mem t.mem := by
  refine WP.mono (body_ok M hc h he hodd h3 hX hsp hd hl) ?_
  rintro t ⟨hr, hbx, h12, h13, h14, h15, hk, hf, u, hm, hu, hcore⟩
  refine ⟨hr, hbx, h12, h13, h14, h15, hk, hf, ?_⟩
  rw [hm]
  apply restored_core_keeps (by have := hc.good.scr.nowrap; omega_arith) hcore
  intro p hp
  have hb : p.2 + 8 ≤ 112 := by
    simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine Eq.trans ?_ (hs p hp)
  apply hu.readW (r := ⟨S, 112⟩)
  · exact Offset.contains_base S hb (by omega_arith)
  · intro r hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    exact hd.symm
  · decide

end VG.Proof.MillerRabin.X86_64
