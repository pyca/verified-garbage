module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-! # Lift the saved arithmetic body to actual Montgomery calls -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.MlKem.X86_64

theorem call_body_ok {code : Prog isa} {s : State} {B : Addr} {n w c b : Nat}
    (hi : code.InlineOk = true) (hc : Clear (hole (s.gpr .rsp)) s)
    (hd : Region.Disjoint ⟨B, 8 * n⟩ (hole (s.gpr .rsp))) (hn : 8 * n ≤ 2 ^ 64)
    (h : WP isa code.inline s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Proof.MillerRabin.Round.round c b).toNat ∧
      t.gpr .rbx = s.mem.readW (s.gpr .rsp + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (s.gpr .rsp + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (s.gpr .rsp + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (s.gpr .rsp + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (s.gpr .rsp + 72#64) 64 ∧ Keep mmRegs s t ∧
      Frame [⟨B, 8 * n⟩] s.mem t.mem ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w s.mem t.mem) :
    WP isa code s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Proof.MillerRabin.Round.round c b).toNat ∧
      t.gpr .rbx = s.mem.readW (s.gpr .rsp + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (s.gpr .rsp + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (s.gpr .rsp + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (s.gpr .rsp + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (s.gpr .rsp + 72#64) 64 ∧ Keep mmRegs s t ∧
      Frame [hole (s.gpr .rsp), ⟨B, 8 * n⟩] s.mem t.mem ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.extended B n w s.mem t.mem := by
  refine WP.mono (WP.of_inline hi hc h) ?_
  rintro t ⟨u, hv, unk, rfl, _, hr, hbx, h12, h13, h14, h15, hk, hf, hp⟩
  refine ⟨hr, hbx, h12, h13, h14, h15, ?_, ?_, ?_⟩
  · exact ⟨hk.1, hk.2.1, hk.2.2⟩
  · intro x hx
    refine (State.patch_mem (hx _ (by simp))).trans (hf x ?_)
    intro r hr'
    exact hx r (by simp only [List.mem_singleton] at hr'; subst hr'; simp)
  · intro i hi' hh ha ht
    have hx : ¬ (hole (s.gpr .rsp)).Contains (B + BitVec.ofNat 64 i) 1 := by
      apply hd _ (Offset.contains_base B (by omega_arith) (by omega_arith))
    exact (State.patch_mem hx).trans (hp i hi' hh ha ht)

end VG.Proof.MillerRabin.X86_64
