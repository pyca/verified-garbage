module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Setup
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

theorem codec_input {c : Cfg} {inputLen outputLen : Nat} {s : State}
    (h : codecPre inputLen outputLen false s) : InputPre c inputLen s := by
  obtain ⟨hrd, hwr, _, _, hpk, _, hargs, _, _, _, hpf, hwf, hsp, hlo, _, hstk⟩ := h
  have lo : c.stk ≤ (s.gpr .esp).toNat := Nat.le_trans (Cfg.stk_le c) hlo
  have stk : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 c.stk, c.stk⟩
      ⟨ptr s 2, size⟩ := by
    have sub := below_le_sub (sp := s.gpr .esp) (Cfg.stk_le c) hlo
    change Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 c.stk).setWidth 64, c.stk⟩
      ⟨((s.gpr .esp) - BitVec.ofNat 32 28).setWidth 64, 28⟩ at sub
    rw [Taint.sub_setWidth lo, Taint.sub_setWidth hlo] at sub
    exact hstk.sub_left sub
  exact ⟨by rw [hrd, hwr]; simp, by rw [hwr]; simp, hpk, hpf, hwf,
    by rw [hrd, hwr]; simp, hargs, hsp, lo, stk⟩

end VG.Proof.EcKey.Compressed.X86
