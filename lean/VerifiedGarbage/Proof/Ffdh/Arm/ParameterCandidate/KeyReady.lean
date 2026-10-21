module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyViewExec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyContext
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Select the same arrays through RSA's proved native key-operation view. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def KeyReady (base : BitVec 32) (capacity w : Nat) (s : State) : Prop :=
  VG.Proof.Rsa.Arm.Keys.Ws (s.withRegions s.rd [keyViewRegion base capacity])
    (base + 96#32) (8 * capacity - 96) (2 * w + 2) 30

theorem KeyReady.rest {s t : State} {base : BitVec 32} {capacity w : Nat} {rs : List Reg}
    (h : KeyReady base capacity w s) (rest : Rest rs s t)
    (r7 : .r7 ∉ rs) (r8 : .r8 ∉ rs) (r9 : .r9 ∉ rs) : KeyReady base capacity w t :=
  h.of (rest.gpr _ r7) (rest.gpr _ r8) (rest.gpr _ r9) rfl

theorem keyContext_ready (s : State) {base : BitVec 32} {capacity k : Nat}
    (workspace : Workspace s base (8 * capacity))
    (data : MontData base capacity (VG.Spec.Rsa.modulusWords k) s.mem)
    (minLength : 64 ≤ k) (maxLength : k ≤ 1024) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext) s fun t =>
      KeyReady base capacity (VG.Spec.Rsa.modulusWords k) t ∧ t.gpr .r0 = base ∧ t.mem = s.mem ∧
        Rest [.r0, .r7, .r8, .r9] s t := by
  have dims := keyView_dimensions minLength maxLength space
  have capLarge : 96 < 8 * capacity := by
    have := minLength
    simp only [Spec.Rsa.scratchWords] at space
    omega
  have shiftFits : base.toNat + 96 < 2 ^ 32 := by have := workspace.nowrap; omega
  have shifted : (base + 96#32).toNat = base.toNat + 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 96 < 2 ^ 32),
      Nat.mod_eq_of_lt shiftFits]
  have native := nativeHeader_of_layout s.mem base workspace.nowrap (Nat.le_refl _) data.layout
  rw [data.width] at native
  have readWidth : InRegions (s.rd ++ s.wr) (State.addr (base + 48#32)) 4 := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; omega)]
    exact workspace.read (by omega)
  have width : s.mem.readW (State.addr (base + 48#32)) 32 = BitVec.ofNat 32 (VG.Spec.Rsa.modulusWords k) := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; omega)]
    exact native.count
  refine WP.mono (keyContext_ok s base (VG.Spec.Rsa.modulusWords k) readBase saved readWidth width) ?_
  rintro t ⟨⟨ptr, r8, r9, r7, mem⟩, rest⟩
  refine ⟨?_, ptr, mem, rest⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, r8, r9⟩
  · rw [shifted]
    have := workspace.nowrap
    omega
  · exact List.mem_cons_self
  · exact dims.2.2
  · exact dims.1
  · exact dims.2.1
  · change t.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Rsa.Arm.Keys.S (2 * VG.Spec.Rsa.modulusWords k + 2))
    rw [keyView_stride]
    exact r7

end VG.Proof.Ffdh.Arm.ParameterCandidate
