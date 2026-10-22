module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticArguments
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Permissions
import VerifiedGarbage.Proof.Framework.Offset

/-! Read-only public arguments adapt the existing RSA runtime workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt VG.Proof.Bignum.X86

def arithmeticRead (s : State) : List Region := ⟨(s.gpr .esp).setWidth 64, 16⟩ :: s.rd

theorem arithmetic_ready {s : State} {base : Addr} {bytes len count : Nat}
    (ws : VG.Proof.Rsa.X86.Keys.Ws s base bytes (kw len) count)
    (length : len ≤ 1024) (fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 16⟩ ⟨base, bytes⟩)
    (workspaceWord : s.mem.readW ((s.gpr .esp).setWidth 64 + 8#64) 32 = BitVec.ofNat 32 base.toNat)
    (lengthWord : s.mem.readW ((s.gpr .esp).setWidth 64 + 12#64) 32 = BitVec.ofNat 32 len) :
    RtWs arithmeticLay (s.withRegions (arithmeticRead s) [⟨base, bytes⟩]) base bytes len count := by
  let t := s.withRegions (arithmeticRead s) [⟨base, bytes⟩]
  have scr : Scr t base bytes := ⟨ws.workspace.edi, List.mem_singleton_self _, ws.workspace.nowrap,
    ws.workspace.stk⟩
  have argument (i : Nat) (hi : 4 + 4 * i + 4 ≤ 16) (v : BitVec 32)
      (value : s.mem.readW ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i)) 32 = v) :
      CallArgument t base bytes i v := by
    have addr : VG.Proof.Dsa.X86.stackAddress t i =
        (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
      addr_eq (by dsimp [t]; omega)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [addr]
      exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), Offset.contains_base _ hi (by omega)⟩
    · rw [addr]
      exact apart.sub_left (Offset.sub_base _ hi)
    · change t.mem.readW (VG.Proof.Dsa.X86.stackAddress t i) 32 = v
      rw [addr]; exact value
  refine ⟨⟨scr, ws.fits, ws.wpos, ws.wle⟩, ?_, ?_, by omega, by decide⟩
  · exact ⟨len, length, rfl, argument 2 (by decide) _ lengthWord⟩
  · exact argument 1 (by decide) _ workspaceWord

end VG.Proof.Dsa.X86.Generation
