module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! Addresses and stack space for the existing streaming hash workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Pbkdf2.Stream.X86

theorem workspace_pointer_address {s : State} {base : Addr} {bytes d : Nat}
    (scr : Scr s base bytes) (bound : d < bytes) :
    (s.gpr .edi + BitVec.ofNat 32 d).setWidth 64 = off base d := scr.ea bound

theorem workspace_pointer_fit {s : State} {base : Addr} {bytes d n : Nat}
    (scr : Scr s base bytes) (bound : d + n < bytes) :
    (s.gpr .edi + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, scr.edi_toNat,
    Nat.mod_eq_of_lt (a := d) (by have := scr.nowrap; omega),
    Nat.mod_eq_of_lt (by have := scr.nowrap; omega)]
  have := scr.nowrap
  omega

theorem pushed_hash_stack52 {s : State} :
    Region.Sub (stk (pushed [.edi] s)) (below (s.gpr .esp) 52) := by
  rw [stk, pushed_esp]
  change Region.Sub (below (s.gpr .esp - 4#32) 48) _
  have address : s.gpr .esp - 4#32 - 48#32 = s.gpr .esp - 52#32 := by rw [BitVec.sub_sub]; rfl
  unfold below
  rw [address]
  exact Region.sub_prefix (by decide : 48 ≤ 52)

theorem pushed_hash_stack {s : State} {base : Addr} {bytes : Nat}
    (room : RoundRoom (s.gpr .esp) base bytes) :
    Region.Sub (stk (pushed [.edi] s)) (below (s.gpr .esp) 1184) :=
  fun x hx => below_sub (by decide : 52 ≤ 1184) room.low x (pushed_hash_stack52 x hx)

end VG.Proof.Dsa.X86.Generation
