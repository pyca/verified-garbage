module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Stack loads and saved register slots of the Montgomery wrapper -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Upd)

theorem wp_loadStack {s : State} {is : List Instr} {Q : State → Prop}
    {r : Reg} {d : Nat} {a : Addr} (hd : d < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 d) = a) (hr : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ t, Upd s t r (s.mem.readW a 32) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r d :: is)) s Q := by
  subst ha
  exact VG.Proof.X25519.Arm.WP.cons
    (by simp only [exec, hd, ite_true, State.load32, hr, Option.map_some]) (k _ (Upd.setReg _ _ _))

def montSaved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16),
   (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]

theorem mont_push_saved (s : State) (fit : 36 ≤ s.sp.toNat) :
    Spill.Saved (pushed [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s).mem
      (State.addr (s.sp - 36)) s.gpr montSaved := by
  let sp := s.sp - 36
  have bound : sp.toNat + 36 ≤ 2 ^ 32 := by
    rw [show sp = s.sp - BitVec.ofNat 32 36 from rfl, FrameStack.sub_toNat' fit]
    have := s.sp.isLt
    omega
  have address (k : Nat) (hk : k < 36) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    addr_add (by omega)
  have memEq : (pushed [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s).mem =
      Spill.saveMem s.mem (State.addr sp) s.gpr montSaved := by
    change storeWords s.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem, montSaved]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide),
      address 16 (by decide), address 20 (by decide), address 24 (by decide),
      address 28 (by decide), address 32 (by decide)]
    simp only [off, BitVec.add_zero]
  rw [memEq]
  exact Spill.saveMem_saved (lo := 0) (hi := 36) (State.addr sp) s.gpr s.mem montSaved (by decide)

end VG.Proof.Bignum.Arm
