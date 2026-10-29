module

import VerifiedGarbage.Proof.Mont.X86.Square.RedStage
import VerifiedGarbage.Proof.Framework.X86.SseDword
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Mont.X86

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def writeState (s : State) (p : Addr) (v : BitVec 64) : State := {s with mem := s.mem.writeW p v}

theorem storePacked_ok {s : State} {W : Addr} {L x d : Nat} {b : Reg} {r : XReg} {v : BitVec 64}
    (hw : Ws s W L) (ptr : PtrAt s W b x) (bound : x+d+8≤L) (vec : s.xmm r = packed v) :
    WP isa (.block [.movqStore (at_ b d) r]) s fun t => t = writeState s (off W (x+d)) v := by
  apply WP.of_runBlock
  refine ⟨_, ?_, rfl⟩
  have ea := ea_ptr hw ptr (d := d) (by omega)
  have writable := ws_write hw bound
  have value : (s.xmm r).extractLsb' 0 64 = v := by
    rw [vec]
    exact qword_packed_zero v
  simp only [runBlock_cons, exec, State.store64, ea, value, writable, ↓reduceIte, runStep_some,
    runBlock_nil, writeState]

theorem writeState_keep (s : State) (p : Addr) (v : BitVec 64) : Keeps [] s (writeState s p v) :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem read32_write64 (m : Mem) (p : Addr) (v : BitVec 64) :
    (m.writeW p v).readW p 32 = v.extractLsb' 0 32 := by
  have e := VG.X86.readW_extract (m.writeW p v) p (w := 64) (k := 0) (n := 4) (by decide)
  rw [Mem.readW_writeW_self64] at e
  simpa only [Nat.mul_zero, Nat.reduceMul, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using e.symm

theorem write64_w32 (m : Mem) (W : Addr) (x v : Nat) :
    w32 (m.writeW (off W x) (BitVec.ofNat 64 v)) W x = v % 2^32 := by
  rw [w32, read32_write64]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_ofNat]
  omega

end VG.Proof.Mont.X86.Square
