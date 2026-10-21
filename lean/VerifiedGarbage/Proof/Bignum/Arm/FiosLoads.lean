module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Block

/-! Workspace reads used by the pipelined integrated Montgomery row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem loadsA_ok (s : State) (dst : Reg) (hne : dst ≠ .r3)
    {base : BitVec 32} {size a d ka kd : Nat}
    (ws : Workspace s base size) (hka : ka<4096) (hkd : kd<4096)
    (fa : a+ka+4≤size) (fd : d+kd+4≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (.block [.ldr .r3 .r12 ka,.ldr dst .r0 kd]) s fun t =>
      t.gpr .r3=s.mem.readW (off (State.addr base) (a+ka)) 32 ∧
      t.gpr dst=s.mem.readW (off (State.addr base) (d+kd)) 32 ∧
      t.mem=s.mem ∧ Rest [.r3,dst] s t := by
  refine wp_ldr (a:=off (State.addr base) (a+ka)) hka (ws.ea pa (by omega)) (ws.read fa) fun u hu => ?_
  refine wp_ldr (a:=off (State.addr base) (d+kd)) hkd
    (by rw [hu.other .r0 (by decide)];exact ws.ea pd (by omega))
    (by rw [hu.rd,hu.wr];exact ws.read fd) fun t ht => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht.other .r3 (Ne.symm hne),hu.gpr]
  · rw [ht.gpr,hu.mem]
  · exact ht.mem.trans hu.mem
  · exact (hu.rest (by simp)).trans (ht.rest (by simp))

theorem loadsM_ok (s : State) {base : BitVec 32} {size m k : Nat}
    (ws : Workspace s base size) (hk : k<4096) (fm : m+k+4≤size)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m) :
    WP isa (.block [.ldr .r5 .r4 k]) s fun t =>
      t.gpr .r5=s.mem.readW (off (State.addr base) (m+k)) 32 ∧
      t.mem=s.mem ∧ Rest [.r5] s t := by
  refine wp_ldr (a:=off (State.addr base) (m+k)) hk (ws.ea pm (by omega)) (ws.read fm) fun t ht => WP.block_nil ?_
  exact ⟨ht.gpr,ht.mem,ht.rest (by simp)⟩

end VG.Proof.Bignum.Arm.Fios
