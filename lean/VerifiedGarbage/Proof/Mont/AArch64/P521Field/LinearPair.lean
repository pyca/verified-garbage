module

public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

/-! Two loads and two carry operations in the fused linear kernels. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def twoLoads (rn d0 d1 : Reg) (b : Nat) : List Instr :=
  [.ldr .x d0 rn b,.ldr .x d1 rn (b+8)]

theorem two_loads_ok {s : State} {rn d0 d1 : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+16≤size) (hb8 : b%8=0)
    (hr : rn≠d0) (hd : d0≠d1) :
    WP isa (.block (twoLoads rn d0 d1 b)) s fun t =>
      t.gpr d0=word s.mem p b ∧ t.gpr d1=word s.mem p (b+8) ∧
      t.c=s.c ∧ Keeps [d0,d1] s t := by
  rw [twoLoads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ldR_ok hp (d:=b) (by omega_arith) hb8 d0) fun u ⟨a0,k0,c0⟩ => ?_
  have hp' := hp.of_keeps k0 (by simpa only [List.mem_singleton] using hr)
  refine WP.mono (ldR_ok hp' (d:=b+8) (by omega_arith) (by omega_arith) d1)
    fun t ⟨a1,k1,c1⟩ => ?_
  exact ⟨by rw [k1.gpr d0 (by simpa only [List.mem_singleton] using hd),a0],
    by rw [a1,k0.mem],c1.trans c0,(k0.mono (by simp)).trans (k1.mono (by simp))⟩

def linearAddPair (rn r0 r1 : Reg) (b : Nat) : List Instr :=
  twoLoads rn .x4 .x3 b++([.adcs .x r0 r0 .x4,.adcs .x r1 r1 .x3] : List Instr)

theorem linear_add_pair_words {s : State} {rn r0 r1 : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+16≤size) (hb8 : b%8=0)
    (hr : rn≠.x4) (h01 : r0≠r1) (h0 : r0∉[Reg.x3,.x4]) (h1 : r1∉[Reg.x3,.x4]) :
    WP isa (.block (linearAddPair rn r0 r1 b)) s fun t =>
      t.gpr r0=addCarry (s.gpr r0) (word s.mem p b) s.c ∧
      t.gpr r1=addCarry (s.gpr r1) (word s.mem p (b+8))
        (carryOut (s.gpr r0) (word s.mem p b) s.c) ∧
      t.c=carryOut (s.gpr r1) (word s.mem p (b+8))
        (carryOut (s.gpr r0) (word s.mem p b) s.c) ∧ Keeps [.x3,.x4,r0,r1] s t := by
  rw [linearAddPair,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 hr (by decide)) fun u ⟨b0,b1,cu,ku⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (addc_ok u r0 r0 .x4 false rfl) fun v ⟨a0,c0,k0⟩ => ?_
  refine WP.mono (addc_ok v r1 r1 .x3 false rfl) fun t ⟨a1,c1,k1⟩ => ?_
  have u0 : u.gpr r0=s.gpr r0 := ku.gpr r0 (by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or,and_comm] using h0)
  have u1 : u.gpr r1=s.gpr r1 := ku.gpr r1 (by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or,and_comm] using h1)
  have v1 : v.gpr r1=u.gpr r1 := k0.gpr r1 (by simpa only [List.mem_singleton,ne_comm] using h01)
  have v3 : v.gpr .x3=u.gpr .x3 := k0.gpr .x3 (by
    simp only [List.mem_singleton]
    intro h
    exact h0 (by simp [←h]))
  simp only [Bool.false_eq_true,ite_false] at a0 c0 a1 c1
  rw [b0,u0,cu] at a0 c0
  rw [v1,v3,u1,b1,c0] at a1 c1
  exact ⟨by simpa only [k1.gpr r0 (by simpa only [List.mem_singleton] using h01)] using a0,a1,c1,
    (ku.mono (by simp)).trans ((k0.mono (by simp)).trans (k1.mono (by simp)))⟩

theorem linear_add_pair_value {s : State} {rn r0 r1 : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+16≤size) (hb8 : b%8=0)
    (hr : rn≠.x4) (h01 : r0≠r1) (h0 : r0∉[Reg.x3,.x4]) (h1 : r1∉[Reg.x3,.x4]) :
    WP isa (.block (linearAddPair rn r0 r1 b)) s fun t =>
      regsVal t [r0,r1]+2^128*t.c.toNat=regsVal s [r0,r1]+wordsVal s.mem p b 2+s.c.toNat ∧
      Keeps [.x3,.x4,r0,r1] s t := by
  refine WP.mono (linear_add_pair_words hp hb hb8 hr h01 h0 h1) fun t ⟨a0,a1,c,k⟩ => ?_
  refine ⟨?_,k⟩
  simp only [regsVal,wordsVal,Nat.add_zero,Nat.mul_zero,a0,a1,c]
  have e0 := addCarry_value (s.gpr r0) (word s.mem p b) s.c
  have e1 := addCarry_value (s.gpr r1) (word s.mem p (b+8))
    (carryOut (s.gpr r0) (word s.mem p b) s.c)
  omega_using [e0,e1]

end VG.Proof.Mont.AArch64.P521Field
