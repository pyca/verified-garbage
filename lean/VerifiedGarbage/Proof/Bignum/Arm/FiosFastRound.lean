module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
import VerifiedGarbage.Proof.Bignum.Arm.FiosArgs
import VerifiedGarbage.Proof.Bignum.Arm.FiosRoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
import VerifiedGarbage.Proof.Bignum.Arm.FiosCode
public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.FiosLoads
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Bignum.Arm.FiosPipelinedStep`, which only this module used -/

section

/-! ### `Bignum.Arm.FiosPipelinedMemory`, which this module and modules that import it used -/

section

/-! Store the oldest pending product's cancelled low word. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Proof.Mont VG.Proof.Bignum.Arm

theorem store_prefix {mem mem' : Mem} {base : Addr} {size acc i : Nat} {out : BitVec 32}
    (nowrap : base.toNat+size≤2^32) (fit : acc+4*(i+1)≤size)
    (memory : mem'=mem.writeW (off base (acc+4*i)) out) :
    Outside base (acc+4*i) 4 mem mem' ∧
    val32 mem' base acc (i+1)=val32 mem base acc i+2^(32*i)*out.toNat := by
  have outside := writeW32_outside mem base (d:=acc+4*i) out (by omega_using [nowrap, fit])
  rw [←memory] at outside
  have low := outside.val32 (d:=acc) (k:=i) (by omega_using []) (by omega_using [nowrap, fit])
  have top : w32 mem' base (acc+4*i)=out.toNat := by rw [memory,w32_write_self]
  exact ⟨outside,by rw [val32_succ,low,top]⟩

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! ### `Bignum.Arm.FiosPipelinedValue`, which this module and modules that import it used -/

section

/-! Lift the carry identities to Montgomery operand prefixes. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosPipelinedMath.lean`, which only this module imported.
section

/-! One pending product joins the independent product and cancellation sums. -/

section
namespace VG.Proof.Bignum.Arm.FiosPipelined

theorem start_value {R P O ca cm lo ca' V a : Nat}
    (prior : R*O+P*(ca+cm)=V) (product : lo+R*ca'=a+ca) :
    R*O+P*(lo+cm)+P*R*ca'=V+P*a := by
  have scaled := congrArg (fun z => P*z) product
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] at *
  omega

theorem step_value {R P O O' pending ca cm next ca' cm' out V a m : Nat}
    (prior : R*O+P*(pending+cm)+P*R*ca=V)
    (product : next+R*ca'=a+ca)
    (cancel : out+R*cm'=pending+m+cm)
    (stored : R*O'=R*O+P*out) :
    R*O'+P*R*(next+cm')+P*R*R*ca'=V+P*R*a+P*m := by
  have prodScaled := congrArg (fun z => P*R*z) product
  have modScaled := congrArg (fun z => P*z) cancel
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] at *
  omega

theorem finish_value {R P O O' pending ca cm cm' out V m : Nat}
    (prior : R*O+P*(pending+cm)+P*R*ca=V)
    (cancel : out+R*cm'=pending+m+cm)
    (stored : R*O'=R*O+P*out) :
    R*O'+P*R*(ca+cm')=V+P*m := by
  have scaled := congrArg (fun z => P*z) cancel
  simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] at *
  omega

end VG.Proof.Bignum.Arm.FiosPipelined
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Proof.Mont

theorem start_prefix {mem0 mem : Mem} {base : Addr} {acc b mod i x q ca cm lo ca' : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*(ca+cm)=
      val32 mem0 base acc (i+1)+x*val32 mem0 base b (i+1)+q*val32 mem0 base mod (i+1))
    (product : lo+2^32*ca'=w32 mem0 base (acc+4*(i+1))+x*w32 mem0 base (b+4*(i+1))+ca) :
    2^32*val32 mem base acc i+2^(32*(i+1))*(lo+cm)+2^(32*(i+2))*ca'=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+1) := by
  have power : 2^(32*(i+2))=2^(32*(i+1))*2^32 :=
    (pow32_succ (i+1)).trans (Nat.mul_comm _ _)
  rw [power]
  refine (start_value prior product).trans ?_
  rw [val32_succ mem0 base acc (i+1),val32_succ mem0 base b (i+1)]
  simp only [Nat.mul_add]
  ac_rfl

theorem step_prefix {mem0 mem mem' : Mem} {base : Addr}
    {acc b mod i x q pending ca cm next ca' cm' out : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*(pending+cm)+2^(32*(i+2))*ca=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+1))
    (product : next+2^32*ca'=w32 mem0 base (acc+4*(i+2))+x*w32 mem0 base (b+4*(i+2))+ca)
    (cancel : out+2^32*cm'=pending+q*w32 mem0 base (mod+4*(i+1))+cm)
    (stored : val32 mem' base acc (i+1)=val32 mem base acc i+2^(32*i)*out) :
    2^32*val32 mem' base acc (i+1)+2^(32*(i+2))*(next+cm')+2^(32*(i+3))*ca'=
      val32 mem0 base acc (i+3)+x*val32 mem0 base b (i+3)+q*val32 mem0 base mod (i+2) := by
  have power : 2^(32*(i+2))=2^(32*(i+1))*2^32 :=
    (pow32_succ (i+1)).trans (Nat.mul_comm _ _)
  have powerNext : 2^(32*(i+3))=2^(32*(i+1))*2^32*2^32 := by
    rw [pow32_succ (i+2),power]
    rw [←Nat.mul_assoc (2^32) (2^(32*(i+1))) (2^32),
      Nat.mul_comm (2^32) (2^(32*(i+1)))]
  have ready := prior
  rw [power] at ready
  have write := congrArg (fun z => 2^32*z) stored
  simp only [Nat.mul_add] at write
  have scale : 2^32*2^(32*i)=2^(32*(i+1)) :=
    (pow32_succ i).symm
  rw [←Nat.mul_assoc (2^32) (2^(32*i)) out,scale] at write
  rw [power,powerNext]
  refine (step_value ready product cancel write).trans ?_
  rw [val32_succ mem0 base acc (i+2),val32_succ mem0 base b (i+2),
    val32_succ mem0 base mod (i+1),power]
  simp only [Nat.mul_add]
  ac_rfl

theorem finish_prefix {mem0 mem mem' : Mem} {base : Addr}
    {acc b mod i x q pending ca cm cm' out : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*(pending+cm)+2^(32*(i+2))*ca=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+1))
    (cancel : out+2^32*cm'=pending+q*w32 mem0 base (mod+4*(i+1))+cm)
    (stored : val32 mem' base acc (i+1)=val32 mem base acc i+2^(32*i)*out) :
    2^32*val32 mem' base acc (i+1)+2^(32*(i+2))*(ca+cm')=
      val32 mem0 base acc (i+2)+x*val32 mem0 base b (i+2)+q*val32 mem0 base mod (i+2) := by
  have power : 2^(32*(i+2))=2^(32*(i+1))*2^32 :=
    (pow32_succ (i+1)).trans (Nat.mul_comm _ _)
  have ready := prior
  rw [power] at ready
  have write := congrArg (fun z => 2^32*z) stored
  simp only [Nat.mul_add] at write
  have scale : 2^32*2^(32*i)=2^(32*(i+1)) :=
    (pow32_succ i).symm
  rw [←Nat.mul_assoc (2^32) (2^(32*i)) out,scale] at write
  rw [power]
  refine (finish_value ready cancel write).trans ?_
  rw [val32_succ mem0 base mod (i+1)]
  simp only [Nat.mul_add]
  ac_rfl

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! ### `Bignum.Arm.FiosPipelinedOps`, which this module and modules that import it used -/

section

/-! Product and cancellation use separate carry registers. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Bignum.Arm.Fios
open VG.Proof.X25519.Arm (Rest wp_str)

private theorem framed {s t : State} {rs : List Reg}
    (h : MacFrame rs s t) : Rest rs s t := ⟨h.regs,h.rd,h.wr,h.sp⟩

theorem productAt_ok (s : State) (dst : Reg) (hdst : dst=.r6 ∨ dst=.r10)
    {base : BitVec 32} {size a d k : Nat}
    (ws : Workspace s base size) (hk : k+4<4096) (fa : a+k+4≤size) (fd : d+k+8≤size)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a) (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.productAt k dst) s fun t =>
      (t.gpr dst).toNat+2^32*(t.gpr .r7).toNat=
        (s.gpr .r1).toNat*w32 s.mem (State.addr base) (a+k)+
        w32 s.mem (State.addr base) (d+k+4)+(s.gpr .r7).toNat ∧
      t.mem=s.mem ∧ Rest [.r3,dst,.r7] s t := by
  rw [VG.Impl.Bignum.Arm.FiosPipelined.productAt,WP.seq_iff]
  refine WP.mono (loadsA_ok s dst (by rcases hdst with rfl|rfl <;> decide) ws
    (by omega_using [hk]) hk fa (by omega_using [fd]) pa pd) ?_
  rintro u ⟨a,t,mem,rest⟩
  simp only [←Nat.add_assoc] at t
  refine WP.mono (umaal_ok u dst .r7 .r3 .r1 (by rcases hdst with rfl|rfl <;> decide)) ?_
  rintro v ⟨value,frame⟩
  rw [a,t,rest.gpr .r1 (by rcases hdst with rfl|rfl <;> simp),
    rest.gpr .r7 (by rcases hdst with rfl|rfl <;> simp),Nat.mul_comm _ (s.gpr .r1).toNat] at value
  exact ⟨by simpa only [w32,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using value,
    frame.mem.trans mem,(rest.mono (by simp)).trans ((framed frame).mono (by simp))⟩

theorem cancelAt_ok (s : State) (dst : Reg) (hdst : dst=.r6 ∨ dst=.r10)
    {base : BitVec 32} {size m d k : Nat}
    (ws : Workspace s base size) (hk : k<4096) (fm : m+k+4≤size) (fd : d+k+4≤size)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m) (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.cancelAt k dst) s fun t =>
      (t.gpr dst).toNat+2^32*(t.gpr .r8).toNat=
        (s.gpr dst).toNat+(s.gpr .r2).toNat*w32 s.mem (State.addr base) (m+k)+(s.gpr .r8).toNat ∧
      t.mem=s.mem.writeW (off (State.addr base) (d+k)) (t.gpr dst) ∧
      Rest [.r5,dst,.r8] s t := by
  rw [VG.Impl.Bignum.Arm.FiosPipelined.cancelAt,WP.seq_iff]
  refine WP.mono (loadsM_ok s ws hk fm pm) ?_
  rintro u ⟨m,mem,rest⟩
  rw [WP.seq_iff]
  refine WP.mono (umaal_ok u dst .r8 .r5 .r2 (by rcases hdst with rfl|rfl <;> decide)) ?_
  rintro v ⟨value,frame⟩
  rw [m,rest.gpr dst (by rcases hdst with rfl|rfl <;> decide),
    rest.gpr .r2 (by decide),rest.gpr .r8 (by decide),Nat.mul_comm _ (s.gpr .r2).toNat] at value
  have rv : Rest [.r5,dst,.r8] s v :=
    (rest.mono (by simp)).trans ((framed frame).mono (by simp))
  have mv : v.mem=s.mem := frame.mem.trans mem
  refine wp_str (a:=off (State.addr base) (d+k)) hk
    ((ws.congr rv.wr).ea ((rv.gpr .r0 (by rcases hdst with rfl|rfl <;> decide)).trans pd) (by omega_using [fd]))
    (by rw [rv.wr];exact ws.write fd) fun t ht => WP.block_nil ?_
  exact ⟨by simpa only [ht.gpr,w32,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using value,
    by rw [ht.mem,mv,ht.gpr],rv.trans (ht.rest _)⟩

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! ### `Bignum.Arm.FiosPipelinedState`, which this module and modules that import it used -/

section

/-! The product carry is one limb ahead of the stored quotient prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Inv (s0 : State) (x q base : BitVec 32) (acc b mod n start i : Nat)
    (pending : Reg) (s : State) : Prop where
  index : i+2≤n
  progress : start≤i
  outPtr : s.gpr .r0=base+BitVec.ofNat 32 (acc+4*start)
  bPtr : s.gpr .r12=base+BitVec.ofNat 32 (b+4*(start+1))
  mPtr : s.gpr .r4=base+BitVec.ofNat 32 (mod+4*(start+1))
  count : s.gpr .lr=BitVec.ofNat 32 (n-(start+1))
  scalar : s.gpr .r1=x
  quotient : s.gpr .r2=q
  outside : Outside (State.addr base) acc (4*i) s0.mem s.mem
  value : 2^32*val32 s.mem (State.addr base) acc i+
      2^(32*(i+1))*((s.gpr pending).toNat+(s.gpr .r8).toNat)+
      2^(32*(i+2))*(s.gpr .r7).toNat=
    val32 s0.mem (State.addr base) acc (i+2)+
      x.toNat*val32 s0.mem (State.addr base) b (i+2)+
      q.toNat*val32 s0.mem (State.addr base) mod (i+1)
  rest : Rest roundClobbers s0 s

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! Issue a product, then cancel the preceding product in the other register. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

abbrev clobbers : List Reg := [.r3,.r5,.r6,.r7,.r8,.r10]

theorem step_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    {pending next : Reg} (regs : (pending=.r6 ∧ next=.r10) ∨ (pending=.r10 ∧ next=.r6))
    (ctx : Fios.Ctx s0 base size acc b mod n)
    (h : Inv s0 x q base acc b mod n start i pending s)
    (hi : i+3≤n) (offsetFits : 4*(i-start)+8<4096) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.step (4*(i-start)) pending next) s
      (Inv s0 x q base acc b mod n start (i+1) next) := by
  have hp : pending=.r6 ∨ pending=.r10 := by rcases regs with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
  have hn : next=.r6 ∨ next=.r10 := by rcases regs with ⟨_,rfl⟩|⟨_,rfl⟩ <;> simp
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have progress := h.progress
  have ws := ctx.workspace.congr h.rest.wr
  rw [VG.Impl.Bignum.Arm.FiosPipelined.step,WP.seq_iff]
  refine WP.mono (productAt_ok s next hn ws (by omega_using [offsetFits]) (by omega_using [hi, inf, progress]) (by omega_using [hi, outf, progress]) h.bPtr h.outPtr) ?_
  rintro u ⟨product,memU,restU⟩
  have eB : b+4*(start+1)+(4*(i-start)+4)=b+4*(i+2) := by omega_using [progress]
  have eT : acc+4*start+(4*(i-start)+4)+4=acc+4*(i+2) := by omega_using [progress]
  have oldB := h.outside.w32 (d:=b+4*(i+2)) (by rcases ctx.accB with h|h <;> omega_arith) (by omega_using [hi, nowrap, inf])
  have oldT := h.outside.w32 (d:=acc+4*(i+2)) (by omega_using []) (by omega_using [hi, nowrap, outf])
  rw [eB,eT,h.scalar,oldB,oldT] at product
  refine WP.mono (cancelAt_ok u pending hp (ws.congr restU.wr) (by omega_using [offsetFits]) (by omega_using [hi, modf, progress]) (by omega_using [hi, outf, progress])
    ((restU.gpr .r4 (by rcases hn with rfl|rfl <;> decide)).trans h.mPtr)
    ((restU.gpr .r0 (by rcases hn with rfl|rfl <;> decide)).trans h.outPtr)) ?_
  rintro v ⟨cancel,memV,restV⟩
  have eM : mod+4*(start+1)+4*(i-start)=mod+4*(i+1) := by omega_using [progress]
  have eO : acc+4*start+4*(i-start)=acc+4*i := by omega_using [progress]
  rw [eO,memU] at memV
  have oldM := h.outside.w32 (d:=mod+4*(i+1)) (by rcases ctx.accM with h|h <;> omega_arith) (by omega_using [hi, nowrap, modf])
  rw [memU,eM,oldM,restU.gpr pending (by rcases regs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),
    restU.gpr .r2 (by rcases hn with rfl|rfl <;> decide),h.quotient,
    restU.gpr .r8 (by rcases hn with rfl|rfl <;> decide)] at cancel
  have productFinal : (v.gpr next).toNat+2^32*(v.gpr .r7).toNat=
      w32 s0.mem (State.addr base) (acc+4*(i+2))+
      x.toNat*w32 s0.mem (State.addr base) (b+4*(i+2))+(s.gpr .r7).toNat := by
    rw [restV.gpr next (by rcases regs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),
      restV.gpr .r7 (by rcases hp with rfl|rfl <;> decide)]
    omega_using [product]
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨writes,stored⟩ := store_prefix nowrap' (by omega_using [hi, outf]) memV
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem v.mem :=
    (h.outside.mono (Nat.le_refl _) (by omega_using [])).trans (writes.mono (by omega_using []) (by omega_using []))
  have rest : Rest clobbers s v :=
    (restU.mono (by rcases hn with rfl|rfl <;> simp [clobbers])).trans
      (restV.mono (by rcases hp with rfl|rfl <;> simp [clobbers]))
  refine ⟨by omega_using [hi],by omega_using [progress],?_,?_,?_,?_,?_,?_,outside,?_,?_⟩
  · rw [rest.gpr .r0 (by decide)];exact h.outPtr
  · rw [rest.gpr .r12 (by decide)];exact h.bPtr
  · rw [rest.gpr .r4 (by decide)];exact h.mPtr
  · rw [rest.gpr .lr (by decide)];exact h.count
  · rw [rest.gpr .r1 (by decide)];exact h.scalar
  · rw [rest.gpr .r2 (by decide)];exact h.quotient
  · exact step_prefix h.value productFinal cancel stored
  · exact h.rest.trans (rest.mono (by decide))

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! ### `Bignum.Arm.FiosFixedState`, which only this module used -/

section

/-! Prefix progress is independent of the fixed operand cursors. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFixed
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Inv (s0 : State) (x q base : BitVec 32) (acc b mod n start i : Nat) (s : State) : Prop where
  index : i+1≤n
  progress : start≤i
  outPtr : s.gpr .r0=base+BitVec.ofNat 32 (acc+4*start)
  bPtr : s.gpr .r12=base+BitVec.ofNat 32 (b+4*(start+1))
  mPtr : s.gpr .r4=base+BitVec.ofNat 32 (mod+4*(start+1))
  count : s.gpr .lr=BitVec.ofNat 32 (n-(start+1))
  scalar : s.gpr .r1=x
  quotient : s.gpr .r2=q
  outside : Outside (State.addr base) acc (4*i) s0.mem s.mem
  value : 2^32*val32 s.mem (State.addr base) acc i+
      2^(32*(i+1))*((s.gpr .r7).toNat+(s.gpr .r8).toNat)=
    val32 s0.mem (State.addr base) acc (i+1)+
      x.toNat*val32 s0.mem (State.addr base) b (i+1)+
      q.toNat*val32 s0.mem (State.addr base) mod (i+1)
  rest : Rest roundClobbers s0 s

theorem Inv.of_cursor {s0 s : State} {x q base : BitVec 32} {acc b mod n i : Nat}
    (h : Fios.Inv s0 x q base acc b mod n i s) : Inv s0 x q base acc b mod n i i s :=
  ⟨h.index,Nat.le_refl _,h.outPtr,h.bPtr,h.mPtr,h.count,h.scalar,h.quotient,h.outside,h.value,h.rest⟩

end VG.Proof.Bignum.Arm.FiosFixed

end

end

/-! ### `Bignum.Arm.FiosFastChoice`, which only this module used -/

section

/-! Selection changes only flags and compares the public packed-word count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_cmp op2_imm)

def Post (s : State) (base : BitVec 32) (acc b mod n : Nat) (t : State) : Prop :=
  (∃ q<2^32, 2^32*val32 t.mem (State.addr base) acc (n+1)=
    val32 s.mem (State.addr base) acc (n+2)+
    (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
    q*val32 s.mem (State.addr base) mod n) ∧
  t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
  Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧
  Rest roundClobbers s t

theorem Post.prefix {s u t : State} {base : BitVec 32} {acc b mod n : Nat}
    (h : Post u base acc b mod n t) (mem : u.mem=s.mem) (rest : Rest [] s u) :
    Post s base acc b mod n t := by
  obtain ⟨value,ptr,outside,rt⟩ := h
  refine ⟨?_,ptr,?_,(rest.mono (by decide)).trans rt⟩
  · simpa only [mem,rest.gpr .r1 (by decide)] using value
  · simpa only [mem] using outside

theorem choose_ok (s : State) (n k : Nat) (hn : n<2^32) (hk : k<2^32)
    (enc : encodable (BitVec.ofNat 32 k)=true) (count : s.gpr .lr=BitVec.ofNat 32 n) :
    WP isa (.block (VG.Impl.Bignum.Arm.FiosFast.choose (BitVec.ofNat 32 k))) s fun t =>
      t.z=decide (n=k) ∧ t.mem=s.mem ∧ Rest [] s t := by
  unfold VG.Impl.Bignum.Arm.FiosFast.choose
  refine wp_cmp (op2_imm enc) fun t ht zero => WP.block_nil ?_
  refine ⟨?_,ht.mem,ht.rest []⟩
  rw [zero,count]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro eq
    have same : BitVec.ofNat 32 n=BitVec.ofNat 32 k := by
      calc
        _ = (BitVec.ofNat 32 n-BitVec.ofNat 32 k)+BitVec.ofNat 32 k := (BitVec.sub_add_cancel _ _).symm
        _ = _ := by
          rw [eq]
          change 0#32+BitVec.ofNat 32 k=BitVec.ofNat 32 k
          exact BitVec.zero_add _
    have e := congrArg BitVec.toNat same
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hk] using e
  · intro eq
    rw [eq,BitVec.sub_self]
    rfl

end VG.Proof.Bignum.Arm.FiosFast

end

end

/-! ### `Bignum.Arm.FiosPipelinedCode`, which only this module used -/

section

/-! ### `Bignum.Arm.FiosPipelinedStart`, which only this module used -/

section

/-! Issue the first pending product before the streaming scan. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem start_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n)
    (h : FiosFixed.Inv s0 x q base acc b mod n start start s) (hi : start+2≤n) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.productAt 0 .r6) s
      (Inv s0 x q base acc b mod n start start .r6) := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  refine WP.mono (productAt_ok s .r6 (Or.inl rfl) (ctx.workspace.congr h.rest.wr)
    (by decide) (by omega_using [hi, inf]) (by omega_using [hi, outf]) h.bPtr h.outPtr) ?_
  rintro t ⟨value,mem,rest⟩
  simp only [Nat.add_zero] at value
  have oldT := h.outside.w32 (d:=acc+4*(start+1)) (by omega_using []) (by omega_using [hi, nowrap, outf])
  have oldB := h.outside.w32 (d:=b+4*(start+1))
    (by rcases ctx.accB with h|h <;> omega_arith) (by omega_using [hi, nowrap, inf])
  rw [h.scalar,show acc+4*start+4=acc+4*(start+1) by omega_using [],oldT,oldB] at value
  have product : (t.gpr .r6).toNat+2^32*(t.gpr .r7).toNat=
      w32 s0.mem (State.addr base) (acc+4*(start+1))+
      x.toNat*w32 s0.mem (State.addr base) (b+4*(start+1))+(s.gpr .r7).toNat := by omega_using [value]
  refine ⟨hi,Nat.le_refl _,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rest.gpr .r0 (by decide)];exact h.outPtr
  · rw [rest.gpr .r12 (by decide)];exact h.bPtr
  · rw [rest.gpr .r4 (by decide)];exact h.mPtr
  · rw [rest.gpr .lr (by decide)];exact h.count
  · rw [rest.gpr .r1 (by decide)];exact h.scalar
  · rw [rest.gpr .r2 (by decide)];exact h.quotient
  · rw [mem];exact h.outside
  · rw [mem,rest.gpr .r8 (by decide)]
    exact start_prefix h.value product
  · exact h.rest.trans (rest.mono (by decide))

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! ### `Bignum.Arm.FiosPipelinedPairs`, which only this module used -/

section

/-! Alternating two product registers keeps one product pending across pairs. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Bignum.Arm

theorem pair_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (h : Inv s0 x q base acc b mod n start i .r6 s)
    (hi : i+4≤n) (offsetFits : 4*(i-start)+12<4096) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.pair (4*(i-start))) s
      (Inv s0 x q base acc b mod n start (i+2) .r6) := by
  rw [VG.Impl.Bignum.Arm.FiosPipelined.pair,WP.seq_iff]
  refine WP.mono (step_ok (Or.inl ⟨rfl,rfl⟩) ctx h (by omega_using [hi]) (by omega_using [offsetFits])) ?_
  intro t ht
  have next : 4*(i-start)+4=4*(i+1-start) := by have := h.progress;omega_using [this]
  rw [next]
  exact step_ok (Or.inr ⟨rfl,rfl⟩) ctx ht (by omega_using [hi]) (by have := h.progress;omega_using [offsetFits])

theorem pairs_ok {s0 : State} {x q base : BitVec 32} {size acc b mod n start : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) :
    ∀ k i s, Inv s0 x q base acc b mod n start i .r6 s → i+2*k+2≤n →
      4*(i+2*k-start)+12<4096 →
      WP isa (VG.Impl.Bignum.Arm.FiosPipelined.pairs (4*(i-start)) k) s
        (Inv s0 x q base acc b mod n start (i+2*k) .r6)
  | 0, i, s, h, _, _ => by
    simpa only [VG.Impl.Bignum.Arm.FiosPipelined.pairs,Nat.mul_zero,Nat.add_zero] using WP.block_nil h
  | k+1, i, s, h, bound, offset => by
    rw [VG.Impl.Bignum.Arm.FiosPipelined.pairs,WP.seq_iff]
    refine WP.mono (pair_ok ctx h (by omega_using [bound]) (by have := h.progress;omega_using [offset])) ?_
    intro t ht
    have next : 4*(i-start)+8=4*(i+2-start) := by have := h.progress;omega_using [this]
    rw [next]
    have result := pairs_ok ctx k (i+2) t ht (by omega_using [bound]) (by omega_using [offset])
    simpa only [show i+2+2*k=i+2*(k+1) by omega_using []] using result

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! ### `Bignum.Arm.FiosPipelinedFinish`, which only this module used -/

section

/-! Cancel the final pending product and recover the ordinary quotient invariant. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem finish_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    {pending : Reg} (hp : pending=.r6 ∨ pending=.r10)
    (ctx : Fios.Ctx s0 base size acc b mod n)
    (h : Inv s0 x q base acc b mod n start i pending s)
    (offsetFits : 4*(i-start)<4096) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.cancelAt (4*(i-start)) pending) s
      (FiosFixed.Inv s0 x q base acc b mod n start (i+1)) := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have modf := ctx.mFits
  have progress := h.progress
  have index := h.index
  refine WP.mono (cancelAt_ok s pending hp (ctx.workspace.congr h.rest.wr) offsetFits
    (by omega_using [modf, progress, index]) (by omega_using [outf, progress, index]) h.mPtr h.outPtr) ?_
  rintro t ⟨cancel,mem,rest⟩
  have eM : mod+4*(start+1)+4*(i-start)=mod+4*(i+1) := by omega_using [progress]
  have eO : acc+4*start+4*(i-start)=acc+4*i := by omega_using [progress]
  rw [eO] at mem
  have oldM := h.outside.w32 (d:=mod+4*(i+1)) (by rcases ctx.accM with h|h <;> omega_arith) (by omega_using [nowrap, modf, index])
  rw [eM,oldM,h.quotient] at cancel
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨writes,stored⟩ := store_prefix nowrap' (by omega_using [outf, index]) mem
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem t.mem :=
    (h.outside.mono (Nat.le_refl _) (by omega_using [])).trans (writes.mono (by omega_using []) (by omega_using []))
  refine ⟨by omega_using [index],by omega_using [progress],?_,?_,?_,?_,?_,?_,outside,?_,?_⟩
  · rw [rest.gpr .r0 (by rcases hp with rfl|rfl <;> decide)];exact h.outPtr
  · rw [rest.gpr .r12 (by rcases hp with rfl|rfl <;> decide)];exact h.bPtr
  · rw [rest.gpr .r4 (by rcases hp with rfl|rfl <;> decide)];exact h.mPtr
  · rw [rest.gpr .lr (by rcases hp with rfl|rfl <;> decide)];exact h.count
  · rw [rest.gpr .r1 (by rcases hp with rfl|rfl <;> decide)];exact h.scalar
  · rw [rest.gpr .r2 (by rcases hp with rfl|rfl <;> decide)];exact h.quotient
  · rw [rest.gpr .r7 (by rcases hp with rfl|rfl <;> decide)]
    exact finish_prefix h.value cancel stored
  · exact h.rest.trans (rest.mono (by rcases hp with rfl|rfl <;> simp [roundClobbers]))

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! One integrated UMAAL row computes a Montgomery quotient without an intermediate product pass. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosFixedAdvance.lean`, which only this module imported.
section

/-! One encodable update advances the public cursors after a fixed scan. -/

section
namespace VG.Proof.Bignum.Arm.FiosFixed
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_imm dpVal)

theorem advance_ok (s : State) (k : Nat) (h4 : encodable (BitVec.ofNat 32 (4*k))=true)
    (h1 : encodable (BitVec.ofNat 32 k)=true) :
    WP isa (.block (VG.Impl.Bignum.Arm.FiosPipelined.advance k)) s fun t =>
      t.gpr .r0=s.gpr .r0+BitVec.ofNat 32 (4*k) ∧
      t.gpr .r12=s.gpr .r12+BitVec.ofNat 32 (4*k) ∧
      t.gpr .r4=s.gpr .r4+BitVec.ofNat 32 (4*k) ∧
      t.gpr .lr=s.gpr .lr-BitVec.ofNat 32 k ∧
      t.z=(s.gpr .lr-BitVec.ofNat 32 k==0) ∧
      t.mem=s.mem ∧ Rest [.r0,.r12,.r4,.lr] s t := by
  unfold VG.Impl.Bignum.Arm.FiosPipelined.advance
  refine wp_dp (op2_imm h4) fun a ha => ?_
  refine wp_dp (op2_imm h4) fun b hb => ?_
  refine wp_dp (op2_imm h4) fun c hc => ?_
  refine wp_subs (op2_imm h1) fun t ht hz => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .r0 (by decide),hc.other .r0 (by decide),hb.other .r0 (by decide),ha.gpr,dpVal]
  · rw [ht.other .r12 (by decide),hc.other .r12 (by decide),hb.gpr,dpVal,ha.other .r12 (by decide)]
  · rw [ht.other .r4 (by decide),hc.gpr,dpVal,hb.other .r4 (by decide),ha.other .r4 (by decide)]
  · rw [ht.gpr,hc.other .lr (by decide),hb.other .lr (by decide),ha.other .lr (by decide)]
  · rw [hz,hc.other .lr (by decide),hb.other .lr (by decide),ha.other .lr (by decide)]
  · rw [ht.mem,hc.mem,hb.mem,ha.mem]
  · exact (ha.rest (by simp)).trans ((hb.rest (by simp)).trans ((hc.rest (by simp)).trans (ht.rest (by simp))))

end VG.Proof.Bignum.Arm.FiosFixed
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosFixedFinishCursor.lean`, which only this module imported.
section

/-! Advance the cursors once after the fixed scan. -/

section
namespace VG.Proof.Bignum.Arm.FiosFixed
open VG VG.Arm VG.Proof.Bignum.Arm

theorem finishCursor_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (h : Inv s0 x q base acc b mod n start i s)
    (h4 : encodable (BitVec.ofNat 32 (4*(i-start)))=true)
    (h1 : encodable (BitVec.ofNat 32 (i-start))=true) :
    WP isa (.block (VG.Impl.Bignum.Arm.FiosPipelined.advance (i-start))) s
      (Fios.Inv s0 x q base acc b mod n i) := by
  refine WP.mono (advance_ok s (i-start) h4 h1) ?_
  rintro t ⟨p0,p12,p4,count,_,mem,rt⟩
  have small : n<2^32 := by have := ctx.workspace.nowrap;have := ctx.accFits;omega
  refine ⟨h.index,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [p0,h.outPtr,Offset.add_add]
    congr 2
    have := h.progress;omega
  · rw [p12,h.bPtr,Offset.add_add]
    congr 2
    have := h.progress;omega
  · rw [p4,h.mPtr,Offset.add_add]
    congr 2
    have := h.progress;omega
  · rw [count,h.count,BitVec.ofNat_sub_ofNat_of_le _ _ (by have := h.index;omega) (by have := h.progress;have := h.index;omega)]
    congr 1
    have := h.progress;have := h.index;omega
  · rw [rt.gpr .r1 (by decide)];exact h.scalar
  · rw [rt.gpr .r2 (by decide)];exact h.quotient
  · rw [mem];exact h.outside
  · rw [mem,rt.gpr .r7 (by decide),rt.gpr .r8 (by decide)];exact h.value
  · exact h.rest.trans (rt.mono (by decide))

end VG.Proof.Bignum.Arm.FiosFixed
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Bignum.Arm.Fios

theorem code_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Ctx s base size acc b mod n) (positive : 4≤n) (even : n%2=0) (bound : n≤32)
    (h4 : encodable (BitVec.ofNat 32 (4*(n-2)))=true)
    (h1 : encodable (BitVec.ofNat 32 (n-2))=true)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 b)
    (modulus : s.gpr .r4=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carryA : s.gpr .r7=0) (carryM : s.gpr .r8=0)
    (inverse : (val32 s.mem (State.addr base) mod n*(s.gpr .r2).toNat+1)%2^32=0)
    (capacity : ∀ q<2^32, val32 s.mem (State.addr base) acc (n+2)+
      (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
      q*val32 s.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.code n) s fun t =>
      (∃ q<2^32, 2^32*val32 t.mem (State.addr base) acc (n+1)=
        val32 s.mem (State.addr base) acc (n+2)+
        (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
        q*val32 s.mem (State.addr base) mod n) ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧
      VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have small : n<2^32 := by omega_arith
  have split : val32 s.mem (State.addr base) mod n=
      w32 s.mem (State.addr base) mod+2^32*val32 s.mem (State.addr base) (mod+4) (n-1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n-1)+1) := by congr 1;omega_arith
      _ = _ := rfl
  have inverseLow : (w32 s.mem (State.addr base) mod*(s.gpr .r2).toNat+1)%2^32=0 := by
    rw [split,Nat.add_mul,Nat.add_right_comm,Nat.mul_assoc,Nat.add_mul_mod_self_left] at inverse
    exact inverse
  rw [VG.Impl.Bignum.Arm.FiosPipelined.code,WP.seq_iff]
  refine WP.mono (first_ok s ctx.workspace (by have := ctx.bFits;omega_arith)
    (by have := ctx.mFits;omega_arith) (by omega_arith) source modulus ptr count (by omega_arith) small carryA carryM inverseLow) ?_
  rintro u ⟨fv,_fq,_qb,p0,p12,p4,lr,scalar,mem,rest⟩
  let x := s.gpr .r1
  let q := u.gpr .r2
  have initial : Fios.Inv s x q base acc b mod n 0 u := by
    refine ⟨by omega_arith,?_,?_,?_,?_,scalar,rfl,?_,?_,rest⟩
    · simpa only [Nat.mul_zero,Nat.add_zero] using p0
    · simpa only [Nat.zero_add,Nat.mul_one] using p12
    · simpa only [Nat.zero_add,Nat.mul_one] using p4
    · simpa only [Nat.zero_add] using lr
    · rw [mem];exact Outside.refl _ _ _ _
    · simpa only [x,q,val32,Nat.zero_add,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.mul_one] using fv
  rw [WP.seq_iff]
  refine WP.mono (body_ok ctx initial (by omega_arith)) ?_
  rintro v ⟨iv,_zv⟩
  rw [WP.seq_iff]
  refine WP.mono (start_ok ctx (FiosFixed.Inv.of_cursor iv) (by omega_arith)) ?_
  intro a ia
  rw [WP.seq_iff]
  have scan := pairs_ok ctx ((n-4)/2) 1 a ia (by omega_arith) (by omega_arith)
  refine WP.mono scan ?_
  intro b ib
  have index : 1+2*((n-4)/2)=n-3 := by omega_arith
  rw [index] at ib
  rw [WP.seq_iff]
  have last := step_ok (Or.inl ⟨rfl,rfl⟩) ctx ib (by omega_arith)
    (by have := ib.progress;omega_arith)
  have lastOffset : 4*(n-3-1)=4*(n-4) := by omega_arith
  simp only [lastOffset] at last
  refine WP.mono last ?_
  intro c ic
  have nextIndex : n-3+1=n-2 := by omega_arith
  rw [nextIndex] at ic
  rw [WP.seq_iff]
  have flush := finish_ok (Or.inr rfl) ctx ic (by have := ic.progress;omega_arith)
  have flushOffset : 4*(n-2-1)=4*(n-3) := by omega_arith
  simp only [flushOffset] at flush
  refine WP.mono flush ?_
  intro w iw
  have finalIndex : n-2+1=n-1 := by omega_arith
  rw [finalIndex] at iw
  rw [WP.seq_iff]
  have cursor := FiosFixed.finishCursor_ok (start:=1) (i:=n-1) ctx iw
    (by simpa only [show n-1-1=n-2 by omega_arith] using h4)
    (by simpa only [show n-1-1=n-2 by omega_arith] using h1)
  simp only [show n-1-1=n-2 by omega_arith] at cursor
  refine WP.mono cursor ?_
  intro z iz
  refine WP.mono (Fios.finish_ok ctx (by omega_arith) iz (capacity q.toNat q.isLt)) ?_
  rintro t ⟨value,pt,outside,rt⟩
  exact ⟨⟨q.toNat,q.isLt,value⟩,pt,outside,rt⟩

end VG.Proof.Bignum.Arm.FiosPipelined

end

end

/-! The integrated scan meets the unchanged complete Montgomery round contract. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FiosFastCode.lean`, which only this module imported.
section

/-! Fixed and general scans meet the same arithmetic and memory postcondition. -/

section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem code_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s base size acc b mod n) (positive : 4≤n) (even : n%2=0)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 b)
    (modulus : s.gpr .r4=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carryA : s.gpr .r7=0) (carryM : s.gpr .r8=0)
    (inverse : (val32 s.mem (State.addr base) mod n*(s.gpr .r2).toNat+1)%2^32=0)
    (capacity : ∀ q<2^32, val32 s.mem (State.addr base) acc (n+2)+
      (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
      q*val32 s.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa VG.Impl.Bignum.Arm.FiosFast.code s (Post s base acc b mod n) := by
  have small : n<2^32 := by have := ctx.workspace.nowrap;have := ctx.accFits;omega
  have ws (u : State) (r : Rest [] s u) : Fios.Ctx u base size acc b mod n :=
    ⟨ctx.workspace.congr r.wr,ctx.accFits,ctx.bFits,ctx.mFits,ctx.accB,ctx.accM⟩
  have fixed (u : State) (r : Rest [] s u) (mem : u.mem=s.mem) (special : n=16 ∨ n=32) :
      WP isa (VG.Impl.Bignum.Arm.FiosPipelined.code n) u (Post s base acc b mod n) := by
    refine WP.mono (FiosPipelined.code_ok u (ws u r) positive even
      (by rcases special with rfl|rfl <;> decide)
      (by rcases special with rfl|rfl <;> decide)
      (by rcases special with rfl|rfl <;> decide)
      (by rw [r.gpr .r0 (by simp)];exact ptr)
      (by rw [r.gpr .r12 (by simp)];exact source)
      (by rw [r.gpr .r4 (by simp)];exact modulus)
      (by rw [r.gpr .lr (by simp)];exact count)
      (by rw [r.gpr .r7 (by simp)];exact carryA)
      (by rw [r.gpr .r8 (by simp)];exact carryM)
      (by rw [mem,r.gpr .r2 (by simp)];exact inverse)
      (by intro q hq;rw [mem,r.gpr .r1 (by simp)];exact capacity q hq)) ?_
    exact fun _ h => Post.prefix h mem r
  have general (u : State) (r : Rest [] s u) (mem : u.mem=s.mem) :
      WP isa VG.Impl.Bignum.Arm.Fios.code u (Post s base acc b mod n) := by
    refine WP.mono (Fios.code_ok u (ws u r) positive even
      (by rw [r.gpr .r0 (by simp)];exact ptr)
      (by rw [r.gpr .r12 (by simp)];exact source)
      (by rw [r.gpr .r4 (by simp)];exact modulus)
      (by rw [r.gpr .lr (by simp)];exact count)
      (by rw [r.gpr .r7 (by simp)];exact carryA)
      (by rw [r.gpr .r8 (by simp)];exact carryM)
      (by rw [mem,r.gpr .r2 (by simp)];exact inverse)
      (by intro q hq;rw [mem,r.gpr .r1 (by simp)];exact capacity q hq)) ?_
    exact fun _ h => Post.prefix h mem r
  rw [VG.Impl.Bignum.Arm.FiosFast.code,WP.seq_iff]
  refine WP.mono (choose_ok s n 16 small (by decide) (by decide) count) ?_
  rintro u ⟨z1,m1,r1⟩
  refine WP.ite u.z rfl ?_ ?_
  · intro selected
    have eq : n=16 := of_decide_eq_true (z1.symm.trans selected)
    subst n
    exact fixed u r1 m1 (Or.inl rfl)
  · intro _
    rw [WP.seq_iff]
    refine WP.mono (choose_ok u n 32 small (by decide) (by decide)
      (by rw [r1.gpr .lr (by simp)];exact count)) ?_
    rintro v ⟨z2,m2,r2⟩
    refine WP.ite v.z rfl ?_ ?_
    · intro selected
      have eq : n=32 := of_decide_eq_true (z2.symm.trans selected)
      subst n
      exact fixed v (r1.trans r2) (m2.trans m1) (Or.inr rfl)
    · intro _
      exact general v (r1.trans r2) (m2.trans m1)

end VG.Proof.Bignum.Arm.FiosFast
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm.Fios

theorem round_law : MontPipeline.RoundLaw VG.Impl.Bignum.Arm.FiosFast.round := by
  intro s base size tmp a b mod acc n i inv ctx even hdr hi ptr hT hB hInv
  have count := ctx.count
  rw [VG.Impl.Bignum.Arm.FiosFast.round,WP.seq_iff]
  refine WP.mono (args_ok s ctx hdr hi ptr) ?_
  rintro u ⟨scalar,p0,p12,p4,p2,cnt,carryA,carryM,memU,restU⟩
  let c : Fios.Ctx u base size acc b mod n :=
    ⟨ctx.workspace.congr restU.wr,ctx.accFits,ctx.bFits,ctx.mFits,ctx.accB,ctx.accM⟩
  rw [WP.seq_iff]
  refine WP.mono (code_ok u c (by omega_using [count]) even p0 p12 p4 cnt carryA carryM ?_ ?_) ?_
  · simpa only [memU,p2] using hInv
  · intro q hq
    rw [memU,scalar]
    exact round_fit hT (s.mem.readW (off (State.addr base) (a+4*i)) 32).isLt
      hB hq (val32_lt s.mem (State.addr base) mod n)
  · rintro v ⟨quotient,ptrV,outsideV,keepV⟩
    rw [memU,scalar] at quotient
    rw [memU] at outsideV
    exact finishRound_ok s v ctx hdr hi hT hB quotient ptrV outsideV
      ((restU.mono (by decide)).trans keepV)

end VG.Proof.Bignum.Arm.FiosFast
