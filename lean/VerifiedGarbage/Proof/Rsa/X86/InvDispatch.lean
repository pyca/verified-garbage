module
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.InvGate
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Rsa.X86.InvStep
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.FrameBase
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Body
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # Public-length selection of the verified batched inverse -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
 VG.Proof.Weierstrass VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)
open VG.Impl.Rsa.X86.CrtValuesRt (lay)
open VG.Impl.Rsa.X86.CrtValues (nArr)
open VG.Proof.Weierstrass.X86.Inv (wordClob)

 def inverseM (P : Nat) := 2*(P/2)+1
 structure InvInput (args : Nat → BitVec 32) (base : Addr) (size len P Q : Nat) (s : State) : Prop where
  ws : RtWs lay s base size len nArr
  gate : InvGate args base size P Q s
  u : num s.mem base (kw len) 0=Q
  m : num s.mem base (kw len) aM=inverseM P
  nm : num s.mem base (kw len) aNM+inverseM P=2^(32*kw len)
  zero : num s.mem base (kw len) aZero=0
  bank : bank s.mem base (kw len) 0=(Q,inverseM P,1,0)

 def InvPost (base : Addr) (size len P Q : Nat) (s t : State) : Prop :=
  RtWs lay t base size len nArr ∧ Keep base (kw len) invArrs invSlots s.mem t.mem ∧ Keeps wordClob s t ∧
  (1<inverseM P → num t.mem base (kw len) 1=Nat.gcd Q (inverseM P) ∧
   (inverseM P : Int)∣(num t.mem base (kw len) 3 : Int)*Q-num t.mem base (kw len) 1 ∧
   num t.mem base (kw len) 3<inverseM P)

 omit rsaBatchLaw in
 theorem InvInput.rest {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s t : State} {regs : List Reg}
    (h : InvInput args base size len P Q s) (K : Keeps regs s t) (di : .edi∉regs) (sp : .esp∉regs)
    (mem : t.mem=s.mem) : InvInput args base size len P Q t := by
  have O : Outside base 0 size s.mem t.mem := by rw [mem]; exact Outside.refl _ _ _ _
  exact ⟨h.ws.keep K di sp O,h.gate.keep K sp O,mem ▸ h.u,mem ▸ h.m,mem ▸ h.nm,mem ▸ h.zero,mem ▸ h.bank⟩

 omit rsaBatchLaw in
 theorem inverseFallback_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.inverse lay) s (InvPost base size len P Q s) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.inverse_ok h.ws (by decide)) fun t ⟨ht,K,R,I⟩ => ?_
  refine ⟨ht,K,R.mono (by decide),?_⟩
  intro large
  have v := I (by rw [h.m,h.nm]) h.zero (by rw [h.m]; unfold inverseM; omega)
    (by rw [h.m]; exact large) (by rw [h.bank,h.u,h.m])
  simpa only [h.m,h.u] using v

 theorem inverseBody_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q w n : Nat} {s : State}
    (h : InvInput args base size len P Q s) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0)
    (width : kw len=w) (pb : (args 9).toNat≤4*n) (qb : (args 11).toNat≤4*n) :
    WP isa (VG.Impl.Rsa.X86.InvBatch.body w n) s (InvPost base size len P Q s) := by
  have hs := h.ws.ws.workspace
  have nw := hs.nowrap
  have hz : VG.Impl.Rsa.X86.InvBatch.offset w 15≤size := by
    change VG.Impl.Rsa.X86.GcdBatch.offset w 15≤size
    rw [VG.Impl.Rsa.X86.GcdBatch.offset]
    have fits := h.ws.ws.fits
    rw [width] at fits
    dsimp only [arr,S,VG.Impl.Rsa.X86.Keys.hdr,VG.Impl.Rsa.X86.CrtValues.nArr] at fits
    omega
  have offeq (j : Nat) : VG.Impl.Rsa.X86.InvBatch.offset w j=arr (kw len) j := by
    rw [width]; dsimp only [VG.Impl.Rsa.X86.InvBatch.offset,arr,S,VG.Impl.Rsa.X86.Keys.hdr]
    rw [show 4*(w+2)=4*w+8 by omega]
  have pc : inverseM P<2^(32*n) := odd_modulus_bound (by omega) (prime_bound h.gate.pBound pb)
  have qc : Q<2^(32*n) := prime_bound h.gate.qBound qb
  have mv : val32 s.mem base (VG.Impl.Rsa.X86.InvBatch.offset w 8) n=inverseM P := by
    rw [offeq]
    change val32 s.mem base (arr (kw len) aM) n=inverseM P
    have v : val32 s.mem base (arr (kw len) aM) (kw len)=inverseM P := h.m
    rw [prefix_eq (w:=kw len) (by omega) (by change val32 s.mem base (arr (kw len) aM) (kw len)<_; rw [v]; exact pc),v]
  have qv : val32 s.mem base (VG.Impl.Rsa.X86.InvBatch.offset w 0) n=Q := by
    rw [offeq]
    have v : val32 s.mem base (arr (kw len) 0) (kw len)=Q := h.u
    rw [prefix_eq (w:=kw len) (by omega) (by rw [v]; exact qc),v]
  refine WP.mono (InvBatch.body_ok hs hn nl hw he hz mv qv (by unfold inverseM; omega)) fun t ⟨G,A,small,R,O⟩ => ?_
  have bankKeep : Keep base (kw len) invArrs invSlots s.mem t.mem := by
    rw [width]
    exact GcdBatch.own_keep O
  have outside := keep_outside h.ws.ws bankKeep (by decide) (by decide)
  refine ⟨h.ws.keep R (by decide) (by decide) outside,bankKeep,R,?_⟩
  intro large
  have vm : InvBatch.virtualMod (inverseM P)=inverseM P := by unfold InvBatch.virtualMod; rw [ite_eq_right (by omega)]
  simp only [vm,←width] at G A small
  change num t.mem base (kw len) 1=Nat.gcd (inverseM P) Q at G
  change (inverseM P : Int)∣(num t.mem base (kw len) 3 : Int)*Q-(Nat.gcd (inverseM P) Q : Int) at A
  change num t.mem base (kw len) 3<inverseM P at small
  refine ⟨G.trans (Nat.gcd_comm _ _),?_,small⟩
  rw [G]; exact A

end VG.Proof.Rsa.X86.CrtValuesRt
