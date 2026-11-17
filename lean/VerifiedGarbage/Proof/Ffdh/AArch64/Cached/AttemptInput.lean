module

public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NativeTimingState
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Finish
public import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.DomainFacts
public import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Ffdh.AArch64.Cached.CheckedParameters`, which this module and modules that import it used -/

section

/-! Every checked API domain supplies the native comb's arithmetic geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Proof.Bignum

def checkedParameters (B src ctx : Addr) (Z k : Nat) (dom : List Byte)
 (room : slot ((k+7)/8) 8≤Z) (small : 64≤k) (large : k≤1024)
 (valid : Spec.Ffdh.domainValid k dom=true) : Parameters := by
 have modulus := VG.Proof.Ffdh.domainValid_mod valid
 simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at modulus
 exact {
  B:=B,Z:=Z,w:=(k+7)/8,mi:=0,P:=(Spec.Ffdh.domainOf k dom).p,G:=(Spec.Ffdh.domainOf k dom).g,
  N:=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom),k:=k,src:=src,ctx:=ctx,
  table:=ctx+BitVec.ofNat 64 (24+16*((k+7)/8)),room:=room,positive:=by omega_using [small],width:=by omega_using [large],
  modulusPositive:=by omega_using [modulus],coprime:=coprime_pow2 modulus.1.1.1 (64*((k+7)/8)) }

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.AttemptContract`, which this module and modules that import it used -/

section

/-! The reviewed cached-attempt contract in native register and stack coordinates. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt i2osp powMod)

abbrev attemptDomain (s : State) : List Byte :=bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
abbrev attemptRandom (s : State) : List Byte :=bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
abbrev attemptParameters (s : State) : Spec.Ffdh.Parameters :=domainOf (s.gpr .x6).toNat (attemptDomain s)
abbrev attemptScalar (s : State) : Nat :=vettedScalarOfOctets (attemptParameters s) (attemptRandom s)

def attemptPre (s : State) : Prop :=
 let xr : Region:=⟨s.gpr .x0,(s.gpr .x1).toNat⟩
 let yr : Region:=⟨s.gpr .x2,(s.gpr .x3).toNat⟩
 let dom : Region:=⟨s.gpr .x4,(s.gpr .x5).toNat⟩
 let rnd : Region:=⟨s.gpr .x7,(stackArg s 0).toNat⟩
 let scr : Region:=⟨stackArg s 1,(stackArg s 2).toNat*8⟩
 let ctx : Region:=⟨stackArg s 3,(stackArg s 4).toNat*8⟩
 let args : Region:=⟨stackArgAddr s 0,40⟩
 s.sp.toNat+40≤2^64 ∧ s.rd=[dom,rnd,ctx,args] ∧ s.wr=[xr,yr,scr] ∧
 xr.Disjoint yr ∧ xr.Disjoint dom ∧ xr.Disjoint rnd ∧ xr.Disjoint scr ∧ xr.Disjoint ctx ∧ xr.Disjoint args ∧
 yr.Disjoint dom ∧ yr.Disjoint rnd ∧ yr.Disjoint scr ∧ yr.Disjoint ctx ∧ yr.Disjoint args ∧
 dom.Disjoint scr ∧ rnd.Disjoint scr ∧ scr.Disjoint ctx ∧ scr.Disjoint args ∧
 (s.gpr .x0).toNat+(s.gpr .x1).toNat≤2^64 ∧ (s.gpr .x2).toNat+(s.gpr .x3).toNat≤2^64 ∧
 (s.gpr .x4).toNat+(s.gpr .x5).toNat≤2^64 ∧ (s.gpr .x7).toNat+(stackArg s 0).toNat≤2^64 ∧
 (stackArg s 1).toNat+(stackArg s 2).toNat*8≤2^64 ∧ (stackArg s 3).toNat+(stackArg s 4).toNat*8≤2^64 ∧
 pLenValid (s.gpr .x6).toNat ∧ domainLenValid (s.gpr .x6).toNat (s.gpr .x5).toNat ∧
 (s.gpr .x1).toNat=(s.gpr .x6).toNat ∧ (s.gpr .x3).toNat=(s.gpr .x6).toNat ∧
 (stackArg s 0).toNat=(s.gpr .x6).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x6).toNat≤(stackArg s 2).toNat ∧
 domainValid (s.gpr .x6).toNat (attemptDomain s) ∧
 generationContextAt s.mem (stackArg s 3) (stackArg s 4).toNat (s.gpr .x6).toNat (attemptDomain s)

def attemptPost (s t : State) : Prop :=
 ((t.gpr .x0).setWidth 32).toNat=keyStatus (attemptParameters s) (attemptScalar s) ∧
 if keyStatus (attemptParameters s) (attemptScalar s)=1 then
  bytesAt t.mem (s.gpr .x0) (s.gpr .x6).toNat=i2osp (attemptScalar s) (s.gpr .x6).toNat ∧
  bytesAt t.mem (s.gpr .x2) (s.gpr .x6).toNat=i2osp (powMod (attemptParameters s).g (attemptScalar s) (attemptParameters s).p) (s.gpr .x6).toNat
 else bytesAt t.mem (s.gpr .x0) (s.gpr .x6).toNat=List.replicate (s.gpr .x6).toNat 0 ∧
  bytesAt t.mem (s.gpr .x2) (s.gpr .x6).toNat=List.replicate (s.gpr .x6).toNat 0

def attemptLeak (s : State) : List Nat :=
 (attemptDomain s).map (·.toNat)++[keyStatus (attemptParameters s) (attemptScalar s)]

def attemptPub (s t : State) : Prop :=
 (∀ r∈argRegs,s.gpr r=t.gpr r) ∧ s.sp=t.sp ∧
 (List.range 5).map (stackArg s)=(List.range 5).map (stackArg t) ∧ attemptLeak s=attemptLeak t

def attemptContract : Contract isa where
 pre:=attemptPre
 post:=attemptPost
 pub:=attemptPub

theorem stackArgs_five (s : State) :
 (List.range 5).map (stackArg s)=[stackArg s 0,stackArg s 1,stackArg s 2,stackArg s 3,stackArg s 4] :=rfl

theorem attempt_shared_pre {s : State} (h : (Proof.Ffdh.cachedGenerateKeyContract abi).pre s) : attemptPre s :=by
 sig_pre [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptPre,stackArgs_five,List.append_eq,
  pLenValid,domainLenValid, List.range, List.range.loop] at h
 sig_pre [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptPre,stackArgs_five,List.append_eq,
  pLenValid,domainLenValid, List.range, List.range.loop] at h
 sig_split h
 sig_reduce [Proof.Ffdh.cachedGenerateKeyContract,Proof.Ffdh.cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptPre,stackArgs_five,
  List.append_eq,pLenValid,domainLenValid, List.range, List.range.loop]
 sig_and_intros
 sig_close
 all_goals first | with_reducible assumption | exact ⟨by assumption,by assumption⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.AttemptGeometry`, which only this module used -/

section

/-! ### `Ffdh.AArch64.GenerateKey.Stages`, which only this module used -/

section

/-! ### `Ffdh.AArch64.GenerateKey.Bound`, which only this module used -/

section

/-!
# `vg_ffdh_generate_key` on AArch64: the bound

The bound's octets (`KeyScalar.bnd`: q's, or p's), the index of their first
nonzero one, and that octet.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh.KeyScalar (bnd bnd_length)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The bound's octets. -/
abbrev FD.bb (D : FD) : List Byte := bnd D.k D.dom

/-- Their first nonzero octet's index. -/
abbrev FD.bl (D : FD) : Nat := lead D.bb

/-- That octet. -/
abbrev FD.bc (D : FD) : Byte := D.bb.getD D.bl 0

end VG.Proof.Ffdh.AArch64

end

end


/-!
# `vg_ffdh_generate_key` on AArch64: a run's data up to the scalar

The public data (`GkP`) are the working space, the lengths, the pointers,
the domain, and whether the scalar is in range; the random octets are
secret. With the public data `p` and the octets `rb`, a run's data are
`p.D₀ rb` (the random octets an input) up to the scalar's octets in `x`
(`GkP.xo`), and `p.D₁ rb` (the scalar's octets an input) after them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data. -/
structure GkP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  xp : Addr
  yp : Addr
  rp : Addr
  /-- Whether the scalar is in range. -/
  pv : Bool
  sp : Addr

/-- The run's data, with the random octets an input. -/
def GkP.D₀ (p : GkP) (rb : List Byte) : FD :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, [(sX, p.xp), (sY, p.yp), (sRand, p.rp)], [(p.rp, rb)]⟩

@[simp] theorem GkP.D₀_B (p : GkP) (rb : List Byte) : (p.D₀ rb).B = p.B := rfl
@[simp] theorem GkP.D₀_Z (p : GkP) (rb : List Byte) : (p.D₀ rb).Z = p.Z := rfl
@[simp] theorem GkP.D₀_k (p : GkP) (rb : List Byte) : (p.D₀ rb).k = p.k := rfl
@[simp] theorem GkP.D₀_dl (p : GkP) (rb : List Byte) : (p.D₀ rb).dl = p.dl := rfl
@[simp] theorem GkP.D₀_dp (p : GkP) (rb : List Byte) : (p.D₀ rb).dp = p.dp := rfl
@[simp] theorem GkP.D₀_dom (p : GkP) (rb : List Byte) : (p.D₀ rb).dom = p.dom := rfl

/-- The mask of the bound's first nonzero octet. -/
abbrev GkP.msk (p : GkP) (rb : List Byte) : BitVec 64 :=
  BitVec.ofNat 64 (KeyScalar.smearN (p.D₀ rb).bc.toNat)

/-- The scalar's octets. -/
def GkP.xo (p : GkP) (rb : List Byte) : List Byte := KeyScalar.cut rb (p.D₀ rb).bl ((p.msk rb).setWidth 8)

/-- The run's data, with the scalar's octets an input. -/
abbrev GkP.D₁ (p : GkP) (rb : List Byte) : FD := (p.D₀ rb).withSrcs [(p.xp, p.xo rb)]

/-- Bytes of regions apart are apart. -/
theorem ne_of_disj {a b : Addr} {n m i j : Nat} (hd : (⟨a, n⟩ : Region).Disjoint ⟨b, m⟩) (ha : a.toNat + n ≤ 2 ^ 64)
    (hb : b.toNat + m ≤ 2 ^ 64) (hi : i < n) (hj : j < m) : a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j :=
  fun he => hd _ (contains_byte a hi (by omega_arith)) (he ▸ contains_byte b hj (by omega_arith))

/-! ## The scalar's octets -/

@[simp] theorem GkP.D₁_B (p : GkP) (rb : List Byte) : (p.D₁ rb).B = p.B := rfl
@[simp] theorem GkP.D₁_Z (p : GkP) (rb : List Byte) : (p.D₁ rb).Z = p.Z := rfl
@[simp] theorem GkP.D₁_k (p : GkP) (rb : List Byte) : (p.D₁ rb).k = p.k := rfl
@[simp] theorem GkP.D₁_dl (p : GkP) (rb : List Byte) : (p.D₁ rb).dl = p.dl := rfl
@[simp] theorem GkP.D₁_dp (p : GkP) (rb : List Byte) : (p.D₁ rb).dp = p.dp := rfl
@[simp] theorem GkP.D₁_dom (p : GkP) (rb : List Byte) : (p.D₁ rb).dom = p.dom := rfl

end VG.Proof.Ffdh.AArch64.GenerateKey

end

end


/-! The reviewed buffer layout supplies every native input, output, alias and context-read obligation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure AttemptGeometry (s : State) : Prop where
 small : 64≤(s.gpr .x6).toNat
 large : (s.gpr .x6).toNat≤1024
 shape : (s.gpr .x5).toNat=2*(s.gpr .x6).toNat ∨ (s.gpr .x5).toNat=3*(s.gpr .x6).toNat
 randLength : (stackArg s 0).toNat=(s.gpr .x6).toNat
 room : slot (((s.gpr .x6).toNat+7)/8) 8≤(stackArg s 2).toNat*8
 scratch : Scr s (stackArg s 1) ((stackArg s 2).toNat*8)
 stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8
 stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8
 domain : Src s (stackArg s 1) ((stackArg s 2).toNat*8) (s.gpr .x4) (attemptDomain s)
 random : Src s (stackArg s 1) ((stackArg s 2).toNat*8) (s.gpr .x7) (attemptRandom s)
 view : ContextView (stackArg s 1) ((stackArg s 2).toNat*8) (stackArg s 3) (stackArg s 4).toNat
  (s.gpr .x6).toNat (attemptDomain s) s
 checked : Spec.Ffdh.domainValid (s.gpr .x6).toNat (attemptDomain s)=true
 writeX : ∀ i<(s.gpr .x6).toNat,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 i) 1
 writeY : ∀ i<(s.gpr .x6).toNat,InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 i) 1
 outsideX : ∀ i<(s.gpr .x6).toNat,(stackArg s 2).toNat*8≤ofs (stackArg s 1) (s.gpr .x0+BitVec.ofNat 64 i)
 outsideY : ∀ i<(s.gpr .x6).toNat,(stackArg s 2).toNat*8≤ofs (stackArg s 1) (s.gpr .x2+BitVec.ofNat 64 i)
 separateRand : ∀ i<(s.gpr .x6).toNat,∀ j<(s.gpr .x6).toNat,s.gpr .x7+BitVec.ofNat 64 i≠s.gpr .x0+BitVec.ofNat 64 j
 separateDomain : ∀ i<(attemptDomain s).length,(s.gpr .x6).toNat≤ofs (s.gpr .x0) (s.gpr .x4+BitVec.ofNat 64 i)
 separateContext : ∀ i<8*(stackArg s 4).toNat,(s.gpr .x6).toNat≤ofs (s.gpr .x0) (stackArg s 3+BitVec.ofNat 64 i)
 separateOutputs : ∀ i<(s.gpr .x6).toNat,(s.gpr .x6).toNat≤ofs (s.gpr .x2) (s.gpr .x0+BitVec.ofNat 64 i)

theorem attempt_geometry {s : State} (h : attemptPre s) : AttemptGeometry s :=by
 obtain ⟨spFits,rd,wr,dXY,dXD,dXR,dXS,dXC,dXA,dYD,dYR,dYS,dYC,dYA,dDS,dRS,dSC,dSA,
  wX,wY,wD,wR,wS,wC,⟨small,large⟩,shape,xLen,yLen,rLen,sLen,checked,canonical⟩:=h
 have scratch : Scr s (stackArg s 1) ((stackArg s 2).toNat*8) :=Scr.of_mem (by rw [wr];simp) wS
 have scrRoom : 128*(s.gpr .x6).toNat+256≤(stackArg s 2).toNat*8 :=by unfold Spec.Rsa.scratchWords at sLen;omega_using [sLen]
 have dlen : (attemptDomain s).length=(s.gpr .x5).toNat :=by simp only [attemptDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
 have readArgs (d : Nat) (fit : d+8≤40) : InRegions (s.rd++s.wr) (s.sp+BitVec.ofNat 64 d) 8 :=
  ⟨⟨s.sp,40⟩,by rw [rd];simp [stackArgAddr],Offset.contains_base _ fit (by omega_using [fit])⟩
 refine ⟨small,large,shape,rLen,?_,scratch,readArgs 8 (by decide),readArgs 24 (by decide),
  src_of_region (by rw [rd];simp) (by omega_using []) dDS,src_of_region (by rw [rd];simp) (by omega_using []) dRS,
  ⟨canonical,?_,?_⟩,checked,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · dsimp only [slot,hdrBytes];omega_using [small, scrRoom]
 · intro i hi
   exact ⟨⟨stackArg s 3,(stackArg s 4).toNat*8⟩,by rw [rd];simp,Offset.contains_base _ (by omega_using [hi]) (by omega_using [wC, hi])⟩
 · intro i hi
   exact out_scr dSC.symm (contains_byte _ (by omega_using [hi]) (by omega_using [wC]))
 · intro i hi
   exact ⟨⟨s.gpr .x0,(s.gpr .x1).toNat⟩,by rw [wr];simp,contains_byte _ (by omega_using [xLen, hi]) (by omega_using [])⟩
 · intro i hi
   exact ⟨⟨s.gpr .x2,(s.gpr .x3).toNat⟩,by rw [wr];simp,contains_byte _ (by omega_using [yLen, hi]) (by omega_using [])⟩
 · intro i hi
   exact out_scr dXS (contains_byte _ (by omega_using [xLen, hi]) (by omega_using []))
 · intro i hi
   exact out_scr dYS (contains_byte _ (by omega_using [yLen, hi]) (by omega_using []))
 · intro i hi j hj
   rw [xLen,rLen] at dXR
   rw [xLen] at wX
   rw [rLen] at wR
   exact VG.Proof.Ffdh.AArch64.GenerateKey.ne_of_disj dXR.symm wR wX hi hj
 · intro i hi
   rw [xLen] at dXD
   exact out_scr dXD.symm (contains_byte _ (by rw [dlen] at hi;exact hi) (by omega_using []))
 · intro i hi
   rw [xLen] at dXC
   exact out_scr dXC.symm (contains_byte _ (by omega_using [hi]) (by omega_using [wC]))
 · intro i hi
   rw [xLen,yLen] at dXY
   exact out_scr dXY (contains_byte _ (by omega_using [hi]) (by omega_using []))

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Every reviewed ABI input establishes the native attempt's complete geometry and public policy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

def attemptNativeParameters (s : State) (g : AttemptGeometry s) : Parameters :=
 checkedParameters (stackArg s 1) (s.gpr .x0) (stackArg s 3) ((stackArg s 2).toNat*8)
  (s.gpr .x6).toNat (attemptDomain s) g.room g.small g.large g.checked

def attemptFront (s : State) (g : AttemptGeometry s) : FrontPublic :=by
 let p:=attemptNativeParameters s g
 have positive : 0<p.k :=by change 0<(s.gpr .x6).toNat;have :=g.small;omega_using [this]
 have odd : p.P%2=1 :=by
  have mod:=VG.Proof.Ffdh.domainValid_mod g.checked
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at mod
  exact mod.1.1.1
 have bitsPositive : 0<p.N :=generation_bits_positive g.checked
 have bitsBound : p.N≤8192 :=generation_bits_bound positive g.large
 have width : p.N≤8*p.k :=Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.bits_le_bound _) (scalarBound_bits_fit positive)
 have valid : Spec.Ffdh.parametersValid (attemptParameters s)=true :=by
  have h:=g.checked
  unfold Spec.Ffdh.domainValid at h
  simp only [Bool.and_eq_true] at h
  exact h.1
 exact ⟨⟨⟨p,s.gpr .x4,(s.gpr .x5).toNat,attemptDomain s,rfl,positive,
   by change (s.gpr .x6).toNat<2^31;have :=g.large;omega_using [this],g.shape,
   by simp only [attemptDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range],rfl,odd⟩,
  s.gpr .x2,Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s),bitsPositive,bitsBound,width,rfl,valid,g.outsideX⟩,
  s.gpr .x7,(stackArg s 4).toNat,g.checked,rfl,rfl,g.separateRand,g.separateDomain,g.separateContext⟩

theorem attempt_native_state {s : State} (g : AttemptGeometry s) : NativeState (attemptFront s g) (attemptRandom s) s :=by
 refine ⟨g.scratch,g.view,g.domain,g.random,?_,rfl,rfl,rfl,?_,?_,rfl,?_,?_,g.stackB,g.stackCtx,g.writeX,rfl⟩
 · change (attemptRandom s).length=(s.gpr .x6).toNat
   simp only [attemptRandom,Spec.Rsa.bytesAt,List.length_map,List.length_range]
   exact g.randLength
 · exact (ofNat_toNat64 _).symm
 · exact (ofNat_toNat64 _).symm
 · rfl
 · rfl

end VG.Proof.Ffdh.AArch64.Cached
