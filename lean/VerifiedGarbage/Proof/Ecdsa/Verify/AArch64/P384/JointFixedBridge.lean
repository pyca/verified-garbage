module

public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Mont.AArch64.Row
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Ecdsa.Verify.AArch64.P384.JointFixedEntry`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.JointRead9`, which this module and modules that import it used -/

section

/-! The generator's digit `j` of width nine as the joint loop reads it, from its two bytes alone,
for any number of digits (`jointFixedRead_ok` and `jointSignRead_ok` assume P-256's 257). -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Digit `j`'s low byte in `x2`, where it is in `x16`, and its high byte in `x3`. -/
theorem fixedRead9_ok {c : Joint.Cfg} (h9 : c.gw=9) {s : State} {base : Addr} {size u j : Nat}
    (hs : Scr s base size) (hB : c.gBits+1<4096) (hl : c.gBits+2*j+2≤size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (g : s.mem (off base (c.gBits+2*j))=FastNaf.wbyte u (2*j))
    (g1 : s.mem (off base (c.gBits+(2*j+1)))=FastNaf.wbyte u (2*j+1)) :
    WP isa (.block (Joint.fixedRead c)) s fun t =>
      t.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64 ∧ t.gpr .x16=off base (2*j) ∧
      t.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64 ∧ Keeps [.x2,.x3,.x16] s t := by
  rw [Joint.fixedRead,ite_eq_left h9,
    show ([.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x2 .x16 c.gBits,
      .ldrb .x3 .x16 (c.gBits+1)] : List Instr)=[.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,
      .ldrb .x2 .x16 c.gBits]++[.ldrb .x3 .x16 (c.gBits+1)] from rfl,WP.block_append_iff]
  refine WP.mono (nafRead2_ok hs (by omega_using [hB]) (by omega_using [hl]) h19 g .x2 (by decide)) fun a ⟨a2,a16,ka⟩ => ?_
  refine WP.mono (nafHiByte_ok (hs.of_keeps ka (by decide)) hB (by omega_using [hl]) a16 (by rw [ka.mem]; exact g1))
    fun t ⟨t3,kt⟩ => ⟨?_,?_,t3,(ka.mono (by simp)).trans (kt.mono (by simp))⟩
  · rw [kt.gpr _ (by decide),a2]
  · rw [kt.gpr _ (by decide),a16]

/-- Digit `j`'s sign, from its high byte. -/
theorem signRead9_ok {c : Joint.Cfg} (h9 : c.gw=9) {s : State} {base : Addr} {size u j : Nat}
    (hs : Scr s base size) (hB : c.gBits+1<4096) (hl : c.gBits+2*j+2≤size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (g : s.mem (off base (c.gBits+(2*j+1)))=FastNaf.wbyte u (2*j+1)) :
    WP isa (.block (Joint.signRead c)) s fun t =>
      t.gpr .x3=BitVec.ofNat 64 (FastNaf.negative 9 u j).toNat ∧ Keeps [.x3,.x16] s t := by
  rw [Joint.signRead,ite_eq_left h9,
    show ([.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19,.ldrb .x3 .x16 (c.gBits+1),
      .lsr .x .x3 .x3 7] : List Instr)=[.add .x .x16 .x0 .x19,.add .x .x16 .x16 .x19]++
      [.ldrb .x3 .x16 (c.gBits+1),.lsr .x .x3 .x3 7] from rfl,WP.block_append_iff]
  refine WP.mono (nafAdd2_ok hs h19) fun a ⟨a16,ka⟩ => ?_
  exact WP.mono (fixedSignByte_ok (u:=u) (hs.of_keeps ka (by decide)) hB (by omega_using [hl]) a16
    (by rw [ka.mem]; exact g)) fun t ⟨t3,kt⟩ => ⟨t3,(ka.mono (by simp)).trans (kt.mono (by simp))⟩

end VG.Proof.Weierstrass.AArch64

end

end

/-! ### `Ecdsa.Verify.AArch64.P384.JointFixedSource`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
/-- The odd entries `[2 a - 1]G` of `VG_P384_GTAB`, `a ≤ 128`, are read by the width-nine NAF. -/
structure FixedGenerator (C : Curve) (base : Addr) (size : Nat)
    (G : Point C) (T : Addr) (s : State) : Prop where
  symbol : s.syms "VG_P384_GTAB"=T
  read : ∀ a,1≤a → a≤128 → ∀ i<12,InRegions (s.rd++s.wr)
    (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)) 8
  outside : ∀ a,1≤a → a≤128 → ∀ i<12,∀ b<8,size≤ofs base
    (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)
  bounds : ∀ a,1≤a → a≤128 →
    wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6<C.p ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6<C.p
  point : ∀ a,1≤a → a≤128 →InvJ C
    (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) (wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6))
    (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) (wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6)) 1 (mul (2*a-1) G)

theorem FixedGenerator.keep {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {s t : State} {W : List Nat} (h : FixedGenerator C base size G T s)
    (hk : ProgKeep P384Joint.K.M base W s t) (hsym : t.syms=s.syms)
    (hw : ∀ w∈W,w+8*P384Joint.K.M.n≤size) (htmp : P384Joint.K.M.tmp+8*P384Joint.K.M.n≤size) :
    FixedGenerator C base size G T t := by
  have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤128) (hi : i<12) :
      word t.mem (T+BitVec.ofNat 64 (192*(a-1))) (8*i)=
      word s.mem (T+BitVec.ofNat 64 (192*(a-1))) (8*i) := by
    apply Mem.readW_congr
    intro b hb
    have ho := h.outside a ha ha32 i hi b (by omega_using [hb])
    apply hk.mem
    · intro w hm; have := hw w hm; dsimp only [off]; exact Or.inr (by omega_using [ho, this])
    · dsimp only [off]; exact Or.inr (by omega_using [htmp, ho])
  have val (a o : Nat) (ha : 1≤a) (ha32 : a≤128) (ho : o=0 ∨ o=48) :
      wordsVal t.mem (T+BitVec.ofNat 64 (192*(a-1))) o 6=
      wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) o 6 := by
    apply wordsVal_of_words₂
    intro i hi
    rcases ho with rfl | rfl
    · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega_using [hi])
    · have e := wordeq a (6+i) ha ha32 (by omega_using [hi])
      simpa only [Nat.mul_add] using e
  refine ⟨?_,?_,h.outside,?_,?_⟩
  · rw [hsym]; exact h.symbol
  · intro a ha ha32 i hi; rw [hk.rd,hk.wr]; exact h.read a ha ha32 i hi
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 48 ha ha32 (by simp)]
    exact h.bounds a ha ha32
  · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 48 ha ha32 (by simp)]
    exact h.point a ha ha32

theorem FixedGenerator.unch {C : Curve} {base T : Addr} {size : Nat}
 {G : Point C} {s t : State} {W : List (Nat×Nat)}
 (h : FixedGenerator C base size G T s)
 (hu : Unch base W s.mem t.mem) (hw : ∀w∈W,w.1+w.2≤size)
 (hr : t.rd=s.rd) (hwr : t.wr=s.wr) (hsy : t.syms=s.syms) :
 FixedGenerator C base size G T t := by
 have wordeq (a i : Nat) (ha : 1≤a) (ha32 : a≤128) (hi : i<12) :
   word t.mem (T+BitVec.ofNat 64 (192*(a-1))) (8*i)=
   word s.mem (T+BitVec.ofNat 64 (192*(a-1))) (8*i) := by
   apply Mem.readW_congr
   intro b hb
   apply hu
   intro w hm
   have ho := h.outside a ha ha32 i hi b (by omega_using [hb])
   have := hw w hm
   exact Or.inr (by dsimp only [off]; omega_using [ho, this])
 have val (a o : Nat) (ha : 1≤a) (ha32 : a≤128) (ho : o=0 ∨ o=48) :
   wordsVal t.mem (T+BitVec.ofNat 64 (192*(a-1))) o 6=
   wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) o 6 := by
   apply wordsVal_of_words₂
   intro i hi
   rcases ho with rfl | rfl
   · simpa only [Nat.zero_add] using wordeq a i ha ha32 (by omega_using [hi])
   · simpa only [Nat.mul_add] using wordeq a (6+i) ha ha32 (by omega_using [hi])
 refine ⟨hsy ▸ h.symbol,?_,h.outside,?_,?_⟩
 · intro a ha ha32 i hi; rw [hr,hwr]; exact h.read a ha ha32 i hi
 · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 48 ha ha32 (by simp)]
   exact h.bounds a ha ha32
 · intro a ha ha32; rw [val a 0 ha ha32 (by simp),val a 48 ha ha32 (by simp)]
   exact h.point a ha ha32

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.P384.JointFixedLoad`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
def fixedLoadBody : List Instr := P384Joint.fixedAddress ++ Joint.loadWords P384Joint.K.E.x 12 ++
 copy 6 P384Joint.K.E.z (p384.sl ONEP)
private theorem syms_write (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
 (s.write sz r x).syms=s.syms := rfl
theorem fixedAddress_ok {s : State} {a : Nat} {T : Addr}
 (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P384_GTAB"=T) :
 WP isa (.block P384Joint.fixedAddress) s fun t =>
 t.gpr .x16=T+BitVec.ofNat 64 (192*(a-1)) ∧ Keeps [.x2,.x3,.x16] s t := by
 apply WP.of_runBlock
 simp only [P384Joint.fixedAddress,show P384Joint.p384v.tsym="VG_P384_GTAB" from rfl,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
 RegUpd.gpr_write,syms_write,BitVec.setWidth_eq,Size.bits,h2,ht,
 show 1<4096 by decide,show 16*0<64 by decide,
 ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
 refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
 · simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
   change T + ((BitVec.ofNat 64 a - BitVec.ofNat 64 1) * BitVec.ofNat 64 192) = _
   rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) (by omega_using [ha]),←BitVec.ofNat_mul]
   congr 2
   omega_using []
 · intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
   simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]
/-- Loading x and y and copying the Montgomery one initializes an affine point. -/
theorem fixedLoadBody_ok {s : State} {base T : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a)
    (ht : s.syms "VG_P384_GTAB"=T) (hy : P384Joint.K.E.y=P384Joint.K.E.x+48)
    (hd : P384Joint.K.E.x+96≤size) (hd8 : P384Joint.K.E.x%8=0)
    (hz : P384Joint.K.E.z+48≤size) (hz8 : P384Joint.K.E.z%8=0)
    (hone : (p384.sl ONEP)+48≤size) (hone8 : (p384.sl ONEP)%8=0)
    (hsep : P384Joint.K.E.x+96≤P384Joint.K.E.z ∨ P384Joint.K.E.z+48≤P384Joint.K.E.x)
    (hsep1 : P384Joint.K.E.x+96≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.x)
    (hsepz : P384Joint.K.E.z≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.z)
    (hr : ∀ i<12, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<12, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b)) :
    WP isa (.block fixedLoadBody) s fun t =>
      wordsVal t.mem base P384Joint.K.E.x 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6 ∧
      wordsVal t.mem base P384Joint.K.E.y 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6 ∧
      wordsVal t.mem base P384Joint.K.E.z 6=wordsVal s.mem base (p384.sl ONEP) 6 ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x16] s t ∧
      Unch base [(P384Joint.K.E.x,96),(P384Joint.K.E.z,48)] s.mem t.mem := by
  rw [fixedLoadBody,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fixedAddress_ok ha h2 ht) fun b ⟨b16,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (jointLoadWords_ok (hs.of_keeps kb (by decide)) b16 hd hd8 (by decide)
    (by intro i hi; rw [kb.rd,kb.wr]; exact hr i hi) hout 12 (by decide)) fun d ⟨wd,kd,od⟩ => ?_
  refine WP.mono (copy_ok 6 ((hs.of_keeps kb (by decide)).of_keepRegs kd (by decide))
    hz hone hz8 hone8 hsepz) fun t ⟨zt,kt,ot⟩ => ?_
  have hn := hs.nowrap
  have wx : wordsVal d.mem base P384Joint.K.E.x 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    simpa only [Nat.zero_add,kb.mem] using wd i (by omega_using [hi])
  have wy : wordsVal d.mem base P384Joint.K.E.y 6=wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6 := by
    refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
    rw [hy]
    have e := wd (6+i) (by omega_using [hi])
    simpa only [Nat.mul_add,Nat.add_assoc,kb.mem] using e
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ot.wordsVal (by omega_using [hsep]) (by omega_using [hd, hn]),wx]
  · rw [ot.wordsVal (by omega_using [hy, hsep]) (by omega_using [hy, hd, hn]),wy]
  · rw [zt,od.wordsVal (by omega_using [hsep1]) (by omega_using [hone, hn]),kb.mem]
  · exact ((Keeps.regs kb).mono (by sub_regs)).trans
      ((kd.mono (by sub_regs)).trans (kt.mono (by sub_regs)))
  · intro x hx
    have hx0 := hx (P384Joint.K.E.x,96) (by simp)
    have hx1 := hx (P384Joint.K.E.z,48) (by simp)
    rw [ot x hx1,od x hx0,kb.mem]

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end


-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointFixedPoint.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
/-- The generator row is consumed directly as canonical Montgomery coordinates. -/
theorem fixedPoint_ok {s : State} {base T : Addr} {size a : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay P384Joint.K.M size Sl) (hAl : Aligned P384Joint.K.M Sl) (hn : P384Joint.K.M.n=6)
    (hi : Inv P384Joint.K.M base size C.p Sl V E s)
    (ha : 1≤a) (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ht : s.syms "VG_P384_GTAB"=T)
    (hy : P384Joint.K.E.y=P384Joint.K.E.x+48)
    (hD : ∀ x∈[P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z],Sl x)
    (hdz : P384Joint.K.E.x≠P384Joint.K.E.z) (hyz : P384Joint.K.E.y≠P384Joint.K.E.z)
    (hx1 : P384Joint.K.E.x≠(p384.sl ONEP)) (hy1 : P384Joint.K.E.y≠(p384.sl ONEP))
    (hOne : (p384.sl ONEP)∈V) (hOneVal : E (p384.sl ONEP)=1)
    (hr : ∀ i<12, InRegions (s.rd++s.wr)
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)) 8)
    (hout : ∀ i<12, ∀ b<8, size≤ofs base
      (T+BitVec.ofNat 64 (192*(a-1))+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hxy : wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6<C.p ∧
      wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6<C.p)
    {P : Point C} (hJ : InvJ C
      (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) (wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 0 6))
      (toM C.p (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64*6)) (wordsVal s.mem (T+BitVec.ofNat 64 (192*(a-1))) 48 6)) 1 P) :
    WP isa (.block fixedLoadBody) s fun t =>
      ProgKeep P384Joint.K.M base [P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z] s t ∧
      Inv P384Joint.K.M base size C.p Sl ([P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z]++V) (tmv C P384Joint.K.M.n base t) t ∧
      InvJ C (tmv C P384Joint.K.M.n base t P384Joint.K.E.x) (tmv C P384Joint.K.M.n base t P384Joint.K.E.y)
        (tmv C P384Joint.K.M.n base t P384Joint.K.E.z) P ∧ tmv C P384Joint.K.M.n base t P384Joint.K.E.z=1 := by
  have bx := hL.le _ (hD P384Joint.K.E.x (by simp))
  have by' := hL.le _ (hD P384Joint.K.E.y (by simp))
  have bz := hL.le _ (hD P384Joint.K.E.z (by simp))
  have b1 := hL.le _ (hi.sl _ hOne)
  have sxz := hL.apart _ _ (hD P384Joint.K.E.x (by simp)) (hD P384Joint.K.E.z (by simp)) hdz
  have syz := hL.apart _ _ (hD P384Joint.K.E.y (by simp)) (hD P384Joint.K.E.z (by simp)) hyz
  have sx1 := hL.apart _ _ (hD P384Joint.K.E.x (by simp)) (hi.sl _ hOne) hx1
  have sy1 := hL.apart _ _ (hD P384Joint.K.E.y (by simp)) (hi.sl _ hOne) hy1
  have sz1 : P384Joint.K.E.z≤(p384.sl ONEP) ∨ (p384.sl ONEP)+48≤P384Joint.K.E.z := by
    by_cases e : P384Joint.K.E.z=(p384.sl ONEP)
    · omega
    · have := hL.apart _ _ (hD P384Joint.K.E.z (by simp)) (hi.sl _ hOne) e
      rw [hn] at this; omega
  simp only [hn,hy] at bx by' bz b1 sxz syz sx1 sy1
  refine WP.mono (fixedLoadBody_ok hi.scr ha h2 ht hy (by omega)
    (hAl.sl _ (hD P384Joint.K.E.x (by simp))) bz (hAl.sl _ (hD P384Joint.K.E.z (by simp)))
    b1 (hAl.sl _ (hi.sl _ hOne)) (by omega) (by omega) sz1 hr hout)
    fun t ⟨vx,vy,vz,kt,ut⟩ => ?_
  have kp : ProgKeep P384Joint.K.M base [P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z] s t := by
    refine ⟨fun r hr => kt.gpr r (fun hh => hr ?_),kt.rd,kt.wr,kt.sp,fun x hx _ => ut x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [clob]
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      have hx0 := hx P384Joint.K.E.x (by simp)
      have hx1 := hx P384Joint.K.E.y (by simp)
      have hx2 := hx P384Joint.K.E.z (by simp)
      rw [hn] at hx0 hx1 hx2
      rw [hy] at hx1
      rcases hw with rfl | rfl <;> dsimp only <;> omega
  have hlt : ∀ x∈[P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z],wordsVal t.mem base x P384Joint.K.M.n<C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [hn]
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hxy.1
    · rw [vy]; exact hxy.2
    · rw [vz,←hn]; exact hi.lt _ hOne
  have zz : tmv C P384Joint.K.M.n base t P384Joint.K.E.z=1 := by
    unfold tmv
    rw [hn,vz,←hn,hi.val _ hOne,hOneVal]
  refine ⟨kp,hi.of_progKeep hL kp hD hlt,?_,zz⟩
  rw [zz]
  unfold tmv
  rw [hn,vx,vy]
  exact hJ

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf

theorem fixedLoad_eq : P384Joint.fixedLoad = Joint.fixedIndex P384Joint.cfg ++ fixedLoadBody := by
 simp only [P384Joint.fixedLoad,fixedLoadBody,List.append_assoc]

def fixedCoords : List Nat := [P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z]

theorem cfg_gw : P384Joint.cfg.gw=9 := rfl

/-- Digit `j`'s bytes, as the generator's digits hold them. -/
structure GBytes (base : Addr) (u j : Nat) (s : State) : Prop where
  lo : s.mem (off base (P384Joint.KG.bits+2*j))=FastNaf.wbyte u (2*j)
  hi : s.mem (off base (P384Joint.KG.bits+(2*j+1)))=FastNaf.wbyte u (2*j+1)

/-- The generator's digits miss what a lookup writes: its coordinates and the temporary. -/
theorem gbytes_apart : ∀ x∈fixedCoords,x+8*P384Joint.K.M.n≤P384Joint.KG.bits := by decide

theorem GBytes.keep {base : Addr} {u j : Nat} {s t : State} (h : GBytes base u j s) (hj : j<385)
    (hk : ProgKeep P384Joint.K.M base fixedCoords s t) : GBytes base u j t := by
  have ha := gbytes_apart
  have ht : P384Joint.K.M.tmp=4000 := rfl
  have hb : P384Joint.KG.bits=3152 := rfl
  have hn : P384Joint.K.M.n=6 := rfl
  have e : ∀ d, P384Joint.KG.bits≤d → d<P384Joint.KG.bits+770 → t.mem (off base d)=s.mem (off base d) := by
    intro d h0 h1
    apply hk.unch.byte (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · simp only [List.mem_map] at hw
        obtain ⟨x,hx,rfl⟩ := hw
        have := ha x hx
        right; dsimp only; omega_using [h0, this]
      · rw [List.mem_singleton.mp hw]; left; dsimp only; omega_using [ht, hb, h1])
      (by omega_using [hb, h1])
  exact ⟨by rw [e _ (by omega_using []) (by omega_using [hj])]; exact h.lo,by rw [e _ (by omega_using []) (by omega_using [hj])]; exact h.hi⟩

theorem fixedLookup_ok {s : State} {base T : Addr} {u j : Nat} {C : Curve} {G : Point C}
 {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P384Joint.K 8192)
 (hi : Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s)
 (hV : ∀ x∈[P384Joint.K.zero,p384.sl ONEP],x∈V)
 (hone : E (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (h19 : s.gpr .x19=BitVec.ofNat 64 j)
 (hbytes : GBytes base u j s)
 (h2 : s.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64)
 (h3 : s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64)
 (hm0 : FastNaf.magnitude 9 u j≠0) :
 WP isa (.block P384Joint.fixedLoad) s fun d =>
 ProgKeep P384Joint.K.M base fixedCoords s d ∧
 Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (fixedCoords++V) (tmv C P384Joint.K.M.n base d) d ∧
 InvJ C (tmv C P384Joint.K.M.n base d P384Joint.K.E.x)
   (tmv C P384Joint.K.M.n base d P384Joint.K.E.y) (tmv C P384Joint.K.M.n base d P384Joint.K.E.z)
   (mul (FastNaf.magnitude 9 u j) G) ∧
 tmv C P384Joint.K.M.n base d P384Joint.K.E.z=1 ∧
 d.gpr .x19=BitVec.ofNat 64 j ∧ GBytes base u j d := by
 let a := (FastNaf.magnitude 9 u j+1)/2
 have hmag := fastMagnitude_bound 9 u j
 have hodd := (FastNaf.magnitude_odd_or_zero 9 u j).resolve_left hm0
 have ha : 1≤a := by dsimp [a]; omega_using [hm0]
 have ha32 : a≤128 := by dsimp [a]; omega_using [hmag]
 have he : 2*a-1=FastNaf.magnitude 9 u j := by dsimp [a]; omega_using [hodd]
 have es : ∀x∈fixedCoords,x∈winSlots P384Joint.K := by decide
 rw [fixedLoad_eq,WP.block_append_iff]
 refine WP.mono_syms (jointFixedIndex_ok (c:=P384Joint.cfg) (Or.inr rfl)
   (by rw [jointGCell,ite_eq_left cfg_gw]; exact h2) (fun _ => h3)) fun b ⟨b2,kb⟩ sb => ?_
 rw [cfg_gw] at b2
 have ib := hi.of_keeps kb (by decide)
 have kp : ProgKeep P384Joint.K.M base [] s b := keeps_prog kb (by decide)
 have srcb := source.keep kp sb (by simp) hi.mod.tmp
 refine WP.mono (fixedPoint_ok hL.win.lay hL.al.al (by decide) ib ha b2 srcb.symbol
   (by decide) es (by decide) (by decide) (by decide) (by decide)
   (hV _ (by simp)) hone (srcb.read a ha ha32) (srcb.outside a ha ha32)
   (srcb.bounds a ha ha32) (srcb.point a ha ha32)) fun d ⟨kd,id,jd,zd⟩ => ?_
 have dj : d.gpr .x19=BitVec.ofNat 64 j := by rw [kd.gpr _ (x19_not_clob _),kb.gpr _ (by decide),h19]
 have kbd : ProgKeep P384Joint.K.M base fixedCoords s d := (kp.mono (by simp)).trans kd
 rw [he] at jd
 exact ⟨kbd,id,jd,zd,dj,hbytes.keep hj kbd⟩

theorem fixedEntry_ok {s : State} {base T : Addr} {u j : Nat} {C : Curve} {G : Point C}
 {V : List Nat} {E : Nat → Fe C}
 (hL : NafLay P384Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hi : Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s)
 (hV : ∀ x∈[P384Joint.K.zero,p384.sl ONEP],x∈V)
 (hzero : E P384Joint.K.zero=0) (hone : E (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (h19 : s.gpr .x19=BitVec.ofNat 64 j)
 (hbytes : GBytes base u j s)
 (h2 : s.gpr .x2=(FastNaf.wbyte u (2*j)).setWidth 64)
 (h3 : s.gpr .x3=(FastNaf.wbyte u (2*j+1)).setWidth 64)
 (hm0 : FastNaf.magnitude 9 u j≠0) :
 WP isa P384Joint.fixedEntry s fun t =>
 ∃ E', ProgKeep P384Joint.K.M base fixedCoords s t ∧
 Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) (fixedCoords++V) E' t ∧
 InvJ C (E' P384Joint.K.E.x) (E' P384Joint.K.E.y) (E' P384Joint.K.E.z)
   (FastNaf.point C G 9 u j) ∧ E' P384Joint.K.E.z=1 := by
 rw [P384Joint.fixedEntry]
 apply WP.seq
 refine WP.mono (fixedLookup_ok hL hi hV hone source hj h19 hbytes h2 h3 hm0) fun d ⟨kd,id,jd,zd,dj,db⟩ => ?_
 have vz : tmv C P384Joint.K.M.n base d P384Joint.K.zero=0 := by
   unfold tmv
   rw [kd.slot hL.win.lay hi.scr (by decide) (by decide) (by decide),hi.val _ (hV _ (by simp)),hzero]
 have vv : ∀x∈[P384Joint.K.E.x,P384Joint.K.E.y,P384Joint.K.E.z,P384Joint.K.zero],x∈fixedCoords++V := by
   intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl | rfl | rfl | rfl
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_left _ (by simp [fixedCoords])
   · exact List.mem_append_right _ (hV _ (by simp))
 refine WP.mono (jointSignEntryG_ok P384Joint.cfg (FastNaf.negative 9 u j) hL.win.lay hL.al.al (by simpa only [P384Joint.cfg] using hm) id vv
   (by decide) (by decide) vz
   (signRead9_ok cfg_gw id.scr (by decide) (by change 3152+2*j+2≤8192; omega_using [hj]) dj db.hi) jd zd)
   fun t ⟨Et,kt,it,jt,zt⟩ => ?_
 refine ⟨Et,kd.trans (kt.mono (by simp [fixedCoords,P384Joint.cfg])),it,?_,zt⟩
 simpa only [FastNaf.point,P384Joint.cfg] using jt
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.P384.JointLoop`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/Weierstrass/AArch64/PubNaf/JointDoubleD.lean`, which only this module imported.
section

/-! # The joint loop's shared doubling, by a given doubling

`jointDoubleD_ok`: `jointDouble_ok` with a doubling that does what the field program's does
(`DblSpec`, such as P-384's register-allocated doubling). -/

section
namespace VG.Proof.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

theorem jointDoubleD_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hC : Law C) (hM3 : AM3 C)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) {A : Point C} (hA : onCurve C A=true)
    {d : Prog isa} (hd : DblSpec K C base size d K.R K.D (dblVR K)) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : JointDigitPost K C base size P s₀ s (j + 1) A) :
    WP isa (.seq (.block [decCounter]) d) s fun t =>
      JointDoublePost K C base size P s₀ t j (Spec.Weierstrass.add A A) := by
  have hW := hL.win
  refine WP.seq (WP.mono (decCounter_ok s (by omega) (by have := hL.n6; omega) h.x19)
    fun s₁ ⟨x₁, k₁⟩ => ?_)
  have S₁ := h.st.regs hW k₁ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₁.mem]
  have V0 : ∀ x ∈ dblVR K, x ∈ winSlots K ∧ wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    all_goals exact ⟨winRo_slots K _ (by simp [winRo]), (S₁.ro hW hF).1 _ (by simp [winRo])⟩
  have I₁ : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) (tmv C K.M.n base s₁) s₁ :=
    inv_of S₁.scr S₁.mod (fun x hx => (V0 x hx).1) (fun x hx => (V0 x hx).2)
  have RJ₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y) (tmv C K.M.n base s₁ K.R.z)
      A := by rw [t₁, t₁, t₁]; exact h.r
  refine WP.mono (hd _ s₁ I₁) fun s₂ ⟨k₂, U₂, E₂, I₂, v₂⟩ => ?_
  have dJ := InvJ.dbl' hC hM3 hA RJ₁ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  have S₂ := S₁.next hW I₂.scr (k₂.mono fun _ h => List.mem_cons_of_mem _ (winSaved_combClob h)) U₂
  have x₂ : s₂.gpr .x19 = BitVec.ofNat 64 j := by
    have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
      (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
    rw [k₂.gpr _ n19, x₁, Nat.add_sub_cancel]
  have Dl : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p :=
    fun x hx => I₂.lt x (List.mem_append_left _ hx)
  have DJ : InvJ C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (Spec.Weierstrass.add A A) := by
    rw [show tmv C K.M.n base s₂ K.D.x = E₂ K.D.x from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.y = E₂ K.D.y from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.z = E₂ K.D.z from I₂.val _ (by simp)]
    exact dJ
  exact ⟨S₂, x₂, Dl, DJ, CacheOk.unch hW hL.cache (CacheUpTo.ofMem k₁.mem h.cache) U₂ S₁.scr.nowrap⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Fixed-generator arithmetic is independent of the joint loop's group recurrence. -/
def FixedStep (C : Curve) (base : Addr) (P G : Point C) (s₀ : State) (u : Nat) : Prop :=
 ∀(s : State) (j : Nat) (A : Point C),j<385 → onCurve C A=true →
  s.syms=s₀.syms → JointDigitPost P384Joint.K C base 8192 P s₀ s j A →
  WP isa P384Joint.fixedDigit s fun t=>
   JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j))

theorem digits_ok {C : Curve} {base : Addr} {P G A : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true)
 (hA : onCurve C A=true) (hF : NafFixed P384Joint.K C base s₀ P v)
 (fixed : FixedStep C base P G s₀ u) (hj : j<385) (sym : s.syms=s₀.syms)
 (h : JointDoublePost P384Joint.K C base 8192 P s₀ s j A) :
 WP isa P384Joint.digits s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 9 u j)) := by
 rw [P384Joint.digits]
 refine WP.seq (WP.mono_syms (jointDigit_ok hL hp hC hM3 hone hP hA h.st hF h.cache hj h.x19 h.dlt h.d)
  fun a ha sy=>?_) 
 exact fixed a j _ hj (hC.onCurve_add hA (Naf5.onCurve_point hC hP v j)) (sy.trans sym) ha

theorem step_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (hj : j<384) (sym : s.syms=s₀.syms)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s (j+1) (jointPoint G P u v (j+1) 9)) :
 WP isa P384Joint.step s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j (jointPoint G P u v j 9) := by
 rw [P384Joint.step]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (jointDoubleD_ok hL hC hM3 hF
  (jointPoint_curve hC hG hP u v (j+1) 9) hD (by change j<385; omega_using [hj]) h) fun a ha sy=>?_)
 refine WP.mono (digits_ok hL hp hC hM3 hone hP
  (hC.onCurve_add (jointPoint_curve hC hG hP u v (j+1) 9) (jointPoint_curve hC hG hP u v (j+1) 9))
  hF fixed (by omega_using [hj]) (sy.trans sym) ha) fun t ht=>?_
 rw [jointPoint_step hC hG hP u v j 9] at ht
 exact ht

/-- The public NAF's iteration with the allocated doubling also works on a joint accumulator. -/
theorem peerStepD_ok {C : Curve} {base : Addr} {P A : Point C} {s₀ s : State} {v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hA : onCurve C A=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (hj : j<384)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s (j+1) A) :
 WP isa (PubNaf.stepD P384Joint.K P384Joint.double) s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j (add (add A A) (Naf5.point C P v j)) := by
 rw [PubNaf.stepD]
 apply WP.assoc
 refine WP.seq (WP.mono (jointDoubleD_ok hL hC hM3 hF hA hD (by change j<385; omega_using [hj]) h) fun a ha=>?_)
 exact jointDigit_ok hL hp hC hM3 hone hP (hC.onCurve_add hA hA) ha.st hF ha.cache
  (by change j<385; omega_using [hj]) ha.x19 ha.dlt ha.d

theorem loop_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (sym : s.syms=s₀.syms)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s 384 (jointPoint G P u v 384 9)) :
 WP isa (.loop P384Joint.step (.nonzero .x .x19)) s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t 0 (add (mul u G) (mul v P)) ∧ t.syms=s₀.syms := by
 let I := fun j t=>JointDigitPost P384Joint.K C base 8192 P s₀ t j (jointPoint G P u v j 9) ∧ t.syms=s₀.syms
 apply countLoop_ok (Inv:=I) (n:=384) (by decide)
 · intro j a hj0 hjn hi
   have e : j-1+1=j := by omega_using [hj0]
   refine WP.mono_syms (step_ok (j:=j-1) hL hp hC hM3 hone hP hG hD hF fixed (by omega_using [hjn]) hi.2
    (by rw [e]; exact hi.1)) fun t ht sy=>?_
   exact ⟨⟨ht,sy.trans hi.2⟩,ht.x19⟩
 · intro t ht
   dsimp only [I] at ht
   rw [jointPoint_zero G P u v 9] at ht
   exact ht
 · decide
 · exact ⟨h,sym⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.P384.JointFixed`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)

theorem fixedDigit_using {s₀ s : State} {base T : Addr} {u v j : Nat} {C : Curve} {P G A : Point C}
 (hL : NafLay P384Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hC : Law C)
 (mixed : ∀ {s : State} {V : List Nat} {E : Nat → Fe C} {A B : Point C},
 Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s →
 (∀x∈rcbR P384Joint.K.S P384Joint.K.R P384Joint.K.E,x∈V) →
 onCurve C A=true → onCurve C B=true →
 InvJ C (E P384Joint.K.R.x) (E P384Joint.K.R.y) (E P384Joint.K.R.z) A →
 InvJ C (E P384Joint.K.E.x) (E P384Joint.K.E.y) (E P384Joint.K.E.z) B →
 E P384Joint.K.E.z=1 →
 WP isa (Jacobian.jacMixedAdd P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D) s
 (JacPost P384Joint.K.M P384Joint.K.S base 8192 C (·∈winSlots P384Joint.K) V P384Joint.K.D (add A B) s))
 (hG : onCurve C G=true) (hA : onCurve C A=true)
 (hf : NafFixed P384Joint.K C base s₀ P v)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s j A)
 (h1 : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (hbytes : GBytes base u j s) :
 WP isa P384Joint.fixedDigit s fun t =>
 JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j)) := by
 let K := P384Joint.K
 let V := winRo K ++ [K.R.x,K.R.y,K.R.z]
 have vs : ∀x∈V,x∈winSlots K := by decide
 have vl : ∀x∈V,wordsVal s.mem base x K.M.n<C.p := by
   intro x hx
   rcases List.mem_append.mp hx with hx | hx
   · exact (h.st.ro hL.win hf).1 x hx
   · exact h.rlt x hx
 have hi := h.st.inv vs vl
 rw [P384Joint.fixedDigit]
 apply WP.seq
 refine WP.mono_syms (fixedRead9_ok (c:=P384Joint.cfg) cfg_gw h.st.scr (by decide)
   (by change 3152+2*j+2≤8192; omega_using [hj]) h.x19 hbytes.lo hbytes.hi) fun a ⟨a2,_,a3,ka⟩ sa => ?_
 have ia := (hi.of_keeps ka (by decide)).to_tmv
 have kpa : ProgKeep K.M base [] s a := keeps_prog ka (by decide)
 have srca := source.keep kpa sa (by simp) hi.mod.tmp
 have na := h.st.regs hL.win ka (by decide) (by decide)
 have ca := CacheUpTo.ofMem ka.mem h.cache
 have a19 := (ka.gpr .x19 (by decide)).trans h.x19
 have ab : GBytes base u j a := ⟨by rw [ka.mem]; exact hbytes.lo,by rw [ka.mem]; exact hbytes.hi⟩
 have a1 : tmv C K.M.n base a (p384.sl ONEP)=1 := by unfold tmv; rw [ka.mem]; exact h1
 have az : tmv C K.M.n base a K.zero=0 := by
   unfold tmv
   rw [(na.ro hL.win hf).2,toM_zero]
 refine WP.ite (decide (FastNaf.magnitude 9 u j≠0)) (by
   change some (a.read .x .x2 != 0)=_
   rw [read_x,a2]
   congr 1
   have hz := jointGCell_zero_iff (c:=P384Joint.cfg) (Or.inr rfl) u j
   rw [jointGCell,ite_eq_left cfg_gw,cfg_gw] at hz
   by_cases h0 : FastNaf.magnitude 9 u j=0
   · rw [hz.mpr h0,h0]; rfl
   · rw [bne_iff_ne.mpr (fun he => h0 (hz.mp he)),decide_eq_true h0]) (fun hn=>?_) (fun hz=>?_)
 · apply WP.seq
   refine WP.mono (fixedEntry_ok hL hm ia (by decide) az a1 srca hj a19 ab a2 a3 (of_decide_eq_true hn))
     fun b ⟨E,kb,ib,jb,zb⟩=>?_
   have rEq : ∀x∈[K.R.x,K.R.y,K.R.z],E x=tmv C K.M.n base a x := by
     intro x hx
     rw [←ib.val x (by apply List.mem_append_right; exact List.mem_append_right _ hx)]
     unfold tmv
     rw [kb.slot hL.win.lay ia.scr (by decide) (vs x (List.mem_append_right _ hx)) (by
       revert x; decide)]
   have ja : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) A := by
     rw [rEq _ (by simp),rEq _ (by simp),rEq _ (by simp)]
     simpa only [tmv,ka.mem] using h.r
   apply WP.seq
   refine WP.mono (mixed ib (by decide) hA (FastNaf.onCurve_point hC hG 9 u j) ja jb zb)
       fun d ⟨Ed,kd,id,jd⟩=>?_
   have copyApart : RcbApart K.S K.D K.D K.R := by
     obtain ⟨_,a2,_,_,_,_,_,_⟩ := rcbApart_naf hL.win
     exact ⟨a2.nodup,fun x hx=>a2.apart x (rcbR_self_mem _ _ _ hx)⟩
   change WP isa (.block (copyPt K.M.n K.R K.D)) d _
   refine WP.mono (copyPointJ_ok hL.win.lay hL.al.al copyApart (by decide) id (by decide) jd)
     fun t ⟨Et,kt,it,jt⟩=>?_
   have kbt : ProgKeep K.M base (winOther K) a t :=
     (kb.mono (by decide)).trans ((kd.mono (by decide)).trans (kt.mono (by decide)))
   have ut : Unch base (loopW K) a.mem t.mem := kbt.unch
   have nt := na.next hL.win it.scr ((⟨kbt.gpr,kbt.rd,kbt.wr,kbt.sp⟩ : KeepRegs (clob K.M.n) a t).mono clob_nafClob) ut
   exact ⟨nt,(kbt.gpr _ (x19_not_clob _)).trans a19,
     fun x hx=>it.lt x (List.mem_append_left _ hx),
     it.point_tmv (fun x hx=>List.mem_append_left _ hx) jt,
     CacheOk.unch hL.win hL.cache ca ut h.st.scr.nowrap⟩
 · have hm0 : FastNaf.magnitude 9 u j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
   have pt : FastNaf.point C G 9 u j=.infinity := by
     rw [FastNaf.point,hm0]
     have h0 : mul 0 G=.infinity := by rw [Spec.Weierstrass.mul]; rfl
     rw [h0]; split <;> rfl
   apply WP.block_nil
   rw [pt,add_infinity]
   exact ⟨na,a19,(by rw [ka.mem]; exact h.rlt),(by simpa only [tmv,ka.mem] using h.r),ca⟩
theorem fixedDigit_ok {s₀ s : State} {base T : Addr} {u v j : Nat} {C : Curve} {P G A : Point C}
 (hL : NafLay P384Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hC : Law C) (hA3 : AM3 C) (hone : P384Joint.K.one<C.p)
 (hG : onCurve C G=true) (hA : onCurve C A=true)
 (hf : NafFixed P384Joint.K C base s₀ P v)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s j A)
 (h1 : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (hbytes : GBytes base u j s) :
 WP isa P384Joint.fixedDigit s fun t =>
 JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j)) := by
 apply fixedDigit_using hL hm hC _ hG hA hf h h1 source hj hbytes
 intro t V E A B it iv a b ja jb z
 obtain ⟨_,_,_,_,_,apart,_,_⟩ := rcbApart_naf hL.win
 exact jacMixedAddB_ok hL.win.lay hL.al.al (by decide) hm hC hA3 apart
   (by decide) (hL.al.low (by decide)) it iv hone a b ja jb z

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end


-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointWindow.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass
theorem window_ok {C : Curve} {base : Addr} {u v : Nat} (hL : NafLay P384Joint.K 8192)
    (hp : UnitMod C.p (2 ^ (64 * P384Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C) (hpn : C.p < 2 ^ (64 * P384Joint.K.M.n))
    (hone_lt : P384Joint.K.one < C.p) (hone : toM C.p (2 ^ (64 * P384Joint.K.M.n)) P384Joint.K.one = 1) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P G : Point C} (hP : onCurve C P = true) (hG : onCurve C G=true) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA P384Joint.K.M 8192 C.p s.mem base) (hF : NafFixed P384Joint.K C base s P v)
    (hz1 : tmv C P384Joint.K.M.n base s P384Joint.K.P.z = 1) (hv : v < 2 ^ (64 * P384Joint.K.M.n)) (hu : u < 2^(64*P384Joint.K.M.n))
    (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
    (fixed : ∀t, Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem t.mem → t.rd=s.rd → t.wr=s.wr → t.syms=s.syms → FixedStep C base P G t u) :
    WP isa P384Joint.window s fun t => Scr t base 8192 ∧ KeepRegs (nafClob P384Joint.K.M.n) s t ∧
      Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem t.mem ∧ ModOkA P384Joint.K.M 8192 C.p t.mem base ∧
      (∀ x ∈ [P384Joint.K.R.x, P384Joint.K.R.y, P384Joint.K.R.z], wordsVal t.mem base x P384Joint.K.M.n < C.p) ∧
      Rep C (tmv C P384Joint.K.M.n base t P384Joint.K.R.x) (tmv C P384Joint.K.M.n base t P384Joint.K.R.y) (tmv C P384Joint.K.M.n base t P384Joint.K.R.z)
        (add (mul u G) (mul v P)) := by
  have hn := hs.nowrap
  rw [P384Joint.window]
  refine WP.seq (WP.mono_syms (table_ok hL hp hC hM3 hO hn17 hP hs hM hF hz1) fun s₁ S₁ sy₁ => ?_)
  -- The cache, from which the loop goes on.
  refine WP.seq (WP.mono_syms (cacheTo_ok hL hp S₁.scr S₁.mod S₁.tbl 8 (Nat.le_refl _))
    fun s₂ ⟨sc₂, k₂, U₂, M₂, T₂, C₂⟩ sy₂ => ?_)
  have U₀₂ : Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem s₂.mem := (S₁.unch.trans U₂).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · exact Or.inl (loopW_sub P384Joint.K w hw)
  have F₂ := hF.rebase hL U₀₂ hn
  have S₂ : NSt P384Joint.K C base 8192 P s₂ s₂ := ⟨sc₂, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, M₂, T₂⟩
  have fixed₂ := fixed s₂ U₀₂ (k₂.rd.trans S₁.keep.rd) (k₂.wr.trans S₁.keep.wr) (sy₂.trans sy₁)
  apply WP.seq
  refine WP.mono_syms (head_ok hL hone_lt F₂ S₂ C₂ hv) fun s₃ ⟨S₃,C₃,x₃,Dl₃,DJ₃⟩ sy₃ => ?_
  have top := jointPoint_topB (B:=64*P384Joint.K.M.n) (u:=u) (v:=v) G P hu hv 9
  change jointPoint G P u v 385 9 = .infinity at top
  have dj : InvJ C (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.x)
    (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.y) (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.z)
    (add (jointPoint G P u v 385 9) (jointPoint G P u v 385 9)) := by
    rw [top]
    have hz := Naf5.residual_zero_top hv
    change Naf5.residual v 385=0 at hz
    change InvJ C _ _ _ (mul (2*Naf5.residual v 385) P) at DJ₃
    rw [hz,Nat.mul_zero,Spec.Weierstrass.mul] at DJ₃
    exact DJ₃
  apply WP.seq
  refine WP.mono_syms (digits_ok hL hp hC hM3 hone_lt hP
    (hC.onCurve_add (jointPoint_curve hC hG hP u v 385 9) (jointPoint_curve hC hG hP u v 385 9))
    F₂ fixed₂ (j:=384) (by decide) sy₃ ⟨S₃,x₃,Dl₃,dj,C₃⟩) fun s₄ I₄ sy₄ => ?_
  rw [jointPoint_step hC hG hP u v 384 9] at I₄
  apply WP.seq
  refine WP.mono (loop_ok hL hp hC hM3 hone_lt hP hG hD F₂ fixed₂ (sy₄.trans sy₃) I₄) fun s₅ ⟨I₅,_⟩=>?_
  refine WP.mono (jointFinish_ok hL hp hC hpn hone_lt hone F₂ I₅.st I₅.rlt I₅.r) fun t ⟨S',l',r'⟩=>?_
  refine ⟨S'.scr,S₁.keep.trans (k₂.trans S'.keep),(U₀₂.trans S'.unch).mono fun w hw=>?_,S'.mod,l',r'⟩
  simp only [List.mem_append] at hw ⊢
  rcases hw with hw | hw
  · exact hw
  · exact Or.inl hw
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- The generator's digits miss the window method's slots and the cache. -/
theorem generator_apart : ∀w∈winW P384Joint.K ++ PubNaf.cacheW P384Joint.K,
 P384Joint.KG.bits+770≤w.1 ∨ w.1+w.2≤P384Joint.KG.bits := by decide

theorem GBytes.of_unch {base : Addr} {u j : Nat} {s t : State} {W : List (Nat×Nat)}
 (hu : Unch base W s.mem t.mem)
 (hw : ∀w∈W,P384Joint.KG.bits+770≤w.1 ∨ w.1+w.2≤P384Joint.KG.bits)
 (bytes : ∀i<770,s.mem (off base (P384Joint.KG.bits+i))=FastNaf.wbyte u i) (hj : j<385) :
 GBytes base u j t := by
 have hb : P384Joint.KG.bits=3152 := rfl
 have e : ∀i<770,t.mem (off base (P384Joint.KG.bits+i))=FastNaf.wbyte u i := fun i hi => by
  rw [hu.byte (fun w hw' => by have := hw w hw'; omega_using [hi, this]) (by omega_using [hb, hi])]
  exact bytes i hi
 exact ⟨e _ (by omega_using [hj]),e _ (by omega_using [hj])⟩

theorem fixedStep_of_source {C : Curve} {base T : Addr} {P G : Point C} {s₀ : State} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hC : Law C) (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hG : onCurve C G=true)
 (hF : NafFixed P384Joint.K C base s₀ P v)
 (source : FixedGenerator C base 8192 G T s₀)
 (bytes : ∀j<770,s₀.mem (off base (P384Joint.KG.bits+j))=FastNaf.wbyte u j)
 (one : tmv C P384Joint.K.M.n base s₀ (p384.sl ONEP)=1) :
 FixedStep C base P G s₀ u := by
 intro s j A hj hA sy h
 have src := source.unch h.st.unch (by decide) h.st.keep.rd h.st.keep.wr sy
 have gb : GBytes base u j s :=
  GBytes.of_unch h.st.unch (fun w hw => generator_apart w (List.mem_append_left _ hw)) bytes hj
 have ho : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1 := by
  unfold tmv
  rw [h.st.unch.wordsVal (by decide) (by decide)]
  exact one
 exact fixedDigit_ok hL hp hC hM3 hone hG hA hF h ho src hj gb

/-- The concrete fixed generator discharges the loop's arithmetic callback. -/
theorem window_source_ok {C : Curve} {base T : Addr} {u v : Nat} (hL : NafLay P384Joint.K 8192)
 (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C)
 (hpn : C.p<2^(64*P384Joint.K.M.n)) (hone : P384Joint.K.one<C.p)
 (h1 : toM C.p (2^(64*P384Joint.K.M.n)) P384Joint.K.one=1) (hO : PrimeOrder C) (hn : 17≤C.n)
 {P G : Point C} (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K)) {s : State}
 (hs : Scr s base 8192) (hm : ModOkA P384Joint.K.M 8192 C.p s.mem base)
 (hf : NafFixed P384Joint.K C base s P v) (hz : tmv C P384Joint.K.M.n base s P384Joint.K.P.z=1)
 (hv : v<2^(64*P384Joint.K.M.n)) (hu : u<2^(64*P384Joint.K.M.n))
 (source : FixedGenerator C base 8192 G T s)
 (bytes : ∀j<770,s.mem (off base (P384Joint.KG.bits+j))=FastNaf.wbyte u j) :
 WP isa P384Joint.window s fun t=>Scr t base 8192 ∧ KeepRegs (nafClob P384Joint.K.M.n) s t ∧
  Unch base (winW P384Joint.K++cacheW P384Joint.K) s.mem t.mem ∧ ModOkA P384Joint.K.M 8192 C.p t.mem base ∧
  (∀x∈[P384Joint.K.R.x,P384Joint.K.R.y,P384Joint.K.R.z],wordsVal t.mem base x P384Joint.K.M.n<C.p) ∧
  Rep C (tmv C P384Joint.K.M.n base t P384Joint.K.R.x) (tmv C P384Joint.K.M.n base t P384Joint.K.R.y)
   (tmv C P384Joint.K.M.n base t P384Joint.K.R.z) (add (mul u G) (mul v P)) := by
 refine window_ok hL hp hC hM3 hpn hone h1 hO hn hP hG hs hm hf hz hv hu hD ?_
 intro a ua rd wr sy
 have ha := hf.rebase hL ua hs.nowrap
 have src := source.unch ua (by decide) rd wr sy
 apply fixedStep_of_source hL hp hC hM3 hone hG ha src
 · intro j hj
   have hb : P384Joint.KG.bits=3152 := rfl
   rw [ua.byte (by
     intro w hw
     have he := generator_apart w hw
     omega_using [hj, he]) (by omega_using [hj, hb])]
   exact bytes j hj
 · unfold tmv
   rw [ua.wordsVal (by decide) (by decide)]
   exact hz
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
