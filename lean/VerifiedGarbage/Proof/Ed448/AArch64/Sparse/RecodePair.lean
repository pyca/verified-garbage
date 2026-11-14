module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointDigits
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.BufferFrame
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Recode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Step
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits

/-! ### `Ed448.AArch64.Sparse.Copy`, which only this module used -/

section

/-! Preserve signature digits while the challenge reuses the bit buffer. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs read1_eq write1_eq writeW8_apply
  writeW8_outside ofs_off' off_eq_iff)

private theorem byte_rt : ∀ b : BitVec 8,
    (b.setWidth 32 |>.setWidth 64 |>.setWidth 32 |>.setWidth 8)=b := by decide +kernel

private theorem copySetup_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block [.addImm .x .x10 .x3 3400,.addImm .x .x10 .x10 3400]) s fun u =>
      u.gpr .x10=off base SDIG ∧ Keeps [.x10] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceLT,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,hs.x3,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  · rw [Offset.add_add]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

private theorem copyOne_ok {s:State} {base:Addr} (hs:Scr s base)
    (hp:s.gpr .x10=off base SDIG) {i:Nat} (hi:i<464) :
    WP isa (.block [.ldrb .x4 .x3 (BITS+i),.strb .x4 .x10 i]) s fun u =>
      u.mem=s.mem.writeW (off base (SDIG+i)) (s.mem (off base (BITS+i))) ∧
      Keeps [.x4] s u := by
  have hr:=hs.read (d:=BITS+i) (n:=1) (by simp only [BITS];omega_using [hi])
  have hw:=hs.write (d:=SDIG+i) (n:=1) (by simp only [SDIG];omega_using [hi])
  have es:BITS+i<4096 := by simp only [BITS];omega_using [hi]
  have ei:i<4096 := by omega_using [hi]
  have ha:off base SDIG+BitVec.ofNat 64 i=off base (SDIG+i) := Offset.add_add _ _ _
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,addr,
    Nat.mod_one,es,ei,and_self,ite_true,hs.x3,hp,ha,State.load,State.store,hr,hw,
    read1_eq,write1_eq,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,
    Option.bind_some,Option.map_some,reduceCtorEq,ite_false,byte_rt,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r h => ?_,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at h
  simp only [RegUpd.gpr_write,h,ite_false]

private theorem copyLoop_ok {s:State} {base:Addr} (hs:Scr s base)
    (hp:s.gpr .x10=off base SDIG) {n:Nat} (hn:n≤464) :
    WP isa (.block ((List.range n).flatMap fun i =>
      [.ldrb .x4 .x3 (BITS+i),.strb .x4 .x10 i])) s fun u =>
      (∀ i<n,u.mem (off base (SDIG+i))=s.mem (off base (BITS+i))) ∧
      Outside base SDIG 464 s.mem u.mem ∧ Keeps [.x4] s u := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => by omega,Outside.refl _ _ _ _,Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun t ⟨ht,fo,kt⟩ => ?_
    refine WP.mono (copyOne_ok (hs.of_keeps kt (by decide))
      ((kt.1 _ (by decide)).trans hp) (by omega_using [hn])) fun u ⟨um,ku⟩ => ?_
    refine ⟨fun i hi => ?_,?_,kt.trans ku⟩
    · have hsrc:t.mem (off base (BITS+n))=s.mem (off base (BITS+n)) :=
        fo _ (Or.inl (by rw [ofs_off' base (by simp only [BITS];omega_using [hn])];simp only [BITS,SDIG];omega_using [hn]))
      rw [um,writeW8_apply]
      simp only [off_eq_iff base (d:=SDIG+i) (e:=SDIG+n)
        (by simp only [SDIG];omega_using [hn, hi]) (by simp only [SDIG];omega_using [hn])]
      by_cases he:i=n
      · subst i
        rw [ite_eq_left rfl,hsrc]
      · rw [ite_eq_right (by omega_using [he])]
        exact ht i (by omega_using [hi, he])
    · rw [um]
      refine fo.trans ?_
      intro x hx
      exact writeW8_outside _ base _ (by simp only [SDIG];omega_using [hn]) (by omega_using [hn, hx])

theorem copySignatureDigits_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block copySignatureDigits) s fun u =>
      (∀ i<464,u.mem (off base (SDIG+i))=s.mem (off base (BITS+i))) ∧
      Outside base SDIG 464 s.mem u.mem ∧ Keeps [.x4,.x10] s u := by
  unfold copySignatureDigits
  rw [WP.block_append_iff]
  refine WP.mono (copySetup_ok hs) fun t ⟨tp,kt,tm⟩ => ?_
  refine WP.mono (copyLoop_ok (hs.of_keeps kt (by decide)) tp (Nat.le_refl 464))
    fun u ⟨hd,fo,ku⟩ => ?_
  rw [tm] at hd fo
  exact ⟨hd,fo,(kt.mono (by decide)).trans (ku.mono (by decide))⟩

end VG.Proof.Ed448.AArch64.Sparse

end

end


/-! Recode both complete public scalars and run the shared sparse multiplier. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (KB bitsAt)
open VG.Impl.Ed448.WnafWide (digitAt scalarLimit)
open VG.Impl.X448.AArch64 (BITS ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Proof.X448.AArch64.Base (pt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- Recoding touches only the two public digit buffers. -/
structure PairOut (s:State) (base:Addr) (P:Spec.Ed448.Point) (S K:Nat) (t:State) : Prop where
  scr : Scr t base
  bnd : BEnv t.mem base
  tab : OddTabOk t.mem base P 8
  xb : ∀ e<8,∀ w<8,(Window.tw t.mem base e w).toNat<Mb
  bt : BaseTableAt t base (t.syms baseSym)
  sd : ∀ i<464,t.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i)
  kd : ∀ i<464,t.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)
  chk : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  mem : ∀ x,(ofs base x<BITS ∨ BITS+464≤ofs base x) →
    (ofs base x<SDIG ∨ SDIG+464≤ofs base x) → t.mem x=s.mem x

theorem recodePair_ok {s:State} {base:Addr} {P:Spec.Ed448.Point} {S K:Nat}
    (hs:Scr s base) (hb:BEnv s.mem base) (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb)
    (hbt:BaseTableAt s base (s.syms baseSym)) (hS:S<scalarLimit) (hK:K<scalarLimit)
    (hsd:∀ i<456,s.mem (off base (BITS+i))=BitVec.ofNat 8 (WnafWide.bit S i))
    (hkv:Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (off base KB) 57)=K) :
    WP isa recodePair s (PairOut s base P S K):=by
  unfold recodePair
  refine WP.seq (WP.mono_syms (recodeBits_ok true hs hS hsd) fun a ha asy => ?_)
  refine WP.seq (WP.mono_syms (copySignatureDigits_ok ha.scr) fun b ⟨bd,bo,bk⟩ bsy => ?_)
  have bs:Scr b base:=ha.scr.of_keeps bk (by decide)
  have bkbytes:Spec.Ed448.bytesAt b.mem (off base KB) 57=Spec.Ed448.bytesAt s.mem (off base KB) 57:=
    (buffer_bytes bo (Or.inl (by decide)) (by decide)).trans
      (buffer_bytes ha.mem (Or.inl (by decide)) (by decide))
  refine WP.seq (WP.mono_syms (VG.Proof.Ed448.AArch64.bitsAt_disjoint_ok bs bs.x3
    (src:=.x3) (so:=KB) (d1:=0) (d2:=BITS) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun q hq => bs.read (by simp only [KB];omega_using [hq]))
    (fun q hq => Or.inl (by
      rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [KB];omega_using [hq])]
      simp only [KB,BITS]
      omega_using [hq]))) fun c ⟨cg,cr,cw,co,cd⟩ csy => ?_)
  have ck:Keeps (.x8::VG.Proof.Ed448.AArch64.bitAtRegs) b c:=⟨cg,cr,cw⟩
  have cs:Scr c base:=bs.of_keeps ck (by decide)
  have cko:Outside base BITS 464 b.mem c.mem:=co.mono (by decide) (by decide)
  have cb:BEnv c.mem base:=buffer_bounds cko (by decide)
    (buffer_bounds bo (by decide) (buffer_bounds ha.mem (by decide) hb))
  have cbits:∀ i<456,c.mem (off base (BITS+i))=BitVec.ofNat 8 (WnafWide.bit K i):=by
    intro i hi
    have h:=cd i hi
    simp only [Nat.zero_add] at h
    rw [bkbytes,hkv] at h
    simpa only [WnafWide.bit,Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod] using h
  refine WP.mono_syms (recodeBits_ok false cs hK cbits) fun d hd dsy => ?_
  have db:BEnv d.mem base:=buffer_bounds hd.mem (by decide) cb
  have dt:OddTabOk d.mem base P 8:=
    buffer_table hd.mem (Or.inl (by decide))
      (buffer_table cko (Or.inl (by decide))
        (buffer_table bo (Or.inr (by decide)) (buffer_table ha.mem (Or.inl (by decide)) ht)))
  have dx:∀ e<8,∀ w<8,(Window.tw d.mem base e w).toNat<Mb:=
    buffer_xbounds hd.mem (Or.inl (by decide))
      (buffer_xbounds cko (Or.inl (by decide))
        (buffer_xbounds bo (Or.inr (by decide)) (buffer_xbounds ha.mem (Or.inl (by decide)) hxb)))
  have bt:BaseTableAt d base (d.syms baseSym):=by
    rw [dsy,csy,bsy,asy]
    exact buffer_baseTable hd.mem (by decide) (by rw [hd.keep.2.1,hd.keep.2.2])
      (buffer_baseTable cko (by decide) (by rw [cr,cw])
        (buffer_baseTable bo (by decide) (by rw [bk.2.1,bk.2.2])
          (buffer_baseTable ha.mem (by decide) (by rw [ha.keep.2.1,ha.keep.2.2]) hbt)))
  have ds:∀ i<464,d.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i):=by
    intro i hi
    rw [hd.mem _ (Or.inr (by
      rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [SDIG];omega_using [hi])]
      simp only [BITS,SDIG];omega_using [])),cko _ (Or.inr (by
      rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [SDIG];omega_using [hi])]
      simp only [BITS,SDIG];omega_using [])),bd i hi]
    exact ha.digits i hi
  refine ⟨hd.scr,db,dt,dx,bt,ds,hd.digits,?_,?_,?_,?_⟩
  · rw [hd.keep.1 _ (by decide),ck.1 _ (by decide),bk.1 _ (by decide),ha.keep.1 _ (by decide)]
  · rw [hd.keep.2.1,cr,bk.2.1,ha.keep.2.1]
  · rw [hd.keep.2.2,cw,bk.2.2,ha.keep.2.2]
  · intro x hbits hsig
    rw [hd.mem x hbits,cko x hbits,bo x hsig,ha.mem x hbits]

end VG.Proof.Ed448.AArch64.Sparse
