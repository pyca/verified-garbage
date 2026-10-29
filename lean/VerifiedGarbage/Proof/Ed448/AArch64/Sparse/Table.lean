module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TableSetup
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.OddLoop
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
/-! Complete bounded odd-key table construction, retaining R for the cofactor check. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/TableFields.lean`, which only this module imported.
section

/-! Initialize the odd table's first entry without changing the bounded representation. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Impl.Ed448.AArch64 (TAB tabStore)
open VG.Proof.X448.AArch64 (Scr Keeps Outside limbs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same copyE FKeep)
open VG.Proof.X448.AArch64.Base (pt zero_env limb_lt)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.Ed448.AArch64.Window (slotPt TPt TBnd tabStore_ok tabStore_pt tabStore_bnd limb_zero)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def tableFields : List Instr :=
  constSlot (slot 19) 0++constSlot (slot 20) 1++
  VG.Impl.Curve448.AArch64.copy (slot 3) (slot 6)++
  VG.Impl.Curve448.AArch64.copy (slot 4) (slot 7)++
  constSlot (slot 5) 1++[.movz .x .x19 0 0]++tabStore

structure FieldsOut (base:Addr) (s t:State) : Prop where
  scr : Scr t base
  env : BEnv t.mem base
  zero : ∀ w<8,limbs t.mem base (slot (19:Index).val) w=0
  zbound : Bnd Mb t.mem base (slot 5)
  counter : t.gpr .x19=0
  acc : pt (EV t.mem base) 3 4 5=slotPt s.mem base
  one : EV t.mem base 20=1
  tab : TPt t.mem base 0=slotPt s.mem base ∧ TBnd t.mem base 0
  xbound : Bnd Mb s.mem base (slot 6) → ∀ w<8,(Window.tw t.mem base 0 w).toNat<Mb
  keep : Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) s t
  mem : OddFrame base s.mem t.mem

theorem tableFields_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) :
    WP isa (.block tableFields) s (FieldsOut base s) := by
  simp only [tableFields,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constE hs hb 19 0) fun a ⟨ab,asm,ae,av,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE ha ab 20 1) fun b ⟨bb,bsm,be,bv,bo,bk⟩ => ?_
  have hb':=ha.of_keeps bk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyE hb' bb 3 6) fun c ⟨ck,cb,cv,csm,ce⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyE (ck.scr hb') cb 4 7) fun d ⟨dk,db,_,dsm,de⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE (dk.scr (ck.scr hb')) db 5 1) fun e ⟨eb,esm,ee,ev,eo,ek⟩ => ?_
  have he:Scr e base:=((dk.scr (ck.scr hb')).of_keeps ek (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok e 0 (by decide))
    fun f ⟨f19,fg,fm,fr,fw⟩ => ?_
  have fk:Keeps [.x19] e f:=⟨fun r hr => fg r (by simpa only [List.mem_singleton] using hr),fr,fw⟩
  have hf:=he.of_keeps fk (by decide)
  refine WP.mono (tabStore_ok hf (e:=0) (by decide) f19) fun t ⟨tv,fo,tk⟩ => ?_
  have envTF:EV t.mem base=EV f.mem base:=by
    funext i
    have hi:=i.isLt
    unfold VG.Proof.X448.AArch64.Weak.E VG.Proof.X448.AArch64.Weak.F
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun j hj =>
      fo.limbs (Or.inl (by simp only [slot,TAB];omega)) (by simp only [slot];omega) (by omega))
  have tB:BEnv t.mem base:=by
    intro i j hj
    have hi:=i.isLt
    rw [fo.limbs (Or.inl (by simp only [slot,TAB];omega)) (by simp only [slot];omega) (by omega),fm]
    exact eb i j hj
  have ez:∀ w<8,limbs e.mem base (slot (19:Index).val) w=0:=by
    intro w hw
    rw [esm 19 (by decide) w hw,dsm 19 (by decide) w hw,csm 19 (by decide) w hw,
      bsm 19 (by decide) w hw]
    change (VG.Proof.X448.AArch64.word a.mem base (slot (19:Index).val+8*w)).toNat=0
    rw [av w hw,limb_zero]
    rfl
  have ep:pt (EV e.mem base) 3 4 5=slotPt s.mem base:=by
    rw [ee,de,ce,be,ae]
    rfl
  have en:EV e.mem base 20=1:=by
    rw [ee,de,ce,be]
    rfl
  refine ⟨hf.of_keeps tk (by decide),tB,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    rw [fo.limbs (Or.inl (by simp only [slot,TAB];omega)) (by decide) (by omega),fm]
    exact ez w hw
  · intro w hw
    show (VG.Proof.X448.AArch64.word t.mem base (slot 5+8*w)).toNat<Mb
    rw [fo.word (Or.inl (by simp only [slot,TAB];omega)) (by simp only [slot];omega),fm]
    change (VG.Proof.X448.AArch64.word e.mem base (slot (5:Index).val+8*w)).toNat<Mb
    rw [ev w hw]
    exact Nat.lt_of_lt_of_le (limb_lt 1 w) (by decide)
  · exact (tk.1 _ (by decide)).trans f19
  · rw [envTF,fm]
    exact ep
  · rw [envTF,fm]
    exact en
  · refine ⟨?_,?_⟩
    · rw [tabStore_pt tv,fm]
      exact ep
    · exact tabStore_bnd (by rw [fm];exact eb) tv
  · intro hx w hw
    rw [Window.tw,tv w (by omega),fm]
    have heq:Window.src w=slot 3+8*w:=by simp only [Window.src,slot];omega
    rw [heq]
    change limbs e.mem base (slot (3:Index).val) w<Mb
    rw [esm 3 (by decide) w hw,dsm 3 (by decide) w hw,cv w hw,
      bsm 6 (by decide) w hw,asm 6 (by decide) w hw]
    exact hx w hw
  · have k1:Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) s b:=
      (ak.mono (by decide)).trans (bk.mono (by decide))
    have k2:Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) b d:=
      (ck.regs.mono (by decide)).trans (dk.regs.mono (by decide))
    have k3:Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) d f:=
      (ek.mono (by decide)).trans (fk.mono (by decide))
    exact ((k1.trans k2).trans k3).trans (tk.mono (by decide))
  · have fa:OddFrame base s.mem a.mem:=fun x hx _ _ => ao x (by simp only [slot] at hx ⊢;omega)
    have fb:OddFrame base a.mem b.mem:=fun x hx _ _ => bo x (by simp only [slot] at hx ⊢;omega)
    have fe:OddFrame base d.mem e.mem:=fun x hx _ _ => eo x (by simp only [slot] at hx ⊢;omega)
    rw [fm] at fo
    exact (((fa.trans fb).trans (OddFrame.of_outside2 ck.mem)).trans
      (OddFrame.of_outside2 dk.mem)).trans (fe.trans (OddFrame.of_entry (by decide) fo))

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64 (TAB RX RY CAN)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 limbs word ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same)
open VG.Proof.Ed448.AArch64.Window (slotPt TPt TBnd copyS_ok)
open VG.Proof.X448.AArch64.Base (pt zero_env)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The table build may write field slots, products, R's saves, and eight entries. -/
def TableFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ x,(ofs base x<64 ∨ 2880≤ofs base x) →
    (ofs base x<ACC ∨ ACC+1152≤ofs base x) →
    (ofs base x<RX ∨ RX+128≤ofs base x) →
    (ofs base x<RY ∨ TAB+1536≤ofs base x) → m' x=m x

theorem OddFrame.word {base:Addr} {m m':Mem} (h:OddFrame base m m') {d:Nat}
    (h1:d+8≤64 ∨ 2880≤d) (h2:d+8≤ACC ∨ ACC+1152≤d)
    (h3:d+8≤TAB ∨ TAB+1536≤d) (hd:d+8≤8192) : word m' base d=word m base d := by
  apply Mem.readW_congr
  intro i hi
  exact h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)];omega)

structure TableOut (s:State) (base:Addr) (t:State) : Prop where
  scr : Scr t base
  env : BEnv t.mem base
  zero : ∀ w<8,limbs t.mem base (slot (19:Index).val) w=0
  one : EV t.mem base 20=1
  tab : OddTabOk t.mem base (slotPt s.mem base) 8
  xbound : ∀ e<8,∀ w<8,(Window.tw t.mem base e w).toNat<Mb
  rx : ∀ w<8,limbs t.mem base RX w=limbs s.mem base (slot 8) w
  ry : ∀ w<8,limbs t.mem base RY w=limbs s.mem base (slot 9) w
  chk : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  mem : TableFrame base s.mem t.mem

theorem oddTable_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) (hx:Bnd Mb s.mem base (slot 6)) :
    WP isa oddTable s (TableOut s base) := by
  have hi:tableInit=VG.Impl.Curve448.AArch64.copy RX (slot 8)++
      (VG.Impl.Curve448.AArch64.copy RY (slot 9)++tableFields):=by
    simp only [tableInit,tableFields,List.append_assoc]
  unfold oddTable
  rw [WP.seq_iff,hi,WP.block_append_iff]
  refine WP.mono (copyS_ok hs (o:=RX) (a:=slot 8) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun a ⟨av,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok ha (o:=RY) (a:=slot 9) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun b ⟨bv,bo,bk⟩ => ?_
  have hb':=ha.of_keeps bk (by decide)
  have sb:∀ (i:Index),∀ j<8,limbs b.mem base (slot i.val) j=limbs s.mem base (slot i.val) j:=by
    intro i j hj
    have hi:=i.isLt
    rw [bo.limbs (Or.inl (by simp only [slot,RY,CAN];omega)) (by simp only [slot];omega) (by omega),
      ao.limbs (Or.inl (by simp only [slot,RX];omega)) (by simp only [slot];omega) (by omega)]
  have bb:BEnv b.mem base:=by
    intro i j hj
    rw [sb i j hj]
    exact hb i j hj
  have be:EV b.mem base=EV s.mem base:=by
    funext i
    exact Window.FV_of_limbs (sb i)
  refine WP.mono (tableFields_ok hb' bb) fun c hc => ?_
  have hcp:slotPt b.mem base=slotPt s.mem base:=by unfold slotPt;rw [be]
  refine WP.seq (WP.mono (Point56.doubleCall_ok hc.scr hc.env hc.zbound)
    fun d ⟨dk,db,dsm,_,_,_,de,_⟩ => ?_)
  have dz:∀ w<8,limbs d.mem base (slot (19:Index).val) w=0:=fun w hw => by
    rw [dsm 19 (by decide) w hw]
    exact hc.zero w hw
  have dp:pt (EV d.mem base) 3 4 5=VG.Proof.Ed448.double (slotPt s.mem base):=by
    rw [de,Window.dblEnv_345,hc.one,Window.dblPt_eq,hc.acc,hcp]
  have dt:TPt d.mem base 0=slotPt s.mem base ∧ TBnd d.mem base 0:=by
    have hw:∀ w<24,Window.tw d.mem base 0 w=Window.tw c.mem base 0 w:=fun w hw =>
      dk.mem.word (Or.inr (by simp only [TAB];omega)) (Or.inr (by simp only [ACC,TAB];omega))
        (by simp only [TAB];omega)
    refine ⟨?_,fun w hw' => ?_⟩
    · rw [Window.TPt_of_tw hw,hc.tab.1,hcp]
    · rw [hw w hw']
      exact hc.tab.2 w hw'
  have dx:∀ w<8,(Window.tw d.mem base 0 w).toNat<Mb:=by
    intro w hw
    have hm:Window.tw d.mem base 0 w=Window.tw c.mem base 0 w:=
      dk.mem.word (Or.inr (by simp only [TAB];omega)) (Or.inr (by simp only [ACC,TAB];omega))
        (by simp only [TAB];omega)
    rw [hm]
    exact hc.xbound (fun j hj => by
      change limbs b.mem base (slot (6:Index).val) j<Mb
      rw [sb 6 j hj]
      exact hx j hj) w hw
  refine WP.seq (WP.mono (tableStepSetup_ok (dk.scr hc.scr) db dz dp dt dx)
    fun e ⟨ei,eo,em,ek⟩ => ?_)
  refine WP.mono (oddLoop_ok 7 e (by decide) (by decide) ei) fun t ht => ?_
  have ce:OddFrame base c.mem e.mem:=(OddFrame.of_outside2 dk.mem).trans (OddFrame.of_outside2 em)
  have ct:OddFrame base c.mem t.mem:=ce.trans ht.mem
  refine ⟨ht.scr,ht.env,ht.zero,?_,ht.tab,ht.xbound,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.one,eo]
    rw [Same.env dsm (i:=20) (by decide)]
    exact hc.one
  · intro w hw
    show (word t.mem base (RX+8*w)).toNat=_
    rw [ct.word (Or.inr (by simp only [RX];omega)) (Or.inr (by simp only [ACC,RX];omega))
      (Or.inr (by simp only [TAB,RX];omega)) (by simp only [RX];omega),
      hc.mem.word (Or.inr (by simp only [RX];omega)) (Or.inr (by simp only [ACC,RX];omega))
      (Or.inr (by simp only [TAB,RX];omega)) (by simp only [RX];omega)]
    change limbs b.mem base RX w=_
    rw [bo.limbs (Or.inr (by simp only [RY,CAN,RX];omega)) (by simp only [RX];omega) (by omega)]
    exact av w hw
  · intro w hw
    show (word t.mem base (RY+8*w)).toNat=_
    rw [ct.word (Or.inr (by simp only [RY,CAN];omega)) (Or.inr (by simp only [ACC,RY,CAN];omega))
      (Or.inl (by simp only [TAB,RY,CAN];omega)) (by simp only [RY,CAN];omega),
      hc.mem.word (Or.inr (by simp only [RY,CAN];omega)) (Or.inr (by simp only [ACC,RY,CAN];omega))
      (Or.inl (by simp only [TAB,RY,CAN];omega)) (by simp only [RY,CAN];omega)]
    change limbs b.mem base RY w=_
    rw [bv w hw,ao.limbs (Or.inl (by simp only [slot,RX];omega)) (by decide) (by omega)]
  · rw [ht.chk,ek.1 _ (by decide),dk.regs.1 _ (by decide),hc.keep.1 _ (by decide),
      bk.1 _ (by decide),ak.1 _ (by decide)]
  · rw [ht.rd,ek.2.1,dk.regs.2.1,hc.keep.2.1,bk.2.1,ak.2.1]
  · rw [ht.wr,ek.2.2,dk.regs.2.2,hc.keep.2.2,bk.2.2,ak.2.2]
  · intro x hx hy hz hr
    rw [ct x hx hy (by simp only [TAB,RY,CAN] at hr ⊢;omega),
      hc.mem x hx hy (by simp only [TAB,RY,CAN] at hr ⊢;omega),
      bo x (by simp only [TAB,RY,CAN] at hr ⊢;omega),ao x hz]

end VG.Proof.Ed448.AArch64.Sparse
