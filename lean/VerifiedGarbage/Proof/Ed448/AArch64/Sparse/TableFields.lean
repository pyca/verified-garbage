module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.OddLoop
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.Framework.Block

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
