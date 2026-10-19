module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullReject

/-! # Singleton fallback timing depends only on the shared matrix seed -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

def fullSuffix (w16 : Bool := false) : Prog isa := .seq (.block [.logic .and .x .x24 .x24 .x0])
  (.seq (Rej8.zeroSuffix w16) (.block [.ldr .x .x22 .x19 1848,.ldr .x .x23 .x19 1856]))

theorem fullSuffix_ct (w16 : Bool) : ConstantTime isa (fun _=>True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4,.x19])) (fullSuffix w16) := by
  cases w16 <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x3,.x4,.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fullFinish_entry_relCT {w16 : Bool} {s u : State} {B : Nat→Byte} {p out : Addr}
    (ps : Rej8.EntryW w16 [] 280 B (p+400) out s) (pu : Rej8.EntryW w16 [] 280 B (p+400) out u)
    (sp : s.sp=u.sp) (p19 : s.gpr .x19=u.gpr .x19) (t16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun t v=>t=s ∧ v=u) (fullFinish w16) (fun _ _=>True) := by
  let R := fun t v : State=>Rej8.PostW w16 [] 280 B out s t ∧ Rej8.PostW w16 [] 280 B out u v
  have parse : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Rej8.rejLoop w16) R :=
    Rej8.segment_relCT ps pu sp t16 (by decide) (by decide)
  refine RelCT.seq parse ?_
  intro t v tr ur t' v' h et ev
  have hsp := h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)
  have h3 : t.gpr .x3=v.gpr .x3 := h.1.acc.x3.trans h.2.acc.x3.symm
  have h4 : t.gpr .x4=v.gpr .x4 := BitVec.eq_of_toNat_eq (h.1.acc.x4.trans h.2.acc.x4.symm)
  have h19 : t.gpr .x19=v.gpr .x19 := by rw [h.1.keep.get .x19,h.2.keep.get .x19,p19]
  exact ⟨fullSuffix_ct w16 t v tr ur t' v' trivial trivial (agree_of hsp (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl; exact h3; exact h4; exact h19)) et ev,trivial⟩

theorem LastInput.full_wp {w16 : Bool} {s initial : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (h : LastInput sb ss off p seed out table s)
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256) (hp : s.gpr .x19=p) (sv : Noise.Saved p initial s.mem) :
    WP isa (fullSampleCode sb ss off a k w16) s (FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initial s) :=
  fullSampleCode_ok hss hsb h8 hoff hk hk256 hp h.ptr h.seedPtr h.outPtr h.readable
    h.context.scratch h.context.output h.separate h.context.apart sv
    (by rw [h.symbol]; exact h.context.artifact) (by rw [h.symbol]; exact h.context.readable)
    (by rw [h.symbol]; exact h.context.tableScratch) (by rw [h.symbol]; exact h.context.tableOut)

theorem fullSampleCode_relCT {w16 : Bool} {s u initialS initialU : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (s19 : s.gpr .x19=p) (u19 : u.gpr .x19=p)
    (svs : Noise.Saved p initialS s.mem) (svu : Noise.Saved p initialU u.mem)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (fullSampleCode sb ss off a k w16)
      (fun t v=>FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initialS s t ∧
        FullPostW w16 (xofByte (seedBytes u.mem seed a k)) p out initialU u v) := by
  let R := fun t v : State=>FullPrefixPostW w16 (xofByte (seedBytes s.mem seed a k)) p out s t ∧
    FullPrefixPostW w16 (xofByte (seedBytes u.mem seed a k)) p out u v ∧
    t.syms=s.syms ∧ v.syms=u.syms
  have prelude : RelCT isa (fun t v=>t=s ∧ v=u) (fullPrefix sb ss off a k) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨fullPrefix_ct hss s u tr ur t' v' trivial trivial (agree_of sp (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl; exact s19.trans u19.symm; exact base)) et ev,
      exec_post (fullPrefix_ok hss hsb h8 hoff hk hk256 ps s19 svs) et,
      exec_post (fullPrefix_ok hss hsb h8 hoff hk hk256 pu u19 svu) ev,Exec.syms et,Exec.syms ev⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u) (.seq (fullPrefix sb ss off a k) (fullFinish w16)) (fun _ _=>True) := by
    refine RelCT.seq prelude ?_
    intro t v tr ur t' v' h et ev
    have t16 : t.gpr .x16=v.gpr .x16 := by
      rw [h.1.tablePtr,h.2.1.tablePtr,ps.symbol,pu.symbol]
    exact fullFinish_entry_relCT h.1.entry (by rw [seedEq]; exact h.2.1.entry)
      (h.1.keep.sp.trans (sp.trans h.2.1.keep.sp.symm)) (h.1.pointer.trans h.2.1.pointer.symm)
      t16 t v tr ur t' v' ⟨rfl,rfl⟩ et ev
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (fullSampleCode sb ss off a k w16) (fun _ _=>True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (ps.full_wp hss hsb h8 hoff hk hk256 s19 svs) et,
    exec_post (pu.full_wp hss hsb h8 hoff hk hk256 u19 svu) ev⟩

end VG.Proof.MlKem.AArch64.Paired
