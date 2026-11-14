module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeCallSetup
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryEnv
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Mem

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def normalizePrefixStep (z out prev : Nat) : Prog isa :=
  .seq (.block (normalizeCopy 9 z 1360)) (normalizeMulStep out prev 1360)

def NormalizePrefixFrame (base : Addr) (out : Nat) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1360 ∨ 1432≤ofs base x) → (ofs base x<out ∨ out+72≤ofs base x) →
    (ofs base x<3952 ∨ 4016≤ofs base x) → m' x=m x

theorem normalize_prefix_step_ok {base table : Addr} {W z out prev : Nat} {s : State}
    (layout : NormalizeLayout base table W) (hs : Scr s base W) (pt : Ptr s .x26 table 3456)
    (hz : z+72≤3456) (hz8 : z%8=0) (hout : out+72≤W) (hprev : prev+72≤W)
    (apartPrev : prev+72≤1360 ∨ 1432≤prev) (scratchPrev : prev+72≤3952 ∨ 4016≤prev)
    (boundPrev : wordsVal s.mem base prev 9<fieldPrime) (boundZ : wordsVal s.mem table z 9<fieldPrime) :
    WP isa (normalizePrefixStep z out prev) s fun t =>
      wordsVal t.mem base out 9<fieldPrime ∧
      wordsVal t.mem base out 9=wordsVal s.mem base prev 9*wordsVal s.mem table z 9%fieldPrime ∧
      NormalizePrefixFrame base out s.mem t.mem ∧ t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.v .v31=s.v .v31 := by
  rw [normalizePrefixStep,WP.seq_iff]
  have copy := normalize_copy_ok layout.tableApart 9 hs pt hz
    (by have h:=layout.workspaceSize; omega_arith) hz8 (by decide : 1360%8=0)
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by
    simp only [normalizeCopy,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,vdstOf,and_self]) copy)
    fun u ⟨⟨value,ku,ou⟩,vu⟩ => ?_
  have prevSame : wordsVal u.mem base prev 9=wordsVal s.mem base prev 9 :=
    ou.wordsVal apartPrev (by have h:=hs.enc; omega_arith)
  have hu := hs.of_keepRegs ku (by decide)
  refine WP.mono (normalize_mul_step_ok hu (by have h:=layout.workspaceSize; omega_arith)
    hout hprev (by have h:=layout.workspaceSize; omega_arith) scratchPrev
    (by rw [prevSame]; exact boundPrev) (by rw [value]; exact boundZ))
    fun t ⟨bound,prod,frame,zero,rd,wr,sp,gp,v31⟩ => ?_
  rw [prevSame,value] at prod
  refine ⟨bound,prod,?_,zero,rd.trans ku.rd,wr.trans ku.wr,sp.trans ku.sp,?_,?_⟩
  · intro x hcopy hout htmp
    rw [frame x hout htmp,ou x hcopy]
  · intro r hr
    exact (gp r hr).trans (ku.gpr r ((by decide : ∀r∈preserved,r∉[Reg.x1]) r hr))
  · rw [v31,vu]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Mont.AArch64.P521Field (ordinary_mul)
open VG.Proof.Weierstrass (ofNat_eq_ofNat ofNat_mod)

theorem normalize_prefix_slot_fits : ∀m,1≤m → m≤16 → normalizePrefixSlot m+72≤7336 := by
  intro m hm hn
  unfold normalizePrefixSlot
  split <;> rename_i h1
  · omega_arith
  · split <;> omega_arith

theorem normalize_prefix_slot_copy_apart : ∀m,1≤m → m≤16 →
    normalizePrefixSlot m+72≤1360 ∨ 1432≤normalizePrefixSlot m := by
  intro m hm hn
  unfold normalizePrefixSlot
  split <;> rename_i h1
  · omega_arith
  · split <;> omega_arith

theorem normalize_prefix_slot_scratch_apart : ∀m,1≤m → m≤16 →
    normalizePrefixSlot m+72≤3952 ∨ 4016≤normalizePrefixSlot m := by
  intro m hm hn
  unfold normalizePrefixSlot
  split <;> rename_i h1
  · omega_arith
  · split <;> omega_arith

theorem normalize_prefix_slots_apart : ∀m<16,∀k≤m,1≤k →
    normalizePrefixSlot k+72≤normalizePrefixSlot (m+1) ∨
      normalizePrefixSlot (m+1)+72≤normalizePrefixSlot k := by decide

theorem NormalizePrefixFrame.wordsVal {base : Addr} {out : Nat} {m m' : Mem}
    (frame : NormalizePrefixFrame base out m m') :
    ∀n d,(d+8*n≤1360 ∨ 1432≤d) → (d+8*n≤out ∨ out+72≤d) →
      (d+8*n≤3952 ∨ 4016≤d) → d+8*n≤2^64 → wordsVal m' base d n=wordsVal m base d n
  | 0,_,_,_,_,_ => rfl
  | n+1,d,hcopy,hout,htmp,hfit => by
    have wordEq : word m' base d=word m base d := by
      apply Mem.readW_congr
      intro i hi
      apply frame
      all_goals rw [ofs_off base (by omega_arith)]; omega_arith
    simp only [VG.Proof.Mont.wordsVal]
    rw [wordEq,frame.wordsVal n (d+8) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]

theorem NormalizePrefixFrame.workspace {base : Addr} {out W : Nat} {m m' : Mem}
    (frame : NormalizePrefixFrame base out m m') (hout : out+72≤W) (hW : 4016≤W) :
    Outside base 0 W m m' := by
  intro x hx
  apply frame <;> omega_arith

theorem NormalizePrefixFrame.region {base : Addr} {out : Nat} {m m' : Mem}
    (frame : NormalizePrefixFrame base out m m') (lo : 1216≤out) (hi : out+72≤7336) :
    Outside base 1216 6120 m m' := by
  intro x hx
  apply frame <;> omega_arith

theorem normalize_prefix_slot_floor : ∀m,2≤m → m≤16 → 1216≤normalizePrefixSlot m := by
  intro m hm hn
  unfold normalizePrefixSlot
  split <;> rename_i h1
  · omega_arith
  · split <;> omega_arith

def normalizePrefixWrites : List (Nat × Nat) := [(1216,72),(1360,72),(3952,64),(6328,1008)]

theorem normalize_prefix_slot_range : ∀m,2≤m → m≤16 → normalizePrefixSlot m=1216 ∨
    (6328≤normalizePrefixSlot m ∧ normalizePrefixSlot m+72≤7336) := by
  intro m hm hn
  unfold normalizePrefixSlot
  split <;> rename_i h1
  · omega_arith
  · split <;> omega_arith

theorem NormalizePrefixFrame.writes {base : Addr} {out : Nat} {m m' : Mem}
    (frame : NormalizePrefixFrame base out m m') (range : out=1216 ∨ (6328≤out ∧ out+72≤7336)) :
    VG.Proof.Weierstrass.Unch base normalizePrefixWrites m m' := by
  intro x hx
  have h0 := hx (1216,72) (by decide)
  have h1 := hx (1360,72) (by decide)
  have h2 := hx (3952,64) (by decide)
  have h3 := hx (6328,1008) (by decide)
  apply frame <;> omega_arith

theorem normalize_prefix_readonly : ∀w∈normalizePrefixWrites,w.1+w.2≤3232 ∨ 3952≤w.1 := by decide

structure NormalizePrefixInv (base table : Addr) (W count : Nat) (s : State)
    (X Y Z : Nat → Fin fieldPrime) : Prop where
  workspace : Scr s base W
  tablePtr : Ptr s .x26 table 3456
  tableValues : NormalizeTable table s X Y Z
  bounds : ∀i,1≤i → i≤count → wordsVal s.mem base (normalizePrefixSlot i) 9<fieldPrime
  values : ∀i,1≤i → i≤count →
    Fin.ofNat fieldPrime (wordsVal s.mem base (normalizePrefixSlot i) 9)=normalizeProduct Z i

theorem normalize_prefix_start {base table : Addr} {W : Nat} {s : State}
    {X Y Z : Nat → Fin fieldPrime} (ctx : NormalizeContext base table W s)
    (tableValues : NormalizeTable table s X Y Z)
    (boundFirst : wordsVal s.mem base 424 9<fieldPrime)
    (valueFirst : Fin.ofNat fieldPrime (wordsVal s.mem base 424 9)=Z 0) :
    NormalizePrefixInv base table W 1 s X Y Z := by
  refine ⟨ctx.workspace,ctx.readTable,tableValues,?_,?_⟩
  · intro i hi hn
    have he : i=1 := by omega_arith
    rw [he]
    exact boundFirst
  · intro i hi hn
    have he : i=1 := by omega_arith
    rw [he]
    change Fin.ofNat fieldPrime (wordsVal s.mem base 424 9)=1*Z 0
    rw [Lean.Grind.Semiring.one_mul]
    exact valueFirst

theorem normalize_prefix_advance {base table : Addr} {W count : Nat} {s : State}
    {X Y Z : Nat → Fin fieldPrime} (layout : NormalizeLayout base table W)
    (inv : NormalizePrefixInv base table W count s X Y Z) (one : 1≤count) (limit : count<16) :
    WP isa (normalizePrefixStep (216*count+144) (normalizePrefixSlot (count+1)) (normalizePrefixSlot count)) s fun t =>
      NormalizePrefixInv base table W (count+1) t X Y Z ∧ Outside base 0 W s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.v .v31=s.v .v31 ∧
      Outside base 1216 6120 s.mem t.mem ∧ VG.Proof.Weierstrass.Unch base normalizePrefixWrites s.mem t.mem := by
  have outFit := normalize_prefix_slot_fits (count+1) (by omega_arith) (by omega_arith)
  have prevFit := normalize_prefix_slot_fits count one (by omega_arith)
  have boundZ := inv.tableValues.canonical count limit 2 (by decide)
  change wordsVal s.mem table (216*count+144) 9<fieldPrime at boundZ
  refine WP.mono (normalize_prefix_step_ok layout inv.workspace inv.tablePtr (by omega_arith)
    (by omega_arith) (by have h:=layout.workspaceSize; omega_arith) (by have h:=layout.workspaceSize; omega_arith)
    (normalize_prefix_slot_copy_apart count one (by omega_arith))
    (normalize_prefix_slot_scratch_apart count one (by omega_arith))
    (inv.bounds count one (Nat.le_refl _)) boundZ)
    fun t ⟨bound,prod,frame,zero,rd,wr,sp,gp,v31⟩ => ?_
  have outRoom : normalizePrefixSlot (count+1)+72≤W := by have h:=layout.workspaceSize; omega_arith
  have outside := frame.workspace outRoom (by have h:=layout.workspaceSize; omega_arith)
  have past (k : Nat) (hk : 1≤k) (hcount : k≤count) :
      wordsVal t.mem base (normalizePrefixSlot k) 9=wordsVal s.mem base (normalizePrefixSlot k) 9 := by
    have fit := normalize_prefix_slot_fits k hk (by omega_arith)
    exact frame.wordsVal 9 _ (normalize_prefix_slot_copy_apart k hk (by omega_arith))
      (normalize_prefix_slots_apart count limit k hcount hk)
      (normalize_prefix_slot_scratch_apart k hk (by omega_arith)) (by omega_arith)
  have zvalue := inv.tableValues.zValue count limit
  change Fin.ofNat fieldPrime (wordsVal s.mem table (216*count+144) 9)=Z count at zvalue
  have outValue : Fin.ofNat fieldPrime (wordsVal t.mem base (normalizePrefixSlot (count+1)) 9)=normalizeProduct Z (count+1) := by
    rw [prod,ordinary_mul,inv.values count one (Nat.le_refl _),zvalue]
    rfl
  refine ⟨⟨⟨zero,by rw [wr]; exact inv.workspace.wr,inv.workspace.nowrap,inv.workspace.enc⟩,
    ⟨(gp .x26 (by decide)).trans inv.tablePtr.reg,by rw [rd,wr]; exact inv.tablePtr.ld,inv.tablePtr.enc⟩,
    inv.tableValues.of_workspace_write layout.tableApart outside,?_,?_⟩,outside,zero,rd,wr,sp,gp,v31,frame.region
      (normalize_prefix_slot_floor (count+1) (by omega_arith) (by omega_arith)) outFit,
      frame.writes (normalize_prefix_slot_range (count+1) (by omega_arith) (by omega_arith))⟩
  · intro k hk hcount
    by_cases eqLast : k=count+1
    · rw [eqLast]; exact bound
    · rw [past k hk (by omega_arith)]
      exact inv.bounds k hk (by omega_arith)
  · intro k hk hcount
    by_cases eqLast : k=count+1
    · rw [eqLast]; exact outValue
    · rw [past k hk (by omega_arith)]
      exact inv.values k hk (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native
