module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeStoreCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldEnv
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizePrefixInv
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldMul
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldSquare

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem field_table_load_ok {base table : Addr} {W z out : Nat} {s : State} {loc : Nat → Nat}
    {V : List Nat} {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (layout : NormalizeLayout base table W) (hs : Scr s base W) (pt : Ptr s .x26 table 3456)
    (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (hz : z+72≤3456) (hz8 : z%8=0) (hout : loc out+72≤W) (hout8 : loc out%8=0)
    (boundZ : wordsVal s.mem table z 9<fieldPrime)
    (fits : ∀x∈V,loc x+72≤W)
    (apart : ∀x∈V,x≠out → loc x+72≤loc out ∨ loc out+72≤loc x) :
    WP isa (.block (normalizeCopy 9 z (loc out))) s fun t =>
      OrdinaryInv base fieldPrime loc (out::V)
        (Function.update E out (Fin.ofNat fieldPrime (wordsVal s.mem table z 9))) (Function.update caps out 1) t ∧
      Scr t base W ∧ (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.sp=s.sp ∧ t.v .v31=s.v .v31 ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ Outside base (loc out) 72 s.mem t.mem := by
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by
    simp only [normalizeCopy,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,vdstOf,and_self])
    (normalize_copy_ok layout.tableApart 9 hs pt hz hout hz8 hout8))
    fun t ⟨⟨value,k,outside⟩,v⟩ => ?_
  have ni := inv.update outside apart (fun x hx => by have h:=fits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [value,Nat.one_mul] using boundZ) (congrArg (Fin.ofNat fieldPrime) value)
  exact ⟨ni,hs.of_keepRegs k (by decide),fun r hr => k.gpr r ((by decide : ∀r∈preserved,r∉[Reg.x1]) r hr),
    k.sp,congrFun v .v31,k.rd,k.wr,outside⟩

theorem field_table_store_ok {base table : Addr} {W dest a : Nat} {s : State} {loc : Nat → Nat}
    {V : List Nat} {E : Nat → Fin fieldPrime} {caps : Nat → Nat}
    (layout : NormalizeLayout base table W) (hs : Scr s base W) (pt : PtrW s .x26 table 3456)
    (inv : OrdinaryInv base fieldPrime loc V E caps s) (readA : a∈V) (capA : caps a=1)
    (ha : loc a+72≤W) (ha8 : loc a%8=0) (hd : dest+72≤3456) (hd8 : dest%8=0)
    (fits : ∀x∈V,loc x+72≤W) :
    WP isa (.block (normalizeStoreCopy 9 (loc a) dest)) s fun t =>
      OrdinaryInv base fieldPrime loc V E caps t ∧ Scr t base W ∧
      wordsVal t.mem table dest 9<fieldPrime ∧ Fin.ofNat fieldPrime (wordsVal t.mem table dest 9)=E a ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.sp=s.sp ∧ t.v .v31=s.v .v31 ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ Outside table dest 72 s.mem t.mem := by
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by
    simp only [normalizeStoreCopy,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,vdstOf,and_self])
    (normalize_store_copy_ok layout.tableApart.disjoint 9 hs pt ha hd ha8 hd8))
    fun t ⟨⟨value,k,outside⟩,v⟩ => ?_
  have workspaceSame : Unch base [(W,2^64)] s.mem t.mem :=
    (outside.mono (by omega_arith) (by omega_arith)).unch_far layout.tableApart.disjoint
  have same (x : Nat) (hx : x∈V) : wordsVal t.mem base (loc x) 9=wordsVal s.mem base (loc x) 9 :=
    workspaceSame.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (fits x hx))
      (by have h:=fits x hx; have e:=hs.enc; omega_arith)
  have ni : OrdinaryInv base fieldPrime loc V E caps t :=
    ⟨fun x hx => by rw [same x hx]; exact inv.bound x hx,
     fun x hx => by rw [same x hx]; exact inv.value x hx⟩
  have bound := inv.bound a readA
  rw [capA,Nat.one_mul] at bound
  exact ⟨ni,hs.of_keepRegs k (by decide),by rw [value]; exact bound,by rw [value]; exact inv.value a readA,
    fun r hr => k.gpr r ((by decide : ∀r∈preserved,r∉[Reg.x1]) r hr),k.sp,congrFun v .v31,k.rd,k.wr,outside⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def normalizeBackSlot (prev : Nat) : Nat → Nat
  | 0 => 1504
  | 1 => 1288
  | 2 => 1432
  | 3 => 1360
  | _ => prev

structure NormalizeBackLayout (prev : Nat) : Prop where
  previous : prev=424 ∨ 6328≤prev
  fits : prev+72≤7336

theorem normalize_back_layout_prefix {n : Nat} (one : 1≤n) (limit : n<16) :
    NormalizeBackLayout (normalizePrefixSlot n) := by
  constructor
  · unfold normalizePrefixSlot
    split <;> rename_i h1
    · exact Or.inl rfl
    · split <;> omega_arith
  · exact normalize_prefix_slot_fits n one (by omega_arith)

theorem NormalizeBackLayout.slots_fit {prev : Nat} (h : NormalizeBackLayout prev) :
    ∀x<5,normalizeBackSlot prev x+72≤8192 := by
  intro x hx
  have hc : x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 := by omega_arith
  rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp only [normalizeBackSlot] <;> have hf:=h.fits <;> omega_arith

theorem NormalizeBackLayout.slots_scratch {prev : Nat} (h : NormalizeBackLayout prev) :
    ∀x<5,normalizeBackSlot prev x+72≤3952 ∨ 4024≤normalizeBackSlot prev x := by
  intro x hx
  have hc : x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 := by omega_arith
  rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp only [normalizeBackSlot]
  all_goals rcases h.previous with hp|hp <;> omega_arith

theorem NormalizeBackLayout.slots_apart {prev : Nat} (h : NormalizeBackLayout prev) :
    ∀x<5,∀y<5,x≠y → normalizeBackSlot prev x+72≤normalizeBackSlot prev y ∨
      normalizeBackSlot prev y+72≤normalizeBackSlot prev x := by
  intro x hx y hy hne
  have xc : x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 := by omega_arith
  have yc : y=0 ∨ y=1 ∨ y=2 ∨ y=3 ∨ y=4 := by omega_arith
  rcases xc with rfl|rfl|rfl|rfl|rfl <;> rcases yc with rfl|rfl|rfl|rfl|rfl <;>
    simp only [normalizeBackSlot] at *
  all_goals rcases h.previous with hp|hp <;> omega_arith

theorem normalize_back_small : ∀prev,∀x<4,normalizeBackSlot prev x+72≤3520 := by
  intro prev x hx
  have hc : x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega_arith
  rcases hc with rfl|rfl|rfl|rfl <;> simp only [normalizeBackSlot] <;> decide

theorem normalize_back_temp_bounds : ∀prev,∀x<4,1288≤normalizeBackSlot prev x ∧ normalizeBackSlot prev x+72≤1576 := by
  intro prev x hx
  have hc : x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega_arith
  rcases hc with rfl|rfl|rfl|rfl <;> simp only [normalizeBackSlot] <;> decide

theorem NormalizeContext.advance {base table : Addr} {W : Nat} {s t : State}
    (ctx : NormalizeContext base table W s) (workspace : Scr t base W)
    (gp : ∀r∈preserved,t.gpr r=s.gpr r) (rd : t.rd=s.rd) (wr : t.wr=s.wr) :
    NormalizeContext base table W t := by
  exact ⟨workspace,⟨(gp .x26 (by decide)).trans ctx.readTable.reg,by rw [rd,wr]; exact ctx.readTable.ld,ctx.readTable.enc⟩,
    ⟨(gp .x26 (by decide)).trans ctx.tableW.reg,by rw [wr]; exact ctx.tableW.st,ctx.tableW.enc,ctx.tableW.nowrap⟩⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.Proof.Mont

def NormalizeBackFrame (base table : Addr) (row bytes : Nat) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1288 ∨ 1576≤ofs base x) → (ofs base x<3952 ∨ 4024≤ofs base x) →
    (ofs table x<216*row ∨ 216*row+bytes≤ofs table x) → m' x=m x

theorem NormalizeBackFrame.refl (base table : Addr) (row bytes : Nat) (m : Mem) :
    NormalizeBackFrame base table row bytes m m := fun _ _ _ _ => rfl

theorem NormalizeBackFrame.trans {base table : Addr} {row bytes : Nat} {m m' m'' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (k : NormalizeBackFrame base table row bytes m' m'') :
    NormalizeBackFrame base table row bytes m m'' := fun x hw ht hr => (k x hw ht hr).trans (h x hw ht hr)

theorem NormalizeBackFrame.mono {base table : Addr} {row bytes bytes' : Nat} {m m' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (le : bytes≤bytes') :
    NormalizeBackFrame base table row bytes' m m' := by
  intro x hw ht hr
  apply h x hw ht
  omega_arith

theorem NormalizeBackFrame.of_field {base table : Addr} {row out : Nat} {m m' : Mem}
    (h : FieldFrame base out m m') (lo : 1288≤out) (hi : out+72≤1576) :
    NormalizeBackFrame base table row 0 m m' := by
  intro x hw ht _
  apply h x (by omega_arith) ht

theorem NormalizeBackFrame.of_load {base table : Addr} {row : Nat} {m m' : Mem}
    (h : Outside base 1360 72 m m') : NormalizeBackFrame base table row 0 m m' := by
  intro x hw _ _
  apply h x
  omega_arith

theorem NormalizeBackFrame.of_store {base table : Addr} {row bytes dest : Nat} {m m' : Mem}
    (h : Outside table dest 72 m m') (lo : 216*row≤dest) (hi : dest+72≤216*row+bytes) :
    NormalizeBackFrame base table row bytes m m' := by
  intro x _ _ hr
  apply h x
  omega_arith

theorem NormalizeBackFrame.table_byte {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hW : 4024≤W) {d : Nat} (hd : d<3456) (outsideRow : d<216*row ∨ 216*row+bytes≤d) :
    m' (off table d)=m (off table d) := by
  apply h
  · have e:=apart d hd; omega_arith
  · have e:=apart d hd; omega_arith
  · rw [ofs_off0 table (by omega_arith)]
    exact outsideRow

theorem NormalizeBackFrame.workspace_byte {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hEnc : W≤32768) (rowFit : 216*row+bytes≤3456) {d : Nat} (hd : d<W)
    (outsideWork : d<1288 ∨ 1576≤d) (outsideScratch : d<3952 ∨ 4024≤d) :
    m' (off base d)=m (off base d) := by
  have address : ofs base (off base d)=d := ofs_off0 base (by omega_arith)
  apply h
  · rw [address]; exact outsideWork
  · rw [address]; exact outsideScratch
  · have notTable := apart.disjoint (off base d) (by
      change ofs base (off base d)+1≤W
      rw [address]; omega_arith)
    have tableLow : 3456≤ofs table (off base d) := by
      change ¬ofs table (off base d)+1≤3456 at notTable
      omega_arith
    exact Or.inr (Nat.le_trans rowFit tableLow)

theorem NormalizeBackFrame.table_words {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hW : 4024≤W) : ∀n d,d+8*n≤3456 → (d+8*n≤216*row ∨ 216*row+bytes≤d) →
      wordsVal m' table d n=wordsVal m table d n
  | 0,_,_,_ => rfl
  | n+1,d,hd,hr => by
    have wordEq : word m' table d=word m table d := by
      apply Mem.readW_congr
      intro i hi
      have address : off table d+BitVec.ofNat 64 i=off table (d+i) := VG.Offset.add_ofNat_add_ofNat table d i
      rw [address]
      exact h.table_byte apart hW (by omega_arith) (by omega_arith)
    simp only [VG.Proof.Mont.wordsVal]
    rw [wordEq,h.table_words apart hW n (d+8) (by omega_arith) (by omega_arith)]

theorem NormalizeBackFrame.workspace_words {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hEnc : W≤32768) (rowFit : 216*row+bytes≤3456) : ∀n d,d+8*n≤W →
      (d+8*n≤1288 ∨ 1576≤d) → (d+8*n≤3952 ∨ 4024≤d) → wordsVal m' base d n=wordsVal m base d n
  | 0,_,_,_,_ => rfl
  | n+1,d,hd,hw,ht => by
    have wordEq : word m' base d=word m base d := by
      apply Mem.readW_congr
      intro i hi
      have address : off base d+BitVec.ofNat 64 i=off base (d+i) := VG.Offset.add_ofNat_add_ofNat base d i
      rw [address]
      exact h.workspace_byte apart hEnc rowFit (by omega_arith) (by omega_arith) (by omega_arith)
    simp only [VG.Proof.Mont.wordsVal]
    rw [wordEq,h.workspace_words apart hEnc rowFit n (d+8) (by omega_arith) (by omega_arith) (by omega_arith)]

theorem NormalizeBackFrame.readonly {base table : Addr} {row bytes : Nat} {m m' : Mem}
    (h : NormalizeBackFrame base table row bytes m m') (apart : TableWorkspaceApart base table 8192)
    (rowFit : 216*row+bytes≤3456) {d : Nat} (lo : 3232≤d) (hi : d<3952) :
    m' (off base d)=m (off base d) :=
  h.workspace_byte apart (by decide) rowFit (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

structure NormalizeBackState (base table : Addr) (prev : Nat) (V : List Nat)
    (E : Nat → Fin fieldPrime) (s : State) : Prop where
  context : NormalizeContext base table 8192 s
  inv : OrdinaryInv base fieldPrime (normalizeBackSlot prev) V E (fun _ => 1) s

structure NormalizeBackKept (s t : State) : Prop where
  gp : ∀r∈preserved,t.gpr r=s.gpr r
  sp : t.sp=s.sp
  v31 : t.v .v31=s.v .v31
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem NormalizeBackKept.refl (s : State) : NormalizeBackKept s s :=
  ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩

theorem NormalizeBackKept.trans {s t u : State} (h : NormalizeBackKept s t)
    (k : NormalizeBackKept t u) : NormalizeBackKept s u :=
  ⟨fun r hr => (k.gp r hr).trans (h.gp r hr),k.sp.trans h.sp,k.v31.trans h.v31,
    k.rd.trans h.rd,k.wr.trans h.wr⟩

private theorem update_one (o : Nat) : Function.update (fun _ : Nat => 1) o 1=(fun _ => 1) := by
  funext x
  simp only [Function.update_apply,ite_self]

theorem normalize_back_mul_ok {base table : Addr} {prev row o a b : Nat}
    {V : List Nat} {E : Nat → Fin fieldPrime} {s : State}
    (layout : NormalizeBackLayout prev) (state : NormalizeBackState base table prev V E s)
    (live : ∀x∈V,x<5) (out : o<4) (readA : a∈V) (readB : b∈V) :
    WP isa (normalizeMulStep (normalizeBackSlot prev o) (normalizeBackSlot prev a) (normalizeBackSlot prev b)) s fun t =>
      NormalizeBackState base table prev (o::V) (Function.update E o (E a*E b)) t ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 0 s.mem t.mem := by
  refine WP.mono (field_mul_ok state.context.workspace (by decide) state.inv readA readB rfl rfl
    (layout.slots_fit o (by omega_arith)) (fun x hx => layout.slots_fit x (live x hx))
    (fun x hx => by have h:=layout.slots_scratch x (live x hx); omega_arith)
    (fun x hx hne => layout.slots_apart x (live x hx) o (by omega_arith) hne))
    fun t ⟨inv,scr,gp,sp,v31,rd,wr,frame⟩ => ?_
  rw [update_one] at inv
  have bounds:=normalize_back_temp_bounds prev o out
  exact ⟨⟨state.context.advance scr gp rd wr,inv⟩,⟨gp,sp,v31,rd,wr⟩,
    NormalizeBackFrame.of_field frame bounds.1 bounds.2⟩

theorem normalize_back_square_ok {base table : Addr} {prev row o a : Nat}
    {V : List Nat} {E : Nat → Fin fieldPrime} {s : State}
    (layout : NormalizeBackLayout prev) (state : NormalizeBackState base table prev V E s)
    (live : ∀x∈V,x<5) (out : o<4) (input : a<4) (readA : a∈V) :
    WP isa (normalizeSquareStep (normalizeBackSlot prev o) (normalizeBackSlot prev a)) s fun t =>
      NormalizeBackState base table prev (o::V) (Function.update E o (E a*E a)) t ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 0 s.mem t.mem := by
  refine WP.mono (field_square_ok state.context.workspace (by decide) (by decide) state.inv readA rfl
    (normalize_back_small prev o out) (normalize_back_small prev a input)
    (fun x hx => layout.slots_fit x (live x hx))
    (fun x hx => by simpa only [VG.Impl.Weierstrass.AArch64.Mont.moAt,Nat.reduceMul,Nat.reduceAdd] using layout.slots_scratch x (live x hx))
    (fun x hx hne => layout.slots_apart x (live x hx) o (by omega_arith) hne))
    fun t ⟨inv,scr,gp,sp,v31,rd,wr,frame⟩ => ?_
  rw [update_one] at inv
  have bounds:=normalize_back_temp_bounds prev o out
  exact ⟨⟨state.context.advance scr gp rd wr,inv⟩,⟨gp,sp,v31,rd,wr⟩,
    NormalizeBackFrame.of_field frame bounds.1 bounds.2⟩

theorem normalize_back_load_ok {base table : Addr} {prev row z : Nat}
    {V : List Nat} {E : Nat → Fin fieldPrime} {s : State}
    (layout : NormalizeLayout base table 8192) (backLayout : NormalizeBackLayout prev)
    (state : NormalizeBackState base table prev V E s) (live : ∀x∈V,x<5)
    (fit : z+72≤3456) (aligned : z%8=0) (bound : wordsVal s.mem table z 9<fieldPrime) :
    WP isa (.block (normalizeCopy 9 z 1360)) s fun t =>
      NormalizeBackState base table prev (3::V)
        (Function.update E 3 (Fin.ofNat fieldPrime (wordsVal s.mem table z 9))) t ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 0 s.mem t.mem := by
  refine WP.mono (field_table_load_ok (out:=3) layout state.context.workspace state.context.readTable state.inv
    fit aligned (by simp [normalizeBackSlot]) (by simp [normalizeBackSlot]) bound (fun x hx => backLayout.slots_fit x (live x hx))
    (fun x hx hne => backLayout.slots_apart x (live x hx) 3 (by decide) hne))
    fun t ⟨inv,scr,gp,sp,v31,rd,wr,frame⟩ => ?_
  rw [update_one] at inv
  exact ⟨⟨state.context.advance scr gp rd wr,inv⟩,⟨gp,sp,v31,rd,wr⟩,NormalizeBackFrame.of_load frame⟩

theorem normalize_back_store_ok {base table : Addr} {prev row dest bytes : Nat}
    {V : List Nat} {E : Nat → Fin fieldPrime} {s : State}
    (layout : NormalizeLayout base table 8192) (backLayout : NormalizeBackLayout prev)
    (state : NormalizeBackState base table prev V E s) (live : ∀x∈V,x<5) (readA : 3∈V)
    (fit : dest+72≤3456) (aligned : dest%8=0) (lo : 216*row≤dest) (hi : dest+72≤216*row+bytes) :
    WP isa (.block (normalizeStoreCopy 9 1360 dest)) s fun t =>
      NormalizeBackState base table prev V E t ∧ NormalizeBackKept s t ∧
      wordsVal t.mem table dest 9<fieldPrime ∧ Fin.ofNat fieldPrime (wordsVal t.mem table dest 9)=E 3 ∧
      NormalizeBackFrame base table row bytes s.mem t.mem ∧ Outside table dest 72 s.mem t.mem := by
  refine WP.mono (field_table_store_ok (a:=3) layout state.context.workspace state.context.tableW state.inv
    readA rfl (by simp [normalizeBackSlot]) (by simp [normalizeBackSlot]) fit aligned (fun x hx => backLayout.slots_fit x (live x hx)))
    fun t ⟨inv,scr,bound,value,gp,sp,v31,rd,wr,frame⟩ => ?_
  exact ⟨⟨state.context.advance scr gp rd wr,inv⟩,⟨gp,sp,v31,rd,wr⟩,bound,value,NormalizeBackFrame.of_store frame lo hi,frame⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def normalizeBackY (row : Nat) : Prog isa :=
  .seq (normalizeMulStep 1432 1432 1288) <|
  .seq (.block (normalizeCopy 9 (216*row+72) 1360)) <|
  .seq (normalizeMulStep 1360 1360 1432) <|
  .block (normalizeStoreCopy 9 1360 (216*row+72))

def normalizeBackYEnv (E : Nat → Fin fieldPrime) (Y : Fin fieldPrime) : Nat → Fin fieldPrime :=
  let e1:=Function.update E 2 (E 2*E 1)
  let e2:=Function.update e1 3 Y
  Function.update e2 3 (e2 3*e2 2)

theorem normalize_back_y_ok {base table : Addr} {prev row : Nat} {E : Nat → Fin fieldPrime}
    {V : List Nat} {s : State}
    (layout : NormalizeLayout base table 8192) (bl : NormalizeBackLayout prev)
    (state : NormalizeBackState base table prev V E s) (live : ∀x∈V,x<5)
    (read2 : 2∈V) (read1 : 1∈V) (rowBound : row<16)
    (boundY : wordsVal s.mem table (216*row+72) 9<fieldPrime) :
    WP isa (normalizeBackY row) s fun t =>
      NormalizeBackState base table prev (3::3::2::V)
        (normalizeBackYEnv E (Fin.ofNat fieldPrime (wordsVal s.mem table (216*row+72) 9))) t ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 144 s.mem t.mem ∧
      wordsVal t.mem table (216*row+72) 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem table (216*row+72) 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem table (216*row+72) 9)*(E 2*E 1) ∧
      wordsVal t.mem table (216*row) 9=wordsVal s.mem table (216*row) 9 := by
  rw [normalizeBackY,WP.seq_iff]
  refine WP.mono (normalize_back_mul_ok (row:=row) (o:=2) (a:=2) (b:=1) bl state live
    (by decide) read2 read1) fun a ⟨i1,k1,f1⟩ => ?_
  have ySame := f1.table_words layout.tableApart (by decide) 9 (216*row+72) (by omega_arith) (Or.inr (by omega_arith))
  have bound : wordsVal a.mem table (216*row+72) 9<fieldPrime := by rw [ySame]; exact boundY
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_load_ok (row:=row) layout bl i1
    (by intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl|hx; decide; exact live x hx)
    (by omega_arith) (by omega_arith) bound) fun b ⟨i2,k2,f2⟩ => ?_
  rw [ySame] at i2
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_mul_ok (row:=row) (o:=3) (a:=3) (b:=2) bl i2
    (by intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl|rfl|hx; decide; decide; exact live x hx)
    (by decide) (by simp) (by simp)) fun c ⟨i3,k3,f3⟩ => ?_
  refine WP.mono (normalize_back_store_ok (row:=row) (bytes:=144) layout bl i3
    (by intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl|rfl|rfl|hx; decide; decide; decide; exact live x hx)
    (by simp) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨i4,k4,byY,value,f4,exactStore⟩ => ?_
  have before := f1.trans (f2.trans f3)
  have xSame := before.table_words layout.tableApart (by decide) 9 (216*row) (by omega_arith) (Or.inr (by omega_arith))
  -- The final store writes only Y. Its exact copy frame also follows directly from the code.
  have xFinal : wordsVal t.mem table (216*row) 9=wordsVal c.mem table (216*row) 9 := by
    exact exactStore.wordsVal (Or.inl (by omega_arith)) (by omega_arith)
  refine ⟨i4,k1.trans (k2.trans (k3.trans k4)),(before.mono (by decide)).trans f4,byY,?_,xFinal.trans xSame⟩
  simpa only [Function.update_self,Function.update_of_ne (by decide : (2:Nat)≠3)] using value

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def normalizeBackX (prev row : Nat) : Prog isa :=
  .seq (.block (normalizeCopy 9 (216*row+144) 1360)) <|
  .seq (normalizeMulStep 1288 1504 prev) <|
  .seq (normalizeMulStep 1504 1504 1360) <|
  .seq (normalizeSquareStep 1432 1288) <|
  .seq (.block (normalizeCopy 9 (216*row) 1360)) <|
  .seq (normalizeMulStep 1360 1360 1432) <|
  .block (normalizeStoreCopy 9 1360 (216*row))

def normalizeBackXEnv (E : Nat → Fin fieldPrime) (X Z : Fin fieldPrime) : Nat → Fin fieldPrime :=
  let e1:=Function.update E 3 Z
  let e2:=Function.update e1 1 (e1 0*e1 4)
  let e3:=Function.update e2 0 (e2 0*e2 3)
  let e4:=Function.update e3 2 (e3 1*e3 1)
  let e5:=Function.update e4 3 X
  Function.update e5 3 (e5 3*e5 2)

theorem normalize_back_x_ok {base table : Addr} {prev row : Nat} {E : Nat → Fin fieldPrime} {s : State}
    (layout : NormalizeLayout base table 8192) (bl : NormalizeBackLayout prev)
    (state : NormalizeBackState base table prev [0,4] E s) (rowBound : row<16)
    (boundX : wordsVal s.mem table (216*row) 9<fieldPrime)
    (boundZ : wordsVal s.mem table (216*row+144) 9<fieldPrime) :
    WP isa (normalizeBackX prev row) s fun t =>
      NormalizeBackState base table prev [3,3,2,0,1,3,0,4]
        (normalizeBackXEnv E (Fin.ofNat fieldPrime (wordsVal s.mem table (216*row) 9))
          (Fin.ofNat fieldPrime (wordsVal s.mem table (216*row+144) 9))) t ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 72 s.mem t.mem ∧
      wordsVal t.mem table (216*row) 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem table (216*row) 9)=
        E 0*E 4*(E 0*E 4)*(Fin.ofNat fieldPrime (wordsVal s.mem table (216*row) 9)) := by
  rw [normalizeBackX,WP.seq_iff]
  refine WP.mono (normalize_back_load_ok (row:=row) layout bl state (by simp) (by omega_arith) (by omega_arith) boundZ) fun a ⟨i1,k1,f1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_mul_ok (row:=row) (o:=1) (a:=0) (b:=4) bl i1 (by simp) (by decide) (by simp) (by simp)) fun b ⟨i2,k2,f2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_mul_ok (row:=row) (o:=0) (a:=0) (b:=3) bl i2 (by simp) (by decide) (by simp) (by simp)) fun c ⟨i3,k3,f3⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_square_ok (row:=row) (o:=2) (a:=1) bl i3 (by simp) (by decide) (by decide) (by simp)) fun d ⟨i4,k4,f4⟩ => ?_
  have fx : NormalizeBackFrame base table row 0 s.mem d.mem := f1.trans (f2.trans (f3.trans f4))
  have xSame := fx.table_words layout.tableApart (by decide) 9 (216*row) (by omega_arith) (Or.inr (by omega_arith))
  have xd : wordsVal d.mem table (216*row) 9<fieldPrime := by rw [xSame]; exact boundX
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_load_ok (row:=row) layout bl i4 (by simp) (by omega_arith) (by omega_arith) xd)
    fun e ⟨i5,k5,f5⟩ => ?_
  rw [xSame] at i5
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_mul_ok (row:=row) (o:=3) (a:=3) (b:=2) bl i5 (by simp) (by decide) (by simp) (by simp))
    fun f ⟨i6,k6,f6⟩ => ?_
  refine WP.mono (normalize_back_store_ok (row:=row) (bytes:=72) layout bl i6 (by simp) (by simp)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨i7,k7,bound,value,f7,_⟩ => ?_
  refine ⟨i7,k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans k7))))),
    (fx.trans (f5.trans f6)).mono (by decide) |>.trans f7,bound,?_⟩
  rw [value]
  simp only [Function.update_self,Function.update_of_ne (by decide : (0:Nat)≠3),
    Function.update_of_ne (by decide : (4:Nat)≠3),Function.update_of_ne (by decide : (1:Nat)≠0),
Function.update_of_ne (by decide : (2:Nat)≠3)]
  exact Lean.Grind.CommRing.mul_comm _ _

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def normalizeBackRow (prev row : Nat) : Prog isa := .seq (normalizeBackX prev row) (normalizeBackY row)

def normalizeBackRowEnv (E : Nat → Fin fieldPrime) (X Y Z : Fin fieldPrime) : Nat → Fin fieldPrime :=
  normalizeBackYEnv (normalizeBackXEnv E X Z) Y

theorem normalize_back_row_ok {base table : Addr} {prev row : Nat} {E : Nat → Fin fieldPrime} {s : State}
    (layout : NormalizeLayout base table 8192) (bl : NormalizeBackLayout prev)
    (state : NormalizeBackState base table prev [0,4] E s) (rowBound : row<16)
    (boundX : wordsVal s.mem table (216*row) 9<fieldPrime)
    (boundY : wordsVal s.mem table (216*row+72) 9<fieldPrime)
    (boundZ : wordsVal s.mem table (216*row+144) 9<fieldPrime) :
    WP isa (normalizeBackRow prev row) s fun t =>
      NormalizeBackState base table prev [3,3,2,3,3,2,0,1,3,0,4]
        (normalizeBackRowEnv E (Fin.ofNat fieldPrime (wordsVal s.mem table (216*row) 9))
          (Fin.ofNat fieldPrime (wordsVal s.mem table (216*row+72) 9))
          (Fin.ofNat fieldPrime (wordsVal s.mem table (216*row+144) 9))) t ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table row 144 s.mem t.mem ∧
      wordsVal t.mem table (216*row) 9<fieldPrime ∧ wordsVal t.mem table (216*row+72) 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem table (216*row) 9)=
        E 0*E 4*(E 0*E 4)*Fin.ofNat fieldPrime (wordsVal s.mem table (216*row) 9) ∧
      Fin.ofNat fieldPrime (wordsVal t.mem table (216*row+72) 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem table (216*row+72) 9)*((E 0*E 4*(E 0*E 4))*(E 0*E 4)) := by
  rw [normalizeBackRow,WP.seq_iff]
  refine WP.mono (normalize_back_x_ok layout bl state rowBound boundX boundZ)
    fun a ⟨i1,k1,f1,bx,vx⟩ => ?_
  have ySame := f1.table_words layout.tableApart (by decide) 9 (216*row+72) (by omega_arith) (Or.inr (by omega_arith))
  have byA : wordsVal a.mem table (216*row+72) 9<fieldPrime := by rw [ySame]; exact boundY
  refine WP.mono (normalize_back_y_ok layout bl i1 (by simp) (by simp) (by simp) rowBound byA)
    fun t ⟨i2,k2,f2,byY,vy,xSame⟩ => ?_
  rw [ySame] at i2 vy
  refine ⟨i2,k1.trans k2,(f1.mono (by decide)).trans f2,by rw [xSame]; exact bx,byY,
    by rw [xSame]; exact vx,?_⟩
  rw [vy]
  simp only [normalizeBackXEnv,Function.update_self,
    Function.update_of_ne (by decide : (2:Nat)≠3),Function.update_of_ne (by decide : (1:Nat)≠3),
    Function.update_of_ne (by decide : (1:Nat)≠2),Function.update_of_ne (by decide : (1:Nat)≠0),
    Function.update_of_ne (by decide : (0:Nat)≠3),Function.update_of_ne (by decide : (4:Nat)≠3)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

structure NormalizeBackInv (base table : Addr) (s : State)
    (X Y Z P : Nat → Fin fieldPrime) (I : Fin fieldPrime) : Prop where
  context : NormalizeContext base table 8192 s
  tableValues : NormalizeTable table s X Y Z
  prefixBound : ∀n,1≤n → n<16 → wordsVal s.mem base (normalizePrefixSlot n) 9<fieldPrime
  prefixValue : ∀n,1≤n → n<16 → Fin.ofNat fieldPrime (wordsVal s.mem base (normalizePrefixSlot n) 9)=P n
  inverseBound : wordsVal s.mem base 1504 9<fieldPrime
  inverseValue : Fin.ofNat fieldPrime (wordsVal s.mem base 1504 9)=I

def normalizeBackInput (I P : Fin fieldPrime) (x : Nat) : Fin fieldPrime := if x=0 then I else P

theorem normalize_back_input_ok {base table : Addr} {s : State} {row : Nat}
    {X Y Z P : Nat → Fin fieldPrime} {I : Fin fieldPrime}
    (inv : NormalizeBackInv base table s X Y Z P I) (lo : 1≤row) (hi : row<16) :
    NormalizeBackState base table (normalizePrefixSlot row) [0,4] (normalizeBackInput I (P row)) s := by
  refine ⟨inv.context,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · simpa only [normalizeBackSlot,Nat.one_mul] using inv.inverseBound
    · simpa only [normalizeBackSlot,Nat.one_mul] using inv.prefixBound row lo hi
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · simpa only [normalizeBackSlot,normalizeBackInput,ite_true] using inv.inverseValue
    · simpa only [normalizeBackSlot,normalizeBackInput,ite_eq_right (by decide : ¬(4:Nat)=0)] using inv.prefixValue row lo hi

theorem NormalizeBackFrame.prefix_words {base table : Addr} {row bytes n : Nat} {m m' : Mem}
    (frame : NormalizeBackFrame base table row bytes m m') (layout : NormalizeLayout base table 8192)
    (rowFit : 216*row+bytes≤3456) (lo : 1≤n) (hi : n<16) :
    wordsVal m' base (normalizePrefixSlot n) 9=wordsVal m base (normalizePrefixSlot n) 9 := by
  have h:=(normalize_back_layout_prefix lo hi)
  apply frame.workspace_words layout.tableApart (by decide) rowFit 9 _
  · have e:=h.fits; omega_arith
  · rcases h.previous with he|he <;> omega_arith
  · rcases h.previous with he|he <;> omega_arith

theorem NormalizeBackFrame.table_other {base table : Addr} {row i bytes c : Nat} {m m' : Mem}
    (frame : NormalizeBackFrame base table row bytes m m') (layout : NormalizeLayout base table 8192)
    (_hr : row<16) (hi : i<16) (hc : c<3) (hb : bytes≤144)
    (outside : i≠row ∨ c=2) :
    wordsVal m' table (normalizeEntrySlot i c) 9=wordsVal m table (normalizeEntrySlot i c) 9 := by
  apply frame.table_words layout.tableApart (by decide) 9 _
  · dsimp only [normalizeEntrySlot]; omega_arith
  · dsimp only [normalizeEntrySlot]
    rcases outside with h|rfl <;> omega_arith

theorem normalize_back_table_update {base table : Addr} {row : Nat} {s t : State}
    {X Y Z : Nat → Fin fieldPrime} {x y : Fin fieldPrime}
    (old : NormalizeTable table s X Y Z) (layout : NormalizeLayout base table 8192) (hr : row<16)
    (frame : NormalizeBackFrame base table row 144 s.mem t.mem)
    (bx : wordsVal t.mem table (216*row) 9<fieldPrime)
    (byY : wordsVal t.mem table (216*row+72) 9<fieldPrime)
    (vx : Fin.ofNat fieldPrime (wordsVal t.mem table (216*row) 9)=x)
    (vy : Fin.ofNat fieldPrime (wordsVal t.mem table (216*row+72) 9)=y) :
    NormalizeTable table t (Function.update X row x) (Function.update Y row y) Z := by
  constructor
  · intro i hi c hc
    by_cases he : i=row
    · subst i
      have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
      rcases cases with rfl|rfl|rfl
      · simpa only [normalizeEntrySlot,Nat.mul_zero,Nat.add_zero] using bx
      · simpa only [normalizeEntrySlot,Nat.mul_one] using byY
      · rw [frame.table_other layout hr hi (by decide) (by decide) (Or.inr rfl)]
        exact old.canonical row hi 2 (by decide)
    · rw [frame.table_other layout hr hi hc (by decide) (Or.inl he)]
      exact old.canonical i hi c hc
  · intro i hi
    by_cases he : i=row
    · subst i
      simpa only [Function.update_self,normalizeEntrySlot,Nat.mul_zero,Nat.add_zero] using vx
    · rw [Function.update_of_ne he,frame.table_other layout hr hi (by decide) (by decide) (Or.inl he)]
      exact old.xValue i hi
  · intro i hi
    by_cases he : i=row
    · subst i
      simpa only [Function.update_self,normalizeEntrySlot,Nat.mul_one] using vy
    · rw [Function.update_of_ne he,frame.table_other layout hr hi (by decide) (by decide) (Or.inl he)]
      exact old.yValue i hi
  · intro i hi
    rw [frame.table_other layout hr hi (by decide) (by decide) (Or.inr rfl)]
    exact old.zValue i hi

end VG.Proof.Weierstrass.AArch64.P521Native
