module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildAdvance
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildCounter
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildSeedStore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

def buildLoopStep : Prog isa := .seq buildMixedMachine (.seq buildAdvance (.block buildCounter))

theorem build_source27 : outerBlock027=outerBlock027.take 1 ++
    (buildStoreCopy .x20 27 1288 0 ++ (buildCopyPoint ++ buildCounter)) := by lit_decide

private theorem BuildCode_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem build_loop_step_wp {s : State} {Q : State → Prop} :
    WP isa (sequence [.block outerBlock016,callNormalSqr,.block outerBlock017,callNormalMul,
      .block outerBlock018,callNormalMul,.block outerBlock019,callNormalMul,
      .block outerBlock020,callNormalSqr,.block outerBlock021,callNormalMul,
      .block outerBlock022,callNormalMul,.block outerBlock023,callNormalSqr,
      .block outerBlock024,callNormalMul,.block outerBlock025,callNormalMul,
      .block outerBlock026,callNormalMul,.block outerBlock027]) s Q ↔ WP isa buildLoopStep s Q := by
  simp only [buildLoopStep,buildMixedMachine,buildAdvance,sequence,List.foldr_cons,List.foldr_nil]
  conv => lhs; rw [build_source27]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply BuildCode_wp_post_iff; intro t)

theorem build_table_phases_wp {s : State} {Q : State → Prop} :
    WP isa buildTable s Q ↔ WP isa (sequence [.block (outerBlock007.take 55),
      buildDoubleMachine,.block (outerBlock015.drop 283),loop22]) s Q := by
  simp only [buildTable,buildDoubleMachine,sequence,List.foldr_cons,List.foldr_nil]
  conv => lhs; rw [←List.take_append_drop 55 outerBlock007,←List.take_append_drop 283 outerBlock015]
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.Proof.Mont

def BuildLoopFrame (base table : Addr) (row bytes : Nat) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1288 ∨ 2152≤ofs base x) → (ofs base x<3952 ∨ 4024≤ofs base x) →
    (ofs table x<216*row ∨ 216*row+bytes≤ofs table x) → m' x=m x

theorem BuildLoopFrame.refl (base table : Addr) (row bytes : Nat) (m : Mem) :
    BuildLoopFrame base table row bytes m m := fun _ _ _ _ => rfl

theorem BuildLoopFrame.trans {base table : Addr} {row bytes : Nat} {m m' m'' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (k : BuildLoopFrame base table row bytes m' m'') :
    BuildLoopFrame base table row bytes m m'' := fun x hw ht hr => (k x hw ht hr).trans (h x hw ht hr)

theorem BuildLoopFrame.mono {base table : Addr} {row bytes bytes' : Nat} {m m' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (le : bytes≤bytes') :
    BuildLoopFrame base table row bytes' m m' := by
  intro x hw ht hr
  apply h x hw ht
  omega_arith

theorem BuildLoopFrame.of_field {base table : Addr} {row out : Nat} {m m' : Mem}
    (h : FieldFrame base out m m') (lo : 1288≤out) (hi : out+72≤2152) :
    BuildLoopFrame base table row 0 m m' := by
  intro x hw ht _
  apply h x (by omega_arith) ht

theorem BuildLoopFrame.of_store {base table : Addr} {row bytes dest : Nat} {m m' : Mem}
    (h : Outside table dest 72 m m') (lo : 216*row≤dest) (hi : dest+72≤216*row+bytes) :
    BuildLoopFrame base table row bytes m m' := by
  intro x _ _ hr
  apply h x
  omega_arith

theorem BuildLoopFrame.of_mixed {base table : Addr} {row : Nat} {m m' : Mem}
    (h : FieldProgramFrame base id buildMixedOps m m') : BuildLoopFrame base table row 0 m m' := by
  intro x hw ht _
  apply h x _ ht
  intro op hop
  have fit : 1288≤op.out ∧ op.out+72≤2152 := by
    simp only [buildMixedOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simpa only [id_eq] using (show ofs base x<op.out ∨ op.out+72≤ofs base x from by omega_arith)

theorem BuildLoopFrame.table_byte {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hW : 4024≤W) {d : Nat} (hd : d<3456) (outsideRow : d<216*row ∨ 216*row+bytes≤d) :
    m' (off table d)=m (off table d) := by
  apply h
  · have e:=apart d hd; omega_arith
  · have e:=apart d hd; omega_arith
  · rw [ofs_off0 table (by omega_arith)]
    exact outsideRow

theorem BuildLoopFrame.workspace_byte {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hEnc : W≤32768) (rowFit : 216*row+bytes≤3456) {d : Nat} (hd : d<W)
    (outsideWork : d<1288 ∨ 2152≤d) (outsideScratch : d<3952 ∨ 4024≤d) :
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

theorem BuildLoopFrame.table_words {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
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

theorem BuildLoopFrame.workspace_words {base table : Addr} {W row bytes : Nat} {m m' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (apart : TableWorkspaceApart base table W)
    (hEnc : W≤32768) (rowFit : 216*row+bytes≤3456) : ∀n d,d+8*n≤W →
      (d+8*n≤1288 ∨ 2152≤d) → (d+8*n≤3952 ∨ 4024≤d) → wordsVal m' base d n=wordsVal m base d n
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

theorem BuildLoopFrame.readonly {base table : Addr} {row bytes : Nat} {m m' : Mem}
    (h : BuildLoopFrame base table row bytes m m') (apart : TableWorkspaceApart base table 8192)
    (rowFit : 216*row+bytes≤3456) {d : Nat} (lo : 3232≤d) (hi : d<3952) :
    m' (off base d)=m (off base d) :=
  h.workspace_byte apart (by decide) rowFit (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

structure BuildLoopInv (C : Curve) (base table : Addr) (P : Point C) (m : Nat) (s : State) : Prop where
  context : NormalizeContext base table 8192 s
  writePointer : s.gpr .x20=off table (216*m)
  counter : s.gpr .x19=BitVec.ofNat 64 (16-m)
  peerX : wordsVal s.mem base 2800 9<fieldPrime
  peerY : wordsVal s.mem base 3160 9<fieldPrime
  peerValue : peerPoint C s.mem base=P
  currentBounds : canonicalPoint s.mem base 1504
  currentValue : InvJ C (pointAt C s.mem base 1504).1 (pointAt C s.mem base 1504).2.1
    (pointAt C s.mem base 1504).2.2 (mul m P)
  tableBounds : ∀i,i<m → ∀c,c<3 → wordsVal s.mem table (216*i+72*c) 9<fieldPrime
  tableValue : ∀i,i<m → InvJ C (pointAt C s.mem table (216*i)).1
    (pointAt C s.mem table (216*i)).2.1 (pointAt C s.mem table (216*i)).2.2 (mul (i+1) P)
  tableFirstZ : wordsVal s.mem table 144 9=1
  oneField : wordsVal s.mem base 424 9=1

theorem BuildLoopInv.write_row {C : Curve} {base table : Addr} {P : Point C} {m : Nat} {s : State}
    (inv : BuildLoopInv C base table P m s) (hi : m<16) : PtrW s .x20 (off table (216*m)) 216 := by
  have full:=inv.context.tableW
  constructor
  · exact inv.writePointer
  · intro d hd
    rw [VG.Offset.add_ofNat_add_ofNat]
    exact full.st (216*m+d) (by omega_arith)
  · decide
  · have le1 : (off table (216*m)).toNat≤table.toNat+216*m := by
      dsimp only [off]
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
    have h:=full.nowrap
    omega_arith

theorem BuildLoopInv.row_apart {C : Curve} {base table : Addr} {P : Point C} {m : Nat} {s : State}
    (_inv : BuildLoopInv C base table P m s) (layout : NormalizeLayout base table 8192) (hi : m<16) :
    Region.Disjoint ⟨base,8192⟩ ⟨off table (216*m),216⟩ := by
  exact layout.tableApart.disjoint.sub_right (VG.Offset.sub_base table (by omega_arith))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Weierstrass Spec.Weierstrass

 theorem wordsVal_off (m : Mem) (base : Addr) (shift : Nat) : ∀n d,
    wordsVal m (off base shift) d n=wordsVal m base (shift+d) n
  | 0,_ => rfl
  | n+1,d => by
    simp only [wordsVal]
    rw [wordsVal_off m base shift n (d+8)]
    have address : off (off base shift) d=off base (shift+d) := VG.Offset.add_ofNat_add_ofNat base shift d
    simp only [word,address,Nat.add_assoc]

theorem pointAt_copy {C : Curve} {m m' : Mem} {a b : Addr} {da db : Nat}
    (copy : ∀c,c<3 → wordsVal m' b (db+72*c) 9=wordsVal m a (da+72*c) 9) :
    pointAt C m' b db=pointAt C m a da := by
  have x:=copy 0 (by decide)
  have y:=copy 1 (by decide)
  have z:=copy 2 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul] at x y z
  simp only [pointAt,x,y,z]

theorem BuildLoopFrame.of_advance {base table : Addr} {row : Nat} {m m' : Mem}
    (hi : row<16)
    (cross : ∀x,8192≤ofs base x → (ofs (off table (216*row)) x<0 ∨ 216≤ofs (off table (216*row)) x) → m' x=m x)
    (workspace : Unch base [(1504,72),(1576,72),(1648,72),(8192,2^64)] m m') :
    BuildLoopFrame base table row 216 m m' := by
  intro x hw _ hr
  by_cases hx : ofs base x<8192
  · apply workspace x
    intro w hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl <;> simp only <;> omega_arith
  · apply cross x (by omega_arith)
    right
    have iff := VG.Offset.lt_iff x table (d:=216*row) (n:=216) (by omega_arith)
    change ofs (off table (216*row)) x<216 ↔ 216*row≤ofs table x ∧ ofs table x<216*row+216 at iff
    omega_arith

theorem NormalizeContext.of_public {base table : Addr} {s t : State}
    (context : NormalizeContext base table 8192 s) (ht : Scr t base 8192) (p : FieldPublic s t) :
    NormalizeContext base table 8192 t :=
  ⟨ht,⟨(p.gpr .x26 (by decide)).trans context.readTable.reg,
    by rw [p.rd,p.wr]; exact context.readTable.ld,context.readTable.enc⟩,
  ⟨(p.gpr .x26 (by decide)).trans context.tableW.reg,
    by rw [p.wr]; exact context.tableW.st,context.tableW.enc,context.tableW.nowrap⟩⟩

end VG.Proof.Weierstrass.AArch64.P521Native
