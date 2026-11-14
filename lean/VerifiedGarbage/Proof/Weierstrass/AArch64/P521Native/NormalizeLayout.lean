module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! Separate stack-table and workspace regions for batch P-521 normalization. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

/-- Every byte of the public stack table is outside the workspace write region. -/
def TableWorkspaceApart (workspace table : Addr) (W : Nat) : Prop :=
  ∀d,d<3456 → W≤ofs workspace (off table d)

structure NormalizeLayout (workspace table : Addr) (W : Nat) : Prop where
  workspaceSize : 7336≤W
  workspaceEnc : W≤32768
  tableApart : TableWorkspaceApart workspace table W

def normalizePrefixSlot (m : Nat) : Nat :=
  if m=1 then 424 else if m=16 then 1216 else 6328+72*(m-2)

def normalizeEntrySlot (i c : Nat) : Nat := 216*i+72*c

structure NormalizeTable (table : Addr) (s : State) (X Y Z : Nat → Fin fieldPrime) : Prop where
  canonical : ∀i,i<16 → ∀c,c<3 → wordsVal s.mem table (normalizeEntrySlot i c) 9<fieldPrime
  xValue : ∀i,i<16 → Fin.ofNat fieldPrime (wordsVal s.mem table (normalizeEntrySlot i 0) 9)=X i
  yValue : ∀i,i<16 → Fin.ofNat fieldPrime (wordsVal s.mem table (normalizeEntrySlot i 1) 9)=Y i
  zValue : ∀i,i<16 → Fin.ofNat fieldPrime (wordsVal s.mem table (normalizeEntrySlot i 2) 9)=Z i

structure NormalizeContext (workspace table : Addr) (W : Nat) (s : State) : Prop where
  workspace : Scr s workspace W
  readTable : Ptr s .x26 table 3456
  tableW : PtrW s .x26 table 3456

theorem TableWorkspaceApart.byte {workspace table : Addr} {W : Nat}
    (apart : TableWorkspaceApart workspace table W) {m m' : Mem}
    (outside : Outside workspace 0 W m m') {d : Nat} (hd : d<3456) :
    m' (off table d)=m (off table d) := outside _ (Or.inr (by simpa only [Nat.zero_add] using apart d hd))

theorem TableWorkspaceApart.word {workspace table : Addr} {W : Nat}
    (apart : TableWorkspaceApart workspace table W) {m m' : Mem}
    (outside : Outside workspace 0 W m m') {d : Nat} (hd : d+8≤3456) :
    word m' table d=word m table d := by
  apply Mem.readW_congr
  intro i hi
  have he : off table d+BitVec.ofNat 64 i=off table (d+i) := VG.Offset.add_ofNat_add_ofNat table d i
  rw [he]
  exact apart.byte outside (by omega_arith)

theorem TableWorkspaceApart.wordsVal {workspace table : Addr} {W : Nat}
    (apart : TableWorkspaceApart workspace table W) {m m' : Mem}
    (outside : Outside workspace 0 W m m') :
    ∀n d,d+8*n≤3456 → wordsVal m' table d n=wordsVal m table d n
  | 0,_,_ => rfl
  | n+1,d,hd => by
    simp only [VG.Proof.Mont.wordsVal]
    rw [apart.word outside (by omega_arith),apart.wordsVal outside n (d+8) (by omega_arith)]

theorem NormalizeTable.of_workspace_write {workspace table : Addr} {W : Nat} {s t : State}
    {X Y Z : Nat → Fin fieldPrime} (h : NormalizeTable table s X Y Z)
    (apart : TableWorkspaceApart workspace table W) (outside : Outside workspace 0 W s.mem t.mem) :
    NormalizeTable table t X Y Z := by
  have e (i c : Nat) (hi : i<16) (hc : c<3) :
      wordsVal t.mem table (normalizeEntrySlot i c) 9=wordsVal s.mem table (normalizeEntrySlot i c) 9 :=
    apart.wordsVal outside 9 _ (by dsimp only [normalizeEntrySlot]; omega_arith)
  exact ⟨fun i hi c hc => by rw [e i c hi hc]; exact h.canonical i hi c hc,
    fun i hi => by rw [e i 0 hi (by decide)]; exact h.xValue i hi,
    fun i hi => by rw [e i 1 hi (by decide)]; exact h.yValue i hi,
    fun i hi => by rw [e i 2 hi (by decide)]; exact h.zValue i hi⟩

end VG.Proof.Weierstrass.AArch64.P521Native
