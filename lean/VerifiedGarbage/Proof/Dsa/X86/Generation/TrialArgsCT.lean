module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialCheck
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFrame
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Trial-table addresses are determined by the public frame and divisor index -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure TrialAddressPublic where
  base : Addr
  table : BitVec 32
  index : Nat

def TrialAddressAt (p : TrialAddressPublic) (s : State) : Prop :=
  TrialFrame s p.base ∧ trialSlot s.mem p.base 4 = p.table ∧
    trialSlot s.mem p.base 8 = BitVec.ofNat 32 p.index

def trialAddressCode : List Instr :=
  [.mov .eax (.mem (trialSp 8)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .eax (.mem (trialSp 4))]

theorem trialAddress_ok {p : TrialAddressPublic} {s : State} (R : TrialAddressAt p s) :
    WP isa (.block trialAddressCode) s fun t => TrialFrame t p.base ∧
      t.gpr .eax = p.table + BitVec.ofNat 32 (8 * p.index) := by
  unfold trialAddressCode
  refine wp_movS (by rw [R.1.read (by decide), R.2.2]) fun a sa _ =>
    wp_addS rfl fun b ab _ => wp_addS rfl fun c bc _ => wp_addS rfl fun d cd _ => ?_
  have F := (((R.1.keeps sa.keeps (by decide)).keeps ab.keeps (by decide)).keeps bc.keeps (by decide)).keeps cd.keeps (by decide)
  have mem : d.mem = s.mem := by rw [cd.mem, bc.mem, ab.mem, sa.mem]
  refine wp_addS (by rw [F.read (by decide), mem, R.2.1]) fun t dt _ => WP.block_nil ?_
  refine ⟨F.keeps dt.keeps (by decide), ?_⟩
  rw [dt.gpr, cd.gpr, bc.gpr, ab.gpr, sa.gpr]
  simp only [← BitVec.ofNat_add]
  rw [show p.index + p.index + (p.index + p.index) + (p.index + p.index + (p.index + p.index)) = 8 * p.index by omega,
    BitVec.add_comm]

theorem trialCheckArgs_ct (len : Nat) :
    RelCT isa (Two TrialAddressAt) (.block (trialCheckArgs len)) (fun _ _ => True) := by
  change RelCT isa (Two TrialAddressAt) (.block (trialAddressCode ++
    [.mov .esi (.mem (VG.Impl.Mont.X86.at_ .eax 0)), .mov .edi (.mem (VG.Impl.Mont.X86.at_ .eax 4)),
      .mov .ebp (.mem (trialSp 0)), .mov .ecx (.imm (BitVec.ofNat 32 (len / 2)))])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p t => TrialFrame t p.base ∧ t.gpr .eax = p.table + BitVec.ofNat 32 (8 * p.index))
    [.esp] ?_ (by taint_decide) (fun _ _ R => trialAddress_ok R)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.espNat.trans ht.1.espNat.symm)
  · refine two_taint [.esp, .eax] ?_ (hc := .block []) (by rfl)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.1.espNat.trans ht.1.espNat.symm)
    · exact hs.2.trans ht.2.symm
end VG.Proof.Dsa.X86.Generation
