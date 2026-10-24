module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MontgomeryOne
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorBasis
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorLoad
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StoreLiteral
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize entries zero and one from cached R² and the checked generator. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem regroup {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := ⟨WP.assoc',WP.assoc⟩

theorem precomputeInitial_ok (M : Mont) {s : State} {p : Parameters} {dom : Addr} {bs : List Byte}
 (field : FieldInitial p s) (space : ContextSpace p s)
 (generator : GeneratorSource p (dom+BitVec.ofNat 64 p.k) bs s) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=dom)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)) :
 WP isa (Precompute.initial M.mm) s fun t =>
 Basis p 1 t ∧ ContextSpace p t ∧ word t.mem p.B (8*sCtx)=p.ctx ∧
 word t.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N) ∧
 TablePrefix p 2 t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.initial
 simp only [seqs]
 rw [regroup,WP.seq_iff]
 refine WP.mono (field_initial_power M field) ?_
 rintro a ⟨powerA,frameA,restA⟩
 have inA := InScr.of_arrays frameA p.room (by simp)
 have sourceA := generator.after_inscr inA restA
 have spaceA := space.after restA
 have ctxA := (arrays_header frameA (by decide)).trans context
 have domA := (arrays_header frameA (by decide)).trans domain
 have lenA := (arrays_header frameA (by decide)).trans length
 have rowsA := (arrays_header frameA (by decide)).trans rows
 rw [regroup,WP.seq_iff]
 refine WP.mono (storeLiteral_ok powerA.good spaceA ctxA (by decide : 6<8) (by decide : 0<32)) ?_
 rintro b ⟨goodB,valueB,frameB,sameB,restB⟩
 have powerB := powerA.after_workspace goodB sameB
 have sourceB := sourceA.after_entry frameB (by decide) restB
 have spaceB := spaceA.after restB
 have ctxB := (workspace_header powerA.good sameB (by decide : sCtx<32)).trans ctxA
 have domB := (workspace_header powerA.good sameB (by decide : sDom<32)).trans domA
 have lenB := (workspace_header powerA.good sameB (by decide : sLen<32)).trans lenA
 have rowsB := (workspace_header powerA.good sameB (by decide : sRows<32)).trans rowsA
 have entryB : wv b.mem p.ctx (entryOffset p.w 0) p.w=entryValue p 0 := by
  unfold entryValue
  rw [valueB,powerA.value,VG.Proof.Rsa.FixedBaseComb.exponent_zero]
 have tableB : TablePrefix p 1 b :=
  TablePrefix.extend (fun j hj => by omega : TablePrefix p 0 a) (by decide) frameB entryB
 rw [regroup,WP.seq_iff]
 refine WP.mono (generatorLoad_ok goodB sourceB words positive size domB lenB) ?_
 rintro c ⟨goodC,generatorC,frameC,restC⟩
 have powerC := powerB.after_arrays goodC frameC (by decide) (by decide) (by decide) (by decide)
 have spaceC := spaceB.after restC
 have tableC := tableB.after_inscr spaceB (by decide) (InScr.of_arrays frameC p.room (by simp))
 have ctxC := (arrays_header frameC (by decide)).trans ctxB
 have rowsC := (arrays_header frameC (by decide)).trans rowsB
 rw [WP.seq_iff]
 refine WP.mono (generator_basis M powerC.toModState generatorC reduced) ?_
 rintro d ⟨basisD,frameD,restD⟩
 have spaceD := spaceC.after restD
 have tableD := tableC.after_inscr spaceC (by decide) (InScr.of_arrays frameD p.room (by simp))
 have ctxD := (arrays_header frameD (by decide)).trans ctxC
 have rowsD := (arrays_header frameD (by decide)).trans rowsC
 refine WP.mono (storeLiteral_ok basisD.good spaceD ctxD (by decide : 5<8) (by decide : 1<32)) ?_
 rintro t ⟨goodT,valueT,frameT,sameT,restT⟩
 have basisT := basisD.after_workspace goodT sameT
 have oneExponent : Spec.Rsa.FixedBaseComb.exponent p.N 1=1 := by
  simpa only [Nat.pow_zero,Nat.zero_mul] using VG.Proof.Rsa.FixedBaseComb.exponent_tooth p.N 0 (by decide)
 have entryT : wv t.mem p.ctx (entryOffset p.w 1) p.w=entryValue p 1 := by
  unfold entryValue
  rw [valueT,basisD.value,oneExponent]
 have tableT := tableD.extend (by decide : 1<32) frameT entryT
 have frames : BuildFrame p s.mem t.mem :=
  ((((BuildFrame.of_inscr inA).trans (BuildFrame.of_entry (by decide : 0<32) frameB)).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameC p.room (by simp)))).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameD p.room (by simp)))).trans
    (BuildFrame.of_entry (by decide : 1<32) frameT)
 exact ⟨basisT,spaceD.after restT,(workspace_header basisD.good sameT (by decide : sCtx<32)).trans ctxD,
  (workspace_header basisD.good sameT (by decide : sRows<32)).trans rowsD,tableT,frames,
  ((((restA.trans restB).trans restC).trans restD).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
