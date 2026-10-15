module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64

theorem keygen_unstrip {P : KemLay} {s : State}
 (h : KeyGen.Pre P (stripConsts constants s)) : KeyGen.Pre P s := by
 refine ⟨?_,h.wr,h.args,h.sp16,h.wf⟩
 exact List.mem_of_mem_take h.rd

theorem kem_unstrip {P : KemLay} {L : Kem.Layout} {s : State}
 (h : Kem.Pre P L (stripConsts constants s)) : Kem.Pre P L s := by
 refine ⟨?_,h.wr,h.args,h.sp16,h.slots,h.scw,h.scl,h.wf⟩
 intro b hb
 exact List.mem_of_mem_take (h.rd b hb)

/-- Entry contracts keep the original mathematical postconditions and public
input relation; the extra hypotheses describe emitted immutable tables. -/
def entryContract (base : Contract isa) : Contract isa where
 pre s := base.pre (stripConsts constants s) ∧ ConstsOk constants 16 s
 post := base.post
 pub s t := base.pub s t ∧ ∀c∈constants,s.syms c.1=t.syms c.1

theorem entry_tables {base : Contract isa} {s : State}
 (h : (entryContract base).pre s) : Tables s := tables_of_consts h.2

theorem entry_keygen {P : KemLay} (hw : P.Wf) {s : State}
 (h : (entryContract (keyGenAArch64 P)).pre s) : KeyGen.Pre P s ∧ Tables s :=
 ⟨keygen_unstrip (KeyGen.pre_of hw h.1),entry_tables h⟩
end VG.Proof.MlKem.AArch64.Optimized
