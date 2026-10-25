module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Frame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State

/-! The prefix leaves stack arguments, source bytes, and the read-only table intact. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

structure Tracking (s t : State) : Prop where
  stack : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem

theorem Tracking.args {s t : State} (track : Tracking s t) (h : contract.pre s) :
    ∀ i < 5, arg t i = arg s i := args_frame h track.stack track.frame

theorem Tracking.domain_eq {s t : State} (track : Tracking s t) (h : contract.pre s) : domain t = domain s :=
  domain_frame h (track.args h) track.frame

theorem Tracking.after {s t u : State} {rs : List Reg} (track : Tracking s t)
    (mem : u.mem = t.mem) (rest : Keeps rs t u) (noSp : .esp ∉ rs) : Tracking s u :=
  ⟨(rest.1 _ noSp).trans track.stack, rest.2.1.trans track.rd, rest.2.2.trans track.wr,
    by rw [mem]; exact track.frame⟩

theorem Tracking.pre {s t : State} (track : Tracking s t) (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi 172).pre (plain t) := by
  have old := (pre_plain h).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes,
    stackBelow] at old ⊢
  simp only [plain_arg, plain_argAddr] at old ⊢
  rw [track.stack, track.rd, track.wr, track.args h 0 (by decide), track.args h 1 (by decide),
    track.args h 2 (by decide), track.args h 3 (by decide), track.args h 4 (by decide)]
  have addr : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [track.stack]
  rw [addr]
  exact old

private theorem singleton_regions {name : String} {words : List (BitVec 64)} {s : State} {st : Nat}
    (h : ConstsOk [(name, words)] st s) :
    (∀ r ∈ s.wr, (⟨symAddr s name, 8 * words.length⟩ : Region).Disjoint r) ∧
    (∀ r ∈ abi.reserved st s, (⟨symAddr s name, 8 * words.length⟩ : Region).Disjoint r) :=
  (h.2.2 ⟨symAddr s name, 8 * words.length⟩ List.mem_cons_self).2

theorem table_separate {s : State} (h : contract.pre s) :
    ∀ r ∈ writes s, (⟨symAddr s tableSym, 17744⟩ : Region).Disjoint r := by
  have regions := singleton_regions (pre_plain h).2
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at regions
  intro r hr
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact regions.1 _ (by
      have wr := (geometry h).wr
      change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
      rw [wr]; exact List.mem_cons_self)
  · have full : (⟨symAddr s tableSym, 17744⟩ : Region).Disjoint
        ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := regions.2 _ (by
      change _ ∈ ([⟨(s.gpr .esp).setWidth 64, 4⟩] ++ stackBelow ((s.gpr .esp).setWidth 64) 172)
      simp only [stackBelow, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr trivial)
    exact full.sub_right (symbol_sub h)

theorem Tracking.table {s t : State} (track : Tracking s t) (h : contract.pre s) :
    TableAt (symAddr s tableSym) groups t := by
  apply tableOfBytes groups _ t
  · rw [track.rd, track.wr]; exact consts_read (pre_plain h).2
  · rw [VG.Proof.Rsa.rsa_bytes_frame track.frame
      (by change tableBytes.length < 2 ^ 64; rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]; decide)
      (by change ∀ r ∈ writes s, (⟨symAddr s tableSym, tableBytes.length⟩ : Region).Disjoint r
          rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]; exact table_separate h)]
    exact consts_bytes (pre_plain h).2
  · change tableBytes.length ≤ 17744
    rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]
  · intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ffdh.X86.VettedValidation
