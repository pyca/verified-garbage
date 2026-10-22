module

public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase

/-! # Parameter generation never writes ESP outside its frames -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem checked {c : Prog isa} (H : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [H i hi]
  rfl

theorem nosp_seq {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := fun i hi =>
  (List.mem_append.mp hi).elim (A i) (B i)

theorem nosp_seqs {l : List (Prog isa)} (h : ∀ p ∈ l, NoSp p) : NoSp (seqs l) := by
  induction l with
  | nil => exact NoSp.of_all rfl
  | cons p ps ih =>
    cases ps with
    | nil => exact h p List.mem_cons_self
    | cons q qs =>
      exact nosp_seq (h p List.mem_cons_self) (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem storeW_mem {dst : Reg} {o : Nat} {xs : List Byte} {n : Nat} {i : Instr}
    (h : i ∈ Impl.Pbkdf2.Md.X86.storeW dst o xs n) : Taint.clobbers i .esp = false := by
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> rfl

theorem hash_noSp (H : Impl.Pbkdf2.Md.X86.Hash) (iv : List (BitVec 32)) (n dst : Nat) (hc : NoSp H.compC)
    (hout : ∀ i ∈ H.out, Taint.clobbers i .esp = false) : NoSp (hash H iv n dst) := by
  unfold VG.Impl.Dsa.X86.Generation.hash
  simp only [seqs]
  refine nosp_seq ?_ (nosp_seq ?_ ?_)
  · intro i hi
    simp only [instrs, ivStore, scr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (((((rfl | rfl) | h) | h) | (rfl | rfl)) | (rfl | rfl))
    all_goals first | rfl | exact storeW_mem h
  · apply NoSp.of_all
    simp only [Impl.MdStream.X86.compressAt, Impl.MdStream.X86.compressWith, Code.allInstrs, checked hc]
    rfl
  · intro i hi
    simp only [instrs, scr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | (rfl | rfl)) | h
    all_goals first | rfl | exact hout i h

theorem test_noSp (name : String) {callee : Prog isa} (C : NoSp callee) : NoSp (test name callee) := by
  apply NoSp.of_all
  simp only [test, seqs, Code.allInstrs, checked C]
  rfl

theorem check_call_noSp (pLen qLen chkWords : Nat) (name : String) {callee : Prog isa} (C : NoSp callee) :
    NoSp (check pLen qLen chkWords name callee) := by
  apply NoSp.of_all
  simp only [check, seqs, Code.allInstrs, checked C]
  rfl

theorem pArith_noSp (pLen qLen : Nat) : NoSp (pArith pLen qLen) := by
  apply NoSp.of_all
  simp only [pArith, seqs, Code.allInstrs, checked (VG.Proof.RsaKeyGen.X86.KeyNoSp.constant _ _ _)]
  rfl

theorem pow_noSp (n e : Nat) : NoSp (Impl.Dsa.X86.Pow.call n e) := by
  apply NoSp.of_all
  simp only [Impl.Dsa.X86.Pow.call, Code.allInstrs, checked (Proof.Dsa.X86.Pow.body_noSp n e)]
  rfl

namespace Geo
variable {g : Geo} (hc : NoSp g.H.compC) (hout : ∀ i ∈ g.H.out, Taint.clobbers i .esp = false)
  (hq : NoSp g.qCode) (hp : NoSp g.pCode) (hk : NoSp g.checkCode)
include hc hout

omit hc hout in
theorem seedIn_noSp' (g : Geo) : NoSp g.seedIn := NoSp.of_all (by rfl)

theorem qPart_noSp (hq : NoSp g.qCode) : NoSp g.qPart := by
  apply NoSp.of_all
  simp only [Geo.qPart, seqs, Code.allInstrs, checked (seedIn_noSp' g), checked (hash_noSp _ _ _ _ hc hout),
    checked (test_noSp _ hq)]
  rfl

theorem pHash_noSp (j : Nat) : NoSp (g.pHash j) := by
  apply NoSp.of_all
  simp only [Geo.pHash, seqs, Code.allInstrs, checked (seedIn_noSp' g), checked (hash_noSp _ _ _ _ hc hout)]
  rfl

theorem pX_noSp : NoSp g.pX := by
  unfold Geo.pX
  refine nosp_seqs fun p hp => ?_
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with ⟨j, _, rfl⟩ | rfl
  · exact pHash_noSp hc hout j
  · exact NoSp.of_all rfl

theorem pAttempt_noSp (hp : NoSp g.pCode) : NoSp g.pAttempt := by
  apply NoSp.of_all
  simp only [Geo.pAttempt, seqs, Code.allInstrs, checked (pX_noSp hc hout), checked (pArith_noSp _ _),
    checked (test_noSp _ hp)]
  rfl

theorem pPart_noSp (hp : NoSp g.pCode) : NoSp g.pPart := by
  apply NoSp.of_all
  simp only [Geo.pPart, seqs, Code.allInstrs, checked (pAttempt_noSp hc hout hp)]
  rfl

omit hc hout in
theorem gStep_noSp (g : Geo) : NoSp g.gStep := by
  apply NoSp.of_all
  simp only [Geo.gStep, seqs, Code.allInstrs, checked (pow_noSp _ _)]
  rfl

omit hc hout in
theorem gPart_noSp (g : Geo) : NoSp g.gPart := by
  apply NoSp.of_all
  simp only [Geo.gPart, seqs, Code.allInstrs, checked (gStep_noSp g)]
  rfl

theorem attempt_noSp (hq : NoSp g.qCode) (hp : NoSp g.pCode) (hk : NoSp g.checkCode) : NoSp g.attempt := by
  apply NoSp.of_all
  simp only [Geo.attempt, seqs, Code.allInstrs, checked (qPart_noSp hc hout hq), checked (pPart_noSp hc hout hp),
    checked (gPart_noSp g), checked (check_call_noSp _ _ _ _ hk)]
  rfl

theorem generate_noSp (hq : NoSp g.qCode) (hp : NoSp g.pCode) (hk : NoSp g.checkCode) : NoSp g.generate := by
  apply NoSp.of_all
  simp only [Geo.generate, Geo.search, Geo.finish, seqs, Code.allInstrs,
    checked (attempt_noSp hc hout hq hp hk)]
  rfl

end Geo

end VG.Proof.Dsa.X86.Generation
