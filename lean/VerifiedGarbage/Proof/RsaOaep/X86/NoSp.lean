module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaPss.X86.NoSp

/-!
# RSAES-OAEP on x86: the calls write `esp` only through their frames

The label's hash (`hashLabelT_noSp`) and MGF1's mask (`mgfX_noSp`) with
their table's indirect calls, and the branch on the digest length
(`byLen_noSp`), when every function they may reach writes `esp` only through
its frames.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (seqs countLoop)

variable (h g : OHash)

/-- The indirect calls of `ts`'s functions write `esp` only through their
frames when each of them does. -/
theorem icalls_noSp {i : Instr} (hi : Taint.clobbers i .esp = false) :
    ∀ {ts : List (String × Prog isa)}, (∀ q ∈ ts, NoSp q.2) → NoSp (Code.icalls i ts)
  | [], _ => NoSp.of_all rfl
  | (n, b) :: ts, h => fun x hx => by
    simp only [Code.icalls, instrs, List.mem_cons, List.mem_append] at hx
    rcases hx with (rfl | hx) | hx
    · exact hi
    · exact h (n, b) (List.mem_cons_self ..) x hx
    · exact icalls_noSp hi (fun q hq => h q (List.mem_cons_of_mem _ hq)) x hx

theorem tcall_noSp {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg} (h : ∀ q ∈ ts, NoSp q.2) :
    NoSp (tcall j ts rs) :=
  noSp_seq (fun x hx => by
    simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl) (noSp_frame rfl rfl (icalls_noSp rfl h))

/-- MGF1 through the table writes `esp` only through its calls' frames, when
each function the calls may reach does. -/
theorem mgfX_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2)
    {j : Nat} (hj : NoSp (.block (tabArgs j ++ Impl.RsaPss.X86.mgfInit) : Prog isa)) : NoSp (mgfXor f j) := by
  have i : NoSp (callInit f) := tcall_noSp hi
  have u : NoSp (callUpd f) := tcall_noSp hu
  have f' : NoSp (callFin f) := tcall_noSp hf
  simp only [mgfXor, mgfRound, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_loop
    | exact i | exact u | exact f' | exact hj
    | exact NoSp.of_all (by decide +kernel))

/-- The label's hash through its table, when each function the calls may
reach writes `esp` only through its frames. -/
theorem hashLabelT_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2)
    (hf : ∀ q ∈ f.fin, NoSp q.2) {j o : Nat} (hj : NoSp (.block (updLabArgs j) : Prog isa))
    (ho : NoSp (.block (finLabArgs j o) : Prog isa)) : NoSp (hashLabelT f j o) := by
  have i : NoSp (callInit f) := tcall_noSp hi
  have u : NoSp (callUpd f) := tcall_noSp hu
  have f' : NoSp (callFin f) := tcall_noSp hf
  simp only [hashLabelT, seqs]
  repeat' (first
    | with_reducible apply noSp_seq
    | exact i | exact u | exact f' | exact hj | exact ho
    | exact NoSp.of_all (by decide +kernel))

/-- The branch on the digest length, when each branch writes `esp` only
through its frames. -/
theorem byLen_noSp {b : Nat → Prog isa} : ∀ {ds : List Nat}, (∀ d ∈ ds, NoSp (b d)) → NoSp (byLen b ds)
  | [], _ => NoSp.of_all rfl
  | [d], h => h d (List.mem_singleton_self _)
  | d :: e :: ds, h => noSp_seq (fun x hx => by
      simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; rfl) (RsaPss.X86.noSp_ite (h d (List.mem_cons_self ..))
        (byLen_noSp fun d' hd' => h d' (List.mem_cons_of_mem _ hd')))

/-- The certificates of a digest length `byLen` branches on. -/
theorem lens_certs {d : Nat} (hd : d ∈ lens) : OCerts (ofLen d) :=
  certsOf (by simpa only [lens, List.mem_cons, List.not_mem_nil, or_false] using hd)

end VG.Proof.RsaOaep.X86
