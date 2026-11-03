module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaPss.X86.NoSp

/-!
# RSAES-OAEP on x86: the calls write `esp` only through their frames

The direct calls of the streaming functions (`hInit_noSp`, …) and the
label's hash (`hashLabel_noSp`), for both functions' bodies, and MGF1's mask
with its table's indirect calls (`mgfX_noSp`), when every function they may
reach writes `esp` only through its frames.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (seqs countLoop)

variable (h g : OHash)

theorem hInit_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (hG : Proof.Pbkdf2.Stream.X86.HashOK G) :
    NoSp (hInit G) := noSp_pushCall hG.initSp
theorem hUpd_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (hG : Proof.Pbkdf2.Stream.X86.HashOK G) :
    NoSp (hUpd G) := noSp_pushCall hG.updSp
theorem hFin_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (hG : Proof.Pbkdf2.Stream.X86.HashOK G) :
    NoSp (hFin G) := noSp_pushCall hG.finSp

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

theorem hashLabel_noSp {j o : Nat} (hj : NoSp (.block (updLabArgs j) : Prog isa))
    (ho : NoSp (.block (finLabArgs j o) : Prog isa)) : NoSp (hashLabel h.H j o) := by
  have i := hInit_noSp h.H h.ok
  have u := hUpd_noSp h.H h.ok
  have f := hFin_noSp h.H h.ok
  simp only [hashLabel, seqs]
  repeat' (first
    | with_reducible apply noSp_seq
    | exact i | exact u | exact f | exact hj | exact ho
    | exact NoSp.of_all (by decide +kernel))

end VG.Proof.RsaOaep.X86
