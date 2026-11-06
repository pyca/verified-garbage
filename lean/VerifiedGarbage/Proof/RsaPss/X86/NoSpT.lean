module

public import VerifiedGarbage.Proof.RsaPss.X86.NoSp
public import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
public import VerifiedGarbage.Impl.RsaPss.X86.Table

/-!
# RSASSA-PSS on x86: the code through the tables keeps `esp`

`ctHashT_noSp`: the hash through the table of `MdHash` writes `esp` only
through the frames of its calls, when every function its calls may reach
does.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaOaep.X86 (tcall_noSp)
open VG.Impl.RsaOaep.X86 (tcall)

variable (h : PssHash)

theorem ctHashT_noSp {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {j : Nat} (hj : NoSp (.block (hTab j) : Prog isa)) : NoSp (ctHashT f h.H j) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := spOk h
  have ti : NoSp (tcall 0 f.init [.ebx]) := tcall_noSp hi
  have tc : NoSp (tcall 3 f.comp [.ebp, .ecx, .eax, .ebx]) := tcall_noSp hc
  have td : NoSp (tcall 4 f.dig [.ebx]) := tcall_noSp hd
  simp only [ctHashT, initPartT, lenPart, padPart, compLoopT, compBodyT, cmpT, outPartT, countLoop, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_loop
    | exact ti | exact tc | exact td | exact hj
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

end VG.Proof.RsaPss.X86
