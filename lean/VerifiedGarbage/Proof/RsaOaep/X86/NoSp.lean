module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `RsaPss.X86.NoSp`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on x86: code that keeps `esp`

`NoSp` of the pieces both functions share whose immediates depend on the
hash function (`spOk`, from `Certs.sp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

theorem noSp_ite {c : Cond} {t e : Prog isa} (ht : NoSp t) (he : NoSp e) : NoSp (.ite c t e) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [ht i h, he i h]

theorem noSp_append {l₁ l₂ : List Instr} (h₁ : NoSp (.block l₁ : Prog isa)) (h₂ : NoSp (.block l₂ : Prog isa)) :
    NoSp (.block (l₁ ++ l₂) : Prog isa) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [h₁ i h, h₂ i h]

theorem noSp_seq_inv {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp a ∧ NoSp b :=
  ⟨fun i hi => h i (List.mem_append_left _ hi), fun i hi => h i (List.mem_append_right _ hi)⟩

/-- The blocks whose immediates depend on the hash function, from `Certs.sp`. -/
structure SpOk (H : Impl.Pbkdf2.Md.X86.Hash) : Prop where
  lenSet : NoSp (.block (lenSet H) : Prog isa)
  clrB : NoSp (.block (clrArgs oLen H.B) : Prog isa)
  clrY : NoSp (.block (clrArgs oY H.B) : Prog isa)
  padArgs : NoSp (.block (padArgs H) : Prog isa)
  padBody : NoSp (.block (padBody H) : Prog isa)
  blkSet : NoSp (.block (blkSet H) : Prog isa)
  cmpSet : NoSp (.block (cmpSet H) : Prog isa)
  selSet : NoSp (.block (selSet H) : Prog isa)
  outPart : NoSp (outPart H)
  mgfSeed : NoSp (.block (mgfSeed H) : Prog isa)
  ctrSet : NoSp (.block (ctrSet H) : Prog isa)
  xorSet : NoSp (.block (xorSet H) : Prog isa)
  mgfNext : NoSp (.block (mgfNext H) : Prog isa)
  params : NoSp (.block (params H) : Prog isa)
  cpDig16 : NoSp (.block (cpDig H 16) : Prog isa)
  cpDig4 : NoSp (.block (cpDig H 4) : Prog isa)
  lenArgs19 : NoSp (.block (lenArgs H 19) : Prog isa)
  lenArgs8 : NoSp (.block (lenArgs H 8) : Prog isa)
  cpSalt : NoSp (.block (cpSalt H) : Prog isa)
  putH : NoSp (.block (putH H) : Prog isa)
  fxSalt : NoSp (.block (fxSalt H) : Prog isa)
  cpDb : NoSp (.block (cpDb H) : Prog isa)
  passSet : NoSp (.block (passSet H) : Prog isa)
  anyLen : NoSp (.block (anyLen H) : Prog isa)
  cmpArgs : NoSp (.block (cmpArgs H) : Prog isa)
  mgfArgs : NoSp (.block (mgfArgsT H) : Prog isa)

theorem spOk : SpOk h.H := by
  have hsp := h.certs.sp
  simp only [spBlocks, seqs] at hsp
  obtain ⟨s1, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s2, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s3, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s4, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s5, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s6, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s7, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s8, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s9, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s10, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s11, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s12, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s13, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s14, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s15, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s16, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s17, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s18, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s19, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s20, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s21, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s22, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s23, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s24, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s25, s26⟩ := noSp_seq_inv hsp
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22,
    s23, s24, s25, s26⟩

end VG.Proof.RsaPss.X86

end

end

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
