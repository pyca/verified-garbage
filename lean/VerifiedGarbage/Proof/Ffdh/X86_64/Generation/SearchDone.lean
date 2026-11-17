module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState

/-! ### `Ffdh.X86_64.Generation.SearchMemory`, which this module and modules that import it used -/

section

/-! # Output permissions relative to the persistent generation controller -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem SearchInput.length_lt {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.k < 2 ^ 64 := by
  cases h.2
  exact (original.gpr .rsi).isLt

theorem SearchInput.tape_lt {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.rand.length < 2 ^ 64 := by
  cases h.2
  simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
    List.length_map, List.length_range] using (stackArg original 0).isLt

theorem SearchInput.width_bounds {p : SearchPublic} {original : State} (h : SearchInput p original) :
    64 ≤ p.c.k ∧ p.c.k ≤ 1024 := by
  have hc := pcCtx_of h.1.1
  cases h.2
  change 64 ≤ (original.gpr .rsi).toNat ∧ (original.gpr .rsi).toNat ≤ 1024
  have hbits1 : 512 ≤ (original.gpr .rcx).toNat := hc.bits1
  have hbits2 : (original.gpr .rcx).toNat ≤ 8192 := hc.bits2
  have hlen : (original.gpr .rsi).toNat = ((original.gpr .rcx).toNat + 7) / 8 := hc.len
  omega_using [hbits1, hbits2, hlen]

theorem SearchInput.width_bits {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.k = (p.c.bits + 7) / 8 := by
  cases h.2
  exact (pcCtx_of h.1.1).len

theorem SearchInput.entropy_bound {p : SearchPublic} {original : State} (h : SearchInput p original) :
    Spec.Ffdh.parameterEntropy p.c.bits ≤ 33555456 := by
  have hk := h.width_bounds.2
  rw [Spec.Ffdh.parameterEntropy, ← h.width_bits]
  omega_using [hk]

theorem SearchInput.tape_bound {p : SearchPublic} {original : State} (h : SearchInput p original) :
    p.c.rand.length ≤ Spec.Ffdh.parameterEntropy p.c.bits := by
  cases h.2
  simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
    List.length_map, List.length_range] using h.1.2.2.2.2.2.2.2.2.2.2.2.2

theorem SearchInput.output {p : SearchPublic} {original s : State} (h : SearchInput p original)
    (hw : s.wr = original.wr) : OutOk s p.control 128 p.c.op p.c.k := by
  have hk := h.length_lt
  cases h.2
  change OutOk s (stackArg original 3) 128 (original.gpr .rdi) (original.gpr .rsi).toNat
  have hd : (inputControl original).Disjoint ⟨original.gpr .rdi, (original.gpr .rsi).toNat⟩ :=
    h.1.2.2.2.2.2.1 _ (by simp [inputBuffers])
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [hw, h.1.2.2.2.1]
    exact ⟨⟨original.gpr .rdi, (original.gpr .rsi).toNat⟩, by simp [inputBuffers],
      contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  · intro i hi
    exact out_scr hd.symm (contains_byte _ (by omega_using [hi]) (by omega_using [hi, hk]))

theorem SearchInput.used_memory {p : SearchPublic} {original s : State} (h : SearchInput p original)
    (hw : s.wr = original.wr) : Scr s p.c.up 8 := by
  cases h.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hu, _⟩ := h.1.1
  exact Scr.of_mem (by rw [hw, h.1.2.2.2.1]; simp [inputBuffers, searchOfState, SearchPublic.c, candidateOfState]) hu

theorem SearchInput.output_used_disjoint {p : SearchPublic} {original : State} (h : SearchInput p original) :
    (⟨p.c.op, p.c.k⟩ : Region).Disjoint ⟨p.c.up, 8⟩ := by
  cases h.2
  obtain ⟨_, _, _, _, hd, _⟩ := h.1.1
  exact hd

theorem SearchInput.control_used_disjoint {p : SearchPublic} {original : State} (h : SearchInput p original) :
    (⟨p.control, 128⟩ : Region).Disjoint ⟨p.c.up, 8⟩ := by
  cases h.2
  exact h.1.2.2.2.2.2.1 _ (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Completed native searches return their result and exact byte consumption -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchOutput (p : SearchPublic) (result : Spec.Ffdh.ParameterSearchResult) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m p.c.op p.c.k = match result with
    | .accepted n _ => Spec.Rsa.i2osp n p.c.k
    | _ => List.replicate p.c.k 0

structure SearchDone (p : SearchPublic) (original : State) (result : Spec.Ffdh.ParameterSearchResult)
    (s : State) : Prop where
  input : SearchInput p original
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  rsp : s.gpr .rsp = p.c.sp
  r12 : s.gpr .r12 = p.control
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → s.gpr r = original.gpr r
  savedR12 : word s.mem p.control 32 = original.gpr .r12
  outPtr : word s.mem p.control 40 = p.c.op
  usedPtr : word s.mem p.control 56 = p.c.up
  used : word s.mem p.control 96 = BitVec.ofNat 64 result.used
  status : word s.mem p.control 112 = BitVec.ofNat 64 result.status
  policy : Spec.Rsa.wordsAt s.mem p.control 4 =
    [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
      BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 (Proof.Ffdh.requested p.c.bits result)]
  output : SearchOutput p result s.mem

theorem done_of_live {p : SearchPublic} {original s : State} {used remaining : Nat}
    {result : Spec.Ffdh.ParameterSearchResult} (h : SearchLive p original used remaining s)
    (hu : result.used = used) (hr : result.remaining = remaining)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 result.status)
    (hq : word s.mem p.control 24 = BitVec.ofNat 64 (Proof.Ffdh.requested p.c.bits result))
    (ho : SearchOutput p result s.mem) : SearchDone p original result s := by
  refine ⟨h.input, h.rd, h.wr, h.rsp, h.r12, h.saved, h.savedR12,
    h.headers (5, p.c.op) (by simp [SearchPublic.headers]),
    h.headers (7, p.c.up) (by simp [SearchPublic.headers]), ?_, hs, ?_, ho⟩
  · rw [hu]
    exact h.headers (12, BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  · have h0 : word s.mem p.control 0 = BitVec.ofNat 64 remaining :=
      h.headers (0, BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
    have h1 : word s.mem p.control 8 = BitVec.ofNat 64 p.c.k :=
      h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
    have h2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
      h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
    change [word s.mem p.control 0, word s.mem p.control 8, word s.mem p.control 16, word s.mem p.control 24] = _
    rw [h0, h1, h2, hq, hr]

theorem SearchDone.keep {p : SearchPublic} {original s t : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) {rs : List Reg} (k : Keep rs s t) (hm : t.mem = s.mem)
    (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) : SearchDone p original result t := by
  refine ⟨h.input, k.2.1.trans h.rd, k.2.2.trans h.wr,
    (k.gpr (hregs .rsp (by decide))).trans h.rsp, (k.gpr (hregs .r12 (by decide))).trans h.r12,
    fun reg hr hn => (k.gpr (hregs reg hr)).trans (h.saved reg hr hn), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  · exact h.savedR12
  · exact h.outPtr
  · exact h.usedPtr
  · exact h.used
  · exact h.status
  · exact h.policy
  · exact h.output

theorem search_finish_values {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block finish) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 result.status ∧ t.gpr .r12 = original.gpr .r12 ∧
      t.mem = s.mem.writeW p.c.up (BitVec.ofNat 64 result.used) ∧
      Keep [.rax, .rcx, .rdx, .r12] s t := by
  have scr := h.input.control_scr h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hup : InRegions s.wr p.c.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_memory h.wr).st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r12] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 result.status ∧ t.gpr .r12 = original.gpr .r12 ∧
    t.mem = s.mem.writeW p.c.up (BitVec.ofNat 64 result.used)) ?_ rfl)
    fun _ ⟨⟨ha, hr, hm⟩, k⟩ => ⟨ha, hr, hm, k⟩
  unfold finish
  xrun [State.ea, field, off, h.r12, h.usedPtr, h.used, h.status, h.savedR12,
    BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hup,
    hl 56 (by decide), hl 96 (by decide), hl 112 (by decide), hl 32 (by decide)]

end VG.Proof.Ffdh.X86_64.Generation
