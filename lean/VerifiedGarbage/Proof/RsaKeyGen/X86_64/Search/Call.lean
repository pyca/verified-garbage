module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Data
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedSafety
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedContract
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The search's call of the candidate

`candidateRun`: in a frame of its stack arguments, the candidate's eleven
arguments for the rest of the tape, and a call of `vg_rsa_keygen_candidate`
(for the backend's Miller–Rabin round). The call keeps the search's frame,
and leaves the candidate's status, its prime or zeros, and the octets it
read.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (codeWith kMainWith millerRabinWith mrRoundWith montSetup)

/-! ## The candidate's stack -/

theorem seqs_depth_le (N : Nat) (l : List (Prog isa)) :
    (seqs l).x86_64Depth ≤ N ↔ ∀ c ∈ l, c.x86_64Depth ≤ N := by
  induction l with
  | nil => simp [seqs, Code.x86_64Depth]
  | cons a l ih =>
    cases l with
    | nil => simp [seqs]
    | cons b l =>
      simp only [seqs, Code.x86_64Depth, Nat.max_le] at ih ⊢
      rw [ih]
      simp only [List.forall_mem_cons]

private theorem template_depth (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hm : ∀ o a b, (mul o a b).x86_64Depth ≤ 128) (hb : body.x86_64Depth ≤ 128) :
    (codeWith mul body).x86_64Depth ≤ 128 := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup
  simp only [seqs_depth_le, Code.x86_64Depth, Nat.max_le, List.forall_mem_append,
    List.forall_mem_cons]
  and_intros
  all_goals first | exact hm _ _ _ | exact hb | decide +kernel

/-- The candidate, as the search calls it. -/
def candidateCall (v : RoundImpl) : Prog isa :=
  .call (Spec.RsaKeyGen.candidateApi.name ++ v.suffix) (sharedCandidateCode v)

/-- Code without calls or frames uses no stack. -/
private theorem depth_noCalls : ∀ {c : Prog isa}, c.noCalls = true → c.x86_64Depth = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, depth_noCalls h.1, depth_noCalls h.2, Nat.max_self]
  | .ite _ t e, h => by
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, depth_noCalls h.1, depth_noCalls h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noCalls] at h
    simp only [Code.x86_64Depth, depth_noCalls h]
  | .call _ _, h => by simp only [Code.noCalls] at h; cases h
  | .frame .., h => by simp only [Code.noCalls] at h; cases h
  | .icall .., h => by simp only [Code.noCalls] at h; cases h

/-- Code whose calls can be inlined uses at most their return addresses. -/
private theorem depth_inlineOk : ∀ {c : Prog isa}, c.InlineOk = true → c.x86_64Depth ≤ 8
  | .block _, _ => Nat.zero_le _
  | .seq a b, h => by
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, Nat.max_le]
    exact ⟨depth_inlineOk h.1, depth_inlineOk h.2⟩
  | .ite _ t e, h => by
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, Nat.max_le]
    exact ⟨depth_inlineOk h.1, depth_inlineOk h.2⟩
  | .loop b _, h => by
    simp only [Code.InlineOk] at h
    simp only [Code.x86_64Depth]
    exact depth_inlineOk h
  | .call _ b, h => by
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.x86_64Depth, depth_noCalls h.1, Nat.zero_add, Nat.le_refl]
  | .frame .., h => by simp only [Code.InlineOk] at h; cases h
  | .icall .., h => by simp only [Code.InlineOk] at h; cases h

theorem mm_depth (v : RoundImpl) (o a b : Nat) : (v.mm o a b).x86_64Depth ≤ 128 :=
  Nat.le_trans (depth_inlineOk (v.mmOk o a b)) (by decide)

theorem sharedCandidate_depth (v : RoundImpl) : (sharedCandidateCode v).x86_64Depth ≤ 128 := by
  apply template_depth _ _ (mm_depth v)
  change (v.code.x86_64Depth + 8) ≤ 128
  have hd : v.code.x86_64Depth ≤ 120 := v.depth
  omega

/-! ## Where the candidate's buffers are -/

/-- The candidate's regions: its output, `used`, `e`, `p`, the rest of the
tape, the working space and its stack arguments; its return address, and the
stack below it the candidate uses. -/
abbrev rO (p : SearchPublic) : Region := ⟨p.op, p.len⟩
abbrev rU (p : SearchPublic) : Region := ⟨p.up, 8⟩
abbrev rE (p : SearchPublic) : Region := ⟨p.ep, p.elen⟩
abbrev rP (p : SearchPublic) : Region := ⟨p.pp, p.plen⟩
abbrev rR (p : SearchPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : SearchPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : SearchPublic) : Region := ⟨p.sp - BitVec.ofNat 64 200, 40⟩
abbrev rRet (p : SearchPublic) : Region := ⟨p.sp - BitVec.ofNat 64 208, 8⟩
abbrev rLow (p : SearchPublic) : Region := ⟨p.sp - BitVec.ofNat 64 336, 128⟩

structure CallFacts (p : SearchPublic) (used : Nat) : Prop where
  room : 336 ≤ p.sp.toNat
  top : p.sp.toNat + 56 ≤ 2 ^ 64
  oU : (rO p).Disjoint (rU p)
  oE : (rO p).Disjoint (rE p)
  oP : (rO p).Disjoint (rP p)
  oR : (rO p).Disjoint (rR p used)
  oS : (rO p).Disjoint (rS p)
  oA : (rO p).Disjoint (rA p)
  uE : (rU p).Disjoint (rE p)
  uP : (rU p).Disjoint (rP p)
  uR : (rU p).Disjoint (rR p used)
  uS : (rU p).Disjoint (rS p)
  uA : (rU p).Disjoint (rA p)
  eS : (rE p).Disjoint (rS p)
  pS : (rP p).Disjoint (rS p)
  rS' : (rR p used).Disjoint (rS p)
  sA : (rS p).Disjoint (rA p)
  ret : ∀ r ∈ [rO p, rU p, rE p, rP p, rR p used, rS p, rA p], (rRet p).Disjoint r
  low : ∀ r ∈ [rO p, rU p, rE p, rP p, rR p used, rS p, rA p], r.Disjoint (rLow p)
  nO : p.op.toNat + p.len ≤ 2 ^ 64
  nU : p.up.toNat + 8 ≤ 2 ^ 64
  nE : p.ep.toNat + p.elen ≤ 2 ^ 64
  nP : p.pp.toNat + p.plen ≤ 2 ^ 64
  nR : (p.rp + BitVec.ofNat 64 used).toNat + (p.randLen - used) ≤ 2 ^ 64
  nS : p.B.toNat + p.Z ≤ 2 ^ 64
  len : Spec.RsaKeyGen.primeLenValid p.len
  e1 : 1 ≤ p.elen
  e8 : p.elen ≤ 8
  plen : p.plen = 0 ∨ p.plen = p.len
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  len64 : p.len < 2 ^ 64
  plen64 : p.plen < 2 ^ 64
  rand64 : p.randLen < 2 ^ 64

private theorem sub_tape {r : Addr} {n used : Nat} (hu : used ≤ n) :
    Region.Sub ⟨r + BitVec.ofNat 64 used, n - used⟩ ⟨r, n⟩ :=
  Offset.sub_base r (by omega)

private theorem nowrap_tape {r : Addr} {n used : Nat} (hn : r.toNat + n ≤ 2 ^ 64) (hu : used ≤ n) :
    (r + BitVec.ofNat 64 used).toNat + (n - used) ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ n - used = 0 := by omega
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega
    · omega
  · rw [hz, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

private theorem disj_of_sep {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) :
    (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩ :=
  fun x hx hy => h x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

theorem rA_sub (p : SearchPublic) : Region.Sub (rA p) (below p.sp stackUse) :=
  Offset.sub_below _ (by decide) (by decide)

theorem rRet_sub (p : SearchPublic) : Region.Sub (rRet p) (below p.sp stackUse) :=
  Offset.sub_below _ (by decide) (by decide)

theorem rLow_sub (p : SearchPublic) : Region.Sub (rLow p) (below p.sp stackUse) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_args (p : SearchPublic) : (rRet p).Disjoint (rA p) :=
  disj_of_sep (Offset.sep_below p.sp 336 (a := 208) (n := 8) (b := 200) (k := 40) (by decide) (by decide)
    (Or.inl (by decide)) (by decide) (by decide))

theorem args_low (p : SearchPublic) : (rA p).Disjoint (rLow p) :=
  disj_of_sep (Offset.sep_below p.sp 336 (a := 200) (n := 40) (b := 336) (k := 128) (by decide) (by decide)
    (Or.inr (by decide)) (by decide) (by decide))

theorem SearchLive.callFacts {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) : CallFacts p used := by
  have hi := h.input
  obtain ⟨htop, hsp, _, _, hnw, hpw, hwr, hstk, hlen, he1, he8, hpl, hscr, -, -, -, -⟩ := hi.1
  have hu := h.used_le
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pou, pos, -⟩, ⟨pus, -⟩, -⟩ := hpw
  obtain ⟨⟨woe, wop, wor, -⟩, ⟨wue, wup, wur, -⟩, ⟨wse, wsp, wsr, -⟩, -⟩ := hwr
  obtain ⟨⟨-, bo⟩, ⟨-, bu⟩, ⟨-, bs⟩, -, ⟨-, be⟩, ⟨-, bp⟩, ⟨-, br⟩, -⟩ := hstk
  obtain ⟨no, nu, ns, -, ne, np, nr, -⟩ := hnw
  have hR : Region.Sub (rR (searchOfState original) used) (inRand original) := sub_tape hu
  have hA := rA_sub (searchOfState original)
  have hRet := rRet_sub (searchOfState original)
  have hLow := rLow_sub (searchOfState original)
  have hsp' : (searchOfState original).sp = original.gpr .rsp := rfl
  rw [hsp'] at hA hRet hLow
  refine ⟨hsp, htop, pou, woe, wop, wor.sub_right hR, pos, bo.symm.sub_right hA,
    wue, wup, wur.sub_right hR, pus, bu.symm.sub_right hA, wse.symm, wsp.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, ?_, ?_, no, nu, ne, np, nowrap_tape nr hu, ns, hlen, he1, he8, hpl, ?_, ?_,
    BitVec.isLt _, BitVec.isLt _, BitVec.isLt _⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bo.sub_left hRet
    · exact bu.sub_left hRet
    · exact be.sub_left hRet
    · exact bp.sub_left hRet
    · exact (br.sub_left hRet).sub_right hR
    · exact bs.sub_left hRet
    · exact ret_args _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (bo.sub_left hLow).symm
    · exact (bu.sub_left hLow).symm
    · exact (be.sub_left hLow).symm
    · exact (bp.sub_left hLow).symm
    · exact ((br.sub_left hLow).sub_right hR).symm
    · exact (bs.sub_left hLow).symm
    · exact args_low _
  · simp only [searchOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [searchOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]

end VG.Proof.RsaKeyGen.X86_64.Search
