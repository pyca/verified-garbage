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

/-! ## The candidate's arguments -/

open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Search

/-- The candidate's stack arguments, in the call's frame. -/
def callValues (p : SearchPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.plen), (1, p.rp + BitVec.ofNat 64 used),
    (2, BitVec.ofNat 64 (p.randLen - used)), (3, p.B), (4, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : SearchPublic) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 20 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The candidate's arguments in registers. -/
def CallRegs (p : SearchPublic) (s : State) : Prop :=
  s.gpr .rdi = p.op ∧ s.gpr .rsi = BitVec.ofNat 64 p.len ∧ s.gpr .rdx = p.up ∧
    s.gpr .rcx = p.ep ∧ s.gpr .r8 = BitVec.ofNat 64 p.elen ∧ s.gpr .r9 = p.pp

theorem SearchLive.frame_ld {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) {t : State} (hw : t.wr = (allocated 40 s).wr) :
    ∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

/-- A read of the frame sees past a store to the call's frame below it. -/
theorem read_past_call (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 40)
    (he : e + 48 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 40 + BitVec.ofNat 64 d) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have hF : F + BitVec.ofNat 64 e = F - BitVec.ofNat 64 40 + BitVec.ofNat 64 (40 + e) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [hF]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := 40 + e) (n := 8) (e := d) (k := 8) (Or.inr (by omega))
    (by omega) (by omega)) (by decide)

theorem read_past_call0 (m : Mem) (F : Addr) (v : BitVec 64) {e : Nat} (he : e + 48 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 40) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have := read_past_call m F v (d := 0) (by decide) he
  rwa [BitVec.add_zero] at this

theorem search_arguments_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block arguments) (allocated 40 s) fun t =>
      CallRegs p t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 40) (callValues p used) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (allocated 40 s) t := by
  have hl := h.frame_ld (t := allocated 40 s) rfl
  have hsp : (allocated 40 s).gpr .rsp = p.F - BitVec.ofNat 64 40 := by rw [allocated_rsp, h.rsp]
  have hr12 : (allocated 40 s).gpr .r12 = p.F := by rw [allocated_reg _ _ _ (by decide), h.r12]
  have hF := h.input.F_toNat
  have hroom : 336 ≤ p.sp.toNat := h.input.room
  have haw : (allocated 40 s).wr = ⟨p.F - BitVec.ofNat 64 40, 40⟩ :: s.wr := by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 40, 40⟩ : Region) :: s.wr = _
    rw [h.rsp]
  have scr : Scr (allocated 40 s) (p.F - BitVec.ofNat 64 40) 40 :=
    Scr.of_mem (by rw [haw]; exact List.mem_cons_self ..) (by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 40).toNat = 40 from rfl]; omega)]
      have := h.input.top
      simp only [show (BitVec.ofNat 64 40).toNat = 40 from rfl]
      omega)
  have hs : ∀ d, d + 8 ≤ 40 → InRegions (allocated 40 s).wr (p.F - BitVec.ofNat 64 40 + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 40 s).wr (p.F - BitVec.ofNat 64 40) 8 := by
    simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used remaining) :
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv5 := hv 5 p.op (by simp [SearchPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  have hv7 := hv 7 p.up (by simp [SearchPublic.headers])
  have hv8 := hv 8 p.ep (by simp [SearchPublic.headers])
  have hv9 := hv 9 (BitVec.ofNat 64 p.elen) (by simp [SearchPublic.headers])
  have hv10 := hv 10 p.pp (by simp [SearchPublic.headers])
  have hv11 := hv 11 (BitVec.ofNat 64 p.plen) (by simp [SearchPublic.headers])
  have hv12 := hv 12 (p.rp + BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  have hv13 := hv 13 (BitVec.ofNat 64 (p.randLen - used)) (by simp [SearchPublic.headers])
  have hv14 := hv 14 p.B (by simp [SearchPublic.headers])
  have hv15 := hv 15 (BitVec.ofNat 64 (p.Z / 8)) (by simp [SearchPublic.headers])
  simp only [Nat.reduceMul] at hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t =>
    CallRegs p t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 40) (callValues p used)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold arguments CallRegs writeFrame callValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, allocated_mem,
    hsp, hr12, hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hl 72 (by decide), hl 80 (by decide), hl 88 (by decide), hl 96 (by decide), hl 104 (by decide),
    hl 112 (by decide), hl 120 (by decide), read_past_call, read_past_call0, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hs0, hs 8 (by decide), hs 16 (by decide), hs 24 (by decide), hs 32 (by decide)]

/-! ## The candidate's entry -/

/-- The regions the candidate reads, and those it writes. -/
def callReads (p : SearchPublic) (used : Nat) : List Region := [rE p, rP p, rR p used, rA p]
def callWrites (p : SearchPublic) : List Region := [rO p, rU p, rS p]

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : SearchPublic) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callReads p used) (callWrites p)

theorem F_40 (p : SearchPublic) : p.F - BitVec.ofNat 64 40 = p.sp - BitVec.ofNat 64 200 := by
  rw [SearchPublic.F, BitVec.sub_sub]; rfl

theorem call_rsp {p : SearchPublic} {used : Nat} {u : State} (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 200) :
    (callState p used u).gpr .rsp = p.sp - BitVec.ofNat 64 208 := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, hu, BitVec.sub_sub]
  rfl

theorem call_gpr {p : SearchPublic} {used : Nat} {u : State} {r : Reg} (hr : r ≠ .rsp) :
    (callState p used u).gpr r = u.gpr r := by
  simp only [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_argAddr {p : SearchPublic} {used : Nat} {u : State} (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 200)
    (j : Nat) : stackArgAddr (callState p used u) j = p.sp - BitVec.ofNat 64 200 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
  rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]

theorem call_arg {p : SearchPublic} {used : Nat} {s u : State} (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 200)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 40) (callValues p used)) (j : Nat) (hj : j < 5) :
    stackArg (callState p used u) j = frameValue (callValues p used) j
      (word s.mem (p.sp - BitVec.ofNat 64 200) (8 * j)) := by
  have e1 : p.sp - BitVec.ofNat 64 200 - 8 + BitVec.ofNat 64 (8 + 8 * j) =
      p.sp - BitVec.ofNat 64 200 + BitVec.ofNat 64 (8 * j) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      BitVec.sub_add_cancel]
  have sep : Mem.Sep (p.sp - BitVec.ofNat 64 200 + BitVec.ofNat 64 (8 * j)) (64 / 8)
      (p.sp - BitVec.ofNat 64 200 - 8) (64 / 8) := by
    have := Offset.sep (p.sp - BitVec.ofNat 64 200 - 8) (d := 8 + 8 * j) (n := 8) (e := 0) (k := 8)
      (.inr (by omega)) (by omega) (by decide)
    rw [e1, BitVec.add_zero] at this
    exact this
  unfold stackArg
  rw [call_argAddr hu, State.withRegions_mem, State.callEntry_mem, hu, Mem.readW_writeW_sep sep (by decide),
    hm, F_40]
  exact writeFrame_word _ _ _ (callValues_bound p used) j (by omega)

/-- The candidate's precondition at its entry. -/
theorem call_cand_pre {p : SearchPublic} {used : Nat} {s u : State} (hf : CallFacts p used)
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 200) (ha : CallRegs p u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 40) (callValues p used)) :
    sharedCandContract.pre (callState p used u) := by
  have a0 : arg (callState p used u) 0 = BitVec.ofNat 64 p.plen := by
    show stackArg _ 0 = _
    rw [call_arg hu hm 0 (by decide)]; rfl
  have a1 : arg (callState p used u) 1 = p.rp + BitVec.ofNat 64 used := by
    show stackArg _ 1 = _
    rw [call_arg hu hm 1 (by decide)]; rfl
  have a2 : arg (callState p used u) 2 = BitVec.ofNat 64 (p.randLen - used) := by
    show stackArg _ 2 = _
    rw [call_arg hu hm 2 (by decide)]; rfl
  have a3 : arg (callState p used u) 3 = p.B := by
    show stackArg _ 3 = _
    rw [call_arg hu hm 3 (by decide)]; rfl
  have a4 : arg (callState p used u) 4 = BitVec.ofNat 64 (p.Z / 8) := by
    show stackArg _ 4 = _
    rw [call_arg hu hm 4 (by decide)]; rfl
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have t8 : (BitVec.ofNat 64 p.elen).toNat = p.elen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.e8; omega)]
  have tl : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have tp : (BitVec.ofNat 64 p.plen).toNat = p.plen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.plen64]
  have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.rand64; omega)]
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.nS; omega)]; exact hf.z8
  have tz' : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.nS; omega)]
  have hsp := call_rsp (used := used) hu
  have h208 : (p.sp - BitVec.ofNat 64 208).toNat = p.sp.toNat - 208 := by
    have := hf.room
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 208).toNat = 208 from rfl]; omega),
      show (BitVec.ofNat 64 208).toNat = 208 from rfl]
  have hargs : stackArgAddr (callState p used u) 0 = p.sp - BitVec.ofNat 64 200 := by
    rw [call_argAddr hu, Nat.mul_zero, BitVec.add_zero]
  have hlow : below (p.sp - BitVec.ofNat 64 208) 128 = rLow p := by
    simp only [below, rLow, BitVec.sub_sub]; rfl
  have hret := hf.ret
  have hlo := hf.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret hlo
  obtain ⟨rO', rU', rE', rP', rR', rS', rA'⟩ := hret
  obtain ⟨lO, lU, lE, lP, lR, lS, lA⟩ := hlo
  refine ⟨?_, ?_⟩
  · simp only [candPre, args, ret, State.withRegions_rd, State.withRegions_wr, hsp, hargs,
      call_gpr (show Reg.rdi ≠ .rsp by decide), call_gpr (show Reg.rsi ≠ .rsp by decide),
      call_gpr (show Reg.rdx ≠ .rsp by decide), call_gpr (show Reg.rcx ≠ .rsp by decide),
      call_gpr (show Reg.r8 ≠ .rsp by decide), call_gpr (show Reg.r9 ≠ .rsp by decide),
      hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, t8, tl, tp, tr, tz', hf.z8, callReads, callWrites]
    have hsp' : (p.sp - BitVec.ofNat 64 208).toNat + 48 ≤ 2 ^ 64 := by
      rw [h208]; have := hf.top; omega
    exact ⟨hsp', by trivial, by trivial, hf.oU, hf.oE, hf.oP, hf.oR, hf.oS, hf.oA, hf.uE, hf.uP, hf.uR, hf.uS, hf.uA,
      hf.eS, hf.pS, hf.rS', hf.sA, rO', rU', rE', rP', rR', rS', rA', hf.nO, hf.nU, hf.nE, hf.nP, hf.nR,
      hf.nS, hf.len, hf.e1, hf.e8, hf.plen, hf.scratch⟩
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hsp, h208]; have := hf.room; omega
    · rw [hsp, hlow, a3, a4, tz]; exact lS
    · rfl
    · intro r hr
      rw [hsp, hlow]
      simp only [State.withRegions_rd, State.withRegions_wr, callReads, callWrites, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [lE, lP, lR, lA, lO, lU, lS]

end VG.Proof.RsaKeyGen.X86_64.Search
