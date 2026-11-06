module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.SearchArgs
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The controller's call of the prime search

The search's regions, from the controller's: its output and the other prime in
the key's buffer, `used`, the working space, the state's first four words,
its exponent in the state's last, the rest of the tape, and its stack
arguments, return address and stack below the controller's frame.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen

/-! ## The search's regions -/

abbrev rO (p : GenPublic) (st : KeyProgress) : Region := ⟨outOf p st, p.L⟩
abbrev rU (p : GenPublic) : Region := ⟨p.up, 8⟩
abbrev rE (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 48, 8⟩
abbrev rP (p : GenPublic) (st : KeyProgress) : Region := ⟨p.slot 4, plenOf p st⟩
abbrev rR (p : GenPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.randLen - used⟩
abbrev rS (p : GenPublic) : Region := ⟨p.B, p.Z⟩
abbrev rT (p : GenPublic) : Region := ⟨p.stp, 32⟩
abbrev rA (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 208, 48⟩
abbrev rRet (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 216, 8⟩
abbrev rLow (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 552, 336⟩

/-- The controller's regions. -/
abbrev cK (p : GenPublic) : Region := ⟨p.kp, 9 * p.L⟩
abbrev cS (p : GenPublic) : Region := ⟨p.stp, 56⟩
abbrev cR (p : GenPublic) : Region := ⟨p.rp, p.randLen⟩
abbrev cStack (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 552, 552⟩

theorem disj_of_sep {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) :
    (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩ :=
  fun x hx hy => h x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

/-- What the controller's precondition says of its regions. -/
structure CFacts (p : GenPublic) : Prop where
  room : 552 ≤ p.sp.toNat
  top : p.sp.toNat + 24 ≤ 2 ^ 64
  kU : (cK p).Disjoint (rU p)
  kS : (cK p).Disjoint (rS p)
  kT : (cK p).Disjoint (cS p)
  uS : (rU p).Disjoint (rS p)
  uT : (rU p).Disjoint (cS p)
  sT : (rS p).Disjoint (cS p)
  kR : (cK p).Disjoint (cR p)
  uR : (rU p).Disjoint (cR p)
  sR : (rS p).Disjoint (cR p)
  tR : (cS p).Disjoint (cR p)
  stack : ∀ r ∈ [cK p, rU p, rS p, cS p, cR p], r.Disjoint (cStack p)
  nK : p.kp.toNat + 9 * p.L ≤ 2 ^ 64
  nU : p.up.toNat + 8 ≤ 2 ^ 64
  nS : p.B.toNat + p.Z ≤ 2 ^ 64
  nT : p.stp.toNat + 56 ≤ 2 ^ 64
  nR : p.rp.toNat + p.randLen ≤ 2 ^ 64
  len : primeLenValid p.L
  scratch : Spec.Rsa.scratchWords (2 * p.L) ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  rand_cap : p.randLen ≤ primeEntropy p.L
  rand64 : p.randLen < 2 ^ 64
  z64 : p.Z / 8 < 2 ^ 64

theorem GenInput.cfacts {p : GenPublic} {s : State} (h : GenInput p s) : CFacts p := by
  obtain ⟨htop, hsp, _, _, hnw, hpw, hwr, hstk, hlen, -, hscr, -, -, -, hcap⟩ := h.1
  cases h.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pku, pks, pkt⟩, ⟨pus, put⟩, pst, -⟩ := hpw
  obtain ⟨⟨wkr, -⟩, ⟨wur, -⟩, ⟨wsr, -⟩, ⟨wtr, -⟩⟩ := hwr
  obtain ⟨⟨-, bk⟩, ⟨-, bu⟩, ⟨-, bs⟩, ⟨-, bt⟩, ⟨-, br⟩, -⟩ := hstk
  obtain ⟨nk, nu, ns, nt, nr, -⟩ := hnw
  have hk : inKey s = ⟨s.gpr .rdi, 9 * genLen s⟩ := by
    simp only [inKey, h.1.2.2.2.2.2.2.2.2.2.1]
  rw [hk] at pku pks pkt wkr bk nk
  refine ⟨hsp, htop, pku, pks, pkt, pus, put, pst, wkr, wur, wsr, wtr, ?_, nk, nu, ns, nt, nr, hlen,
    ?_, ?_, hcap, BitVec.isLt _, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [bk.symm, bu.symm, bs.symm, bt.symm, br.symm]
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]; exact hscr
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]
  · simp only [genOfState, Nat.mul_div_cancel _ (show 0 < 8 by decide)]; exact BitVec.isLt _

/-! ## Sub-regions and disjointness -/

section

variable {p : GenPublic} {used : Nat} {st : KeyProgress}

theorem plen_le : plenOf p st ≤ p.L := by unfold plenOf; split <;> omega

theorem rO_sub (hf : CFacts p) : Region.Sub (rO p st) (cK p) := by
  have := hf.len.1
  unfold rO outOf
  split
  · exact slot_sub _ (by omega)
  · exact slot_sub _ (by omega)

theorem rP_sub : Region.Sub (rP p st) (cK p) := slot_sub _ (by have := plen_le (p := p) (st := st); omega)

theorem rR_sub (hu : used ≤ p.randLen) : Region.Sub (rR p used) (cR p) := Offset.sub_base _ (by omega)

theorem rT_sub : Region.Sub (rT p) (cS p) := Region.sub_prefix (by decide)

theorem rE_sub : Region.Sub (rE p) (cS p) := Offset.sub_base _ (by decide)

theorem rA_sub : Region.Sub (rA p) (cStack p) := Offset.sub_below _ (by decide) (by decide)

theorem rRet_sub : Region.Sub (rRet p) (cStack p) := Offset.sub_below _ (by decide) (by decide)

theorem rLow_sub : Region.Sub (rLow p) (cStack p) := Region.sub_prefix (by decide)

theorem oP (hf : CFacts p) : (rO p st).Disjoint (rP p st) := by
  have := hf.len.1
  unfold rO rP outOf plenOf
  split
  · intro x _ hy; simp only [Region.Contains] at hy; omega
  · exact slot_disjoint _ (.inr (by omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)

theorem tE : (rT p).Disjoint (rE p) := by
  have := Offset.sep p.stp (d := 0) (n := 32) (e := 48) (k := 8) (.inl (by decide)) (by decide) (by decide)
  rw [BitVec.add_zero] at this
  exact disj_of_sep this

theorem ret_args : (rRet p).Disjoint (rA p) :=
  disj_of_sep (Offset.sep_below p.sp 552 (a := 216) (n := 8) (b := 208) (k := 48) (by decide) (by decide)
    (Or.inl (by decide)) (by decide) (by decide))

theorem args_low : (rA p).Disjoint (rLow p) :=
  disj_of_sep (Offset.sep_below p.sp 552 (a := 208) (n := 48) (b := 552) (k := 336) (by decide) (by decide)
    (Or.inr (by decide)) (by decide) (by decide))

end

/-! ## The search's precondition -/

/-- The regions the search reads, and those it writes. -/
def sReads (p : GenPublic) (used : Nat) (st : KeyProgress) : List Region := [rE p, rP p st, rR p used, rA p]
def sWrites (p : GenPublic) (st : KeyProgress) : List Region := [rO p st, rU p, rS p, rT p]

/-- The search's entry, as the call makes it. -/
abbrev callS (p : GenPublic) (used : Nat) (st : KeyProgress) (u : State) : State :=
  u.callEntry.withRegions (sReads p used st) (sWrites p st)

open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)

theorem F_48 (p : GenPublic) : p.F - BitVec.ofNat 64 48 = p.sp - BitVec.ofNat 64 208 := by
  rw [GenPublic.F, BitVec.sub_sub]; rfl

theorem callS_rsp {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State}
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) :
    (callS p used st u).gpr .rsp = p.sp - BitVec.ofNat 64 216 := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, hu, BitVec.sub_sub]
  rfl

theorem callS_gpr {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State} {r : Reg} (hr : r ≠ .rsp) :
    (callS p used st u).gpr r = u.gpr r := by
  simp only [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem callS_argAddr {p : GenPublic} {used : Nat} {st : KeyProgress} {u : State}
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (j : Nat) :
    stackArgAddr (callS p used st u) j = p.sp - BitVec.ofNat 64 208 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
  rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]

theorem callS_arg {p : GenPublic} {used : Nat} {st : KeyProgress} {s u : State}
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) (j : Nat) (hj : j < 6) :
    stackArg (callS p used st u) j = frameValue (callValues p used st) j
      (word s.mem (p.sp - BitVec.ofNat 64 208) (8 * j)) := by
  have e1 : p.sp - BitVec.ofNat 64 208 - 8 + BitVec.ofNat 64 (8 + 8 * j) =
      p.sp - BitVec.ofNat 64 208 + BitVec.ofNat 64 (8 * j) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      BitVec.sub_add_cancel]
  have sep : Mem.Sep (p.sp - BitVec.ofNat 64 208 + BitVec.ofNat 64 (8 * j)) (64 / 8)
      (p.sp - BitVec.ofNat 64 208 - 8) (64 / 8) := by
    have := Offset.sep (p.sp - BitVec.ofNat 64 208 - 8) (d := 8 + 8 * j) (n := 8) (e := 0) (k := 8)
      (.inr (by omega)) (by omega) (by decide)
    rw [e1, BitVec.add_zero] at this
    exact this
  unfold stackArg
  rw [callS_argAddr hu, State.withRegions_mem, State.callEntry_mem, hu, Mem.readW_writeW_sep sep (by decide),
    hm, F_48]
  exact writeFrame_word _ _ _ (callValues_bound p used st) j (by omega)

/-- The search's stack arguments. -/
theorem callS_args {p : GenPublic} {used : Nat} {st : KeyProgress} {s u : State}
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    stackArg (callS p used st u) 0 = BitVec.ofNat 64 (plenOf p st) ∧
      stackArg (callS p used st u) 1 = p.rp + BitVec.ofNat 64 used ∧
      stackArg (callS p used st u) 2 = BitVec.ofNat 64 (p.randLen - used) ∧
      stackArg (callS p used st u) 3 = p.B ∧ stackArg (callS p used st u) 4 = BitVec.ofNat 64 (p.Z / 8) ∧
      stackArg (callS p used st u) 5 = p.stp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [callS_arg hu hm 0 (by decide)]; rfl
  · rw [callS_arg hu hm 1 (by decide)]; rfl
  · rw [callS_arg hu hm 2 (by decide)]; rfl
  · rw [callS_arg hu hm 3 (by decide)]; rfl
  · rw [callS_arg hu hm 4 (by decide)]; rfl
  · rw [callS_arg hu hm 5 (by decide)]; rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section

variable {p : GenPublic} {used : Nat} {st : KeyProgress} {s u : State}

/-- The call's entry writes only the controller's stack below its frame. -/
theorem callS_frame (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    Frame [cStack p] s.mem (callS p used st u).mem := by
  have h1 : Frame [cStack p] s.mem u.mem := by
    rw [hm, F_48]
    apply (Search.writeFrame_frame_size _ _ (callValues p used st) (size := 48) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, rA_sub⟩
  refine h1.trans ?_
  simp only [State.withRegions_mem, State.callEntry_mem]
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
  rw [hu, BitVec.sub_sub]
  rw [show p.sp - (BitVec.ofNat 64 208 + 8) = p.sp - BitVec.ofNat 64 552 + BitVec.ofNat 64 336 by
    rw [show BitVec.ofNat 64 208 + 8 = BitVec.ofNat 64 216 from rfl]
    exact Offset.sub_ofNat_eq _ (by decide)]
  exact Offset.contains_base _ (by decide) (by decide)

theorem callS_regions (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (ha : SearchRegs p st u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) (hf : CFacts p) :
    Search.inReads (callS p used st u) = sReads p used st ∧
      Search.inWrites (callS p used st u) = sWrites p st := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hL := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by obtain ⟨-, h, -⟩ := hL; omega)
  have tp : (BitVec.ofNat 64 (plenOf p st)).toNat = plenOf p st :=
    toNat_ofNat_lt (by have := plen_le (p := p) (st := st); obtain ⟨-, h, -⟩ := hL; omega)
  have tr : (BitVec.ofNat 64 (p.randLen - used)).toNat = p.randLen - used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by rw [toNat_ofNat_lt hf.z64]; exact hf.z8
  have hargs : stackArgAddr (callS p used st u) 0 = p.sp - BitVec.ofNat 64 208 := by
    rw [callS_argAddr hu, Nat.mul_zero, BitVec.add_zero]
  simp only [Search.inReads, Search.inWrites, Search.inE, Search.inP, Search.inRand, Search.inArgs,
    Search.inOut, Search.inUsed, Search.inScr, Search.inState, sReads, sWrites,
    callS_gpr (show Reg.rdi ≠ .rsp by decide), callS_gpr (show Reg.rsi ≠ .rsp by decide),
    callS_gpr (show Reg.rdx ≠ .rsp by decide), callS_gpr (show Reg.rcx ≠ .rsp by decide),
    callS_gpr (show Reg.r8 ≠ .rsp by decide), callS_gpr (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, tl, tp, tr, tz, hargs]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

theorem slot_nowrap (hf : CFacts p) {j n : Nat} (h : j * p.L + n ≤ 9 * p.L) :
    (p.kp + BitVec.ofNat 64 (j * p.L)).toNat + n ≤ 2 ^ 64 := by
  have := hf.nK
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  omega

theorem cstack_lo (hf : CFacts p) : (p.sp - BitVec.ofNat 64 552).toNat = p.sp.toNat - 552 := by
  have := hf.room
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 552).toNat = 552 from rfl]; omega),
    show (BitVec.ofNat 64 552).toNat = 552 from rfl]

/-- The search's precondition at its entry. -/
theorem callS_pre {original : State} (h : GenLive p original used st s)
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (ha : SearchRegs p st u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    Search.searchPre (callS p used st u) := by
  have hf := h.input.cfacts
  obtain ⟨hrd, hwr⟩ := callS_regions hu ha hm hf
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callS_args (used := used) (st := st) hu hm
  have hsp := callS_rsp (used := used) (st := st) hu
  have hfr := callS_frame hu hm
  have hL := hf.len
  obtain ⟨hL1, hL2, -⟩ := hL
  have hul := h.used_le
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hsi : (callS p used st u).gpr .rsi = BitVec.ofNat 64 p.L := by rw [callS_gpr (by decide)]; exact ha.2.1
  have h8 : (callS p used st u).gpr .r8 = BitVec.ofNat 64 8 := by rw [callS_gpr (by decide)]; exact ha.2.2.2.2.1
  have hcS : ∀ r ∈ [cStack p], (cS p).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact hf.stack (cS p) (by simp)
  have hword (d : Nat) (hd : d + 8 ≤ 56) :
      (callS p used st u).mem.readW (p.stp + BitVec.ofNat 64 d) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 d) 64 :=
    hfr.readW (Offset.contains_base _ hd (by omega)) hcS (by decide)
  have hE : Spec.Rsa.bytesAt (callS p used st u).mem (p.stp + 48) 8 = p.eB := by
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfr.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hf.stack (cS p) (by simp)).sub_left (by
        rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]; exact Offset.sub_base _ (by decide)))
      (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have hlow : below (p.sp - BitVec.ofNat 64 216) 336 = rLow p := by
    simp only [below, rLow, BitVec.sub_sub]; rfl
  have st0 := h.state
  -- The disjointness of the search's regions, from the controller's.
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, sU, sS, sT, sR⟩ := hst
  have oK := rO_sub (st := st) hf
  have pK := rP_sub (p := p) (st := st)
  have rRc := rR_sub (p := p) hul
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp]; have := hf.top
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 216).toNat = 216 from rfl]; have := hf.room; omega),
      show (BitVec.ofNat 64 216).toNat = 216 from rfl]; omega
  · rw [hsp, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 216).toNat = 216 from rfl]; have := hf.room; omega),
      show (BitVec.ofNat 64 216).toNat = 216 from rfl]; have := hf.room; show 336 ≤ _; omega
  · rw [hrd]; rfl
  · rw [hwr]; rfl
  · rw [hwr, hrd]
    intro r hr
    simp only [sWrites, sReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    have hlo := cstack_lo hf
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show (outOf p st).toNat + p.L ≤ 2 ^ 64
      unfold outOf; split
      · exact slot_nowrap hf (by omega)
      · exact slot_nowrap hf (by omega)
    · exact hf.nU
    · exact hf.nS
    · have := hf.nT; simp only; omega
    · simp only; rw [BitVec.toNat_add, toNat_ofNat_lt (by decide)]; have := hf.nT; omega
    · show (p.kp + BitVec.ofNat 64 (4 * p.L)).toNat + plenOf p st ≤ 2 ^ 64
      exact slot_nowrap hf (by have := plen_le (p := p) (st := st); omega)
    · simp only; rw [BitVec.toNat_add, toNat_ofNat_lt (by have := hf.rand64; omega)]; have := hf.nR; omega
    · simp only; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 208).toNat = 208 from rfl]; have := hf.room; omega),
        show (BitVec.ofNat 64 208).toNat = 208 from rfl]; have := hf.top; omega
  · rw [hwr]
    simp only [sWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hf.kU.sub_left oK, hf.kS.sub_left oK, (hf.kT.sub_left oK).sub_right rT_sub⟩,
      ⟨hf.uS, hf.uT.sub_right rT_sub⟩, hf.sT.sub_right rT_sub, fun _ h => h.elim⟩
  · rw [hwr, hrd]
    simp only [sWrites, sReads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨(hf.kT.sub_left oK).sub_right rE_sub, oP hf, (hf.kR.sub_left oK).sub_right rRc,
        (sK.sub_left oK).sub_right rA_sub⟩,
      ⟨hf.uT.sub_right rE_sub, (hf.kU.sub_left pK).symm, hf.uR.sub_right rRc, sU.sub_right rA_sub⟩,
      ⟨hf.sT.sub_right rE_sub, (hf.kS.sub_left pK).symm, hf.sR.sub_right rRc, sS.sub_right rA_sub⟩,
      ⟨tE, ((hf.kT.sub_left pK).sub_right rT_sub).symm, (hf.tR.sub_left rT_sub).sub_right rRc,
        (sT.sub_left rT_sub).sub_right rA_sub⟩⟩
  · rw [hwr, hrd, hsp, hlow]
    intro r hr
    simp only [sWrites, sReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(sK.sub_left oK).symm.sub_left rRet_sub, (sK.sub_left oK).symm.sub_left rLow_sub⟩
    · exact ⟨sU.symm.sub_left rRet_sub, sU.symm.sub_left rLow_sub⟩
    · exact ⟨sS.symm.sub_left rRet_sub, sS.symm.sub_left rLow_sub⟩
    · exact ⟨(sT.sub_left rT_sub).symm.sub_left rRet_sub, (sT.sub_left rT_sub).symm.sub_left rLow_sub⟩
    · exact ⟨(sT.sub_left rE_sub).symm.sub_left rRet_sub, (sT.sub_left rE_sub).symm.sub_left rLow_sub⟩
    · exact ⟨(sK.sub_left pK).symm.sub_left rRet_sub, (sK.sub_left pK).symm.sub_left rLow_sub⟩
    · exact ⟨(sR.sub_left rRc).symm.sub_left rRet_sub, (sR.sub_left rRc).symm.sub_left rLow_sub⟩
    · exact ⟨ret_args, args_low.symm⟩
  · simp only [Search.searchLen, hsi, tl]; exact ⟨hL1, hL2, hf.len.2.2⟩
  · rw [h8]; decide
  · rw [h8]; decide
  · simp only [Search.searchLen, hsi, tl, a0]
    rw [toNat_ofNat_lt (by have := plen_le (p := p) (st := st); omega)]
    unfold plenOf; split
    · exact .inl rfl
    · exact .inr rfl
  · simp only [Search.searchLen, hsi, tl, a4]
    rw [toNat_ofNat_lt hf.z64]
    have := hf.scratch; unfold Spec.Rsa.scratchWords at this ⊢; omega
  · have h0 := hword 0 (by decide)
    rw [BitVec.add_zero] at h0
    have h0' := st0.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0'
    have hlim : st.remaining < 2 ^ 64 := by
      have := st0.remaining_le
      unfold KeySearch.limitOf primeLimit at this
      split at this <;> omega
    have hrem : (Search.searchRemaining (callS p used st u)) = st.remaining := by
      simp only [Search.searchRemaining, a5, h0, h0']
      exact toNat_ofNat_lt hlim
    have hse : Search.searchE (callS p used st u) = p.eB := by
      simp only [Search.searchE, callS_gpr (show Reg.rcx ≠ .rsp by decide), callS_gpr (show Reg.r8 ≠ .rsp by decide),
        ha.2.2.2.1, ha.2.2.2.2.1, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
      exact hE
    rw [hrem, hse]
    simp only [Search.searchLen, hsi, tl]
    exact st0.remaining_le
  · simp only [Search.searchLen, hsi, tl, a5]
    rw [show (p.stp + 8 : Addr) = p.stp + BitVec.ofNat 64 8 from rfl, hword 8 (by decide)]
    exact st0.len
  · simp only [Search.searchLen, hsi, tl, a5]
    rw [show (p.stp + 16 : Addr) = p.stp + BitVec.ofNat 64 16 from rfl, hword 16 (by decide)]
    exact st0.cap
  · simp only [Search.searchLen, hsi, tl, a2]
    rw [toNat_ofNat_lt (by have := hf.rand64; omega)]
    have := hf.rand_cap; omega

end

end VG.Proof.RsaKeyGen.X86_64.Generate
