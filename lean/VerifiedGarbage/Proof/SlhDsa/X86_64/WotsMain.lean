module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Impl
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: `WotsCT` runs the taint analysis, which needs a `meta import` of each of its imports;
-- keeping the correctness proofs here keeps them out of that.

/-!
# SLH-DSA on x86-64: `wotsLeaves4` meets its contract

Calling `thash4` on the lanes, the prologue and the setup, a chain, its
steps, the chains, the public keys, and the whole function
(`wots4_correct`): from a state satisfying `wots4Contract`'s precondition,
it returns in a state satisfying its postcondition, keeping what the
calling convention keeps.
-/

@[expose] public section

/-! ## Calling `thash4` on the lanes of the working space

A call of an implementation `T` of `thash4` (`Thash4Impl`) on four lanes of
`stride` bytes at `scratch + o`, with `work` at `scratch`, from a state whose
writable regions include `scratch` (64 KiB) and whose stack below `rsp` is
disjoint from it (`t4call_ok`): each output, at `n + 32` in its lane, is
`SHAKE256` of its message, and the memory changes only in the outputs,
`work[0..1600)`, `work[2368..2400)` and the stack below `rsp`.
-/

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Spec.Sha3 (bytesAt shake256)

/-- What a call of `thash4` on the lanes at `S + o` changes. -/
def wotsT4Changes (n : Nat) (S : Addr) (o st : Nat) (sp : Addr) (stk : Nat) : List Region :=
  (List.range 4).map (fun j => ⟨at' S (o + j * st + n + 32), n⟩) ++
    [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp (8 + stk)]

theorem sub_scr {S : Addr} {o len : Nat} (h : o + len ≤ 65536) : Region.Sub ⟨at' S o, len⟩ ⟨S, 65536⟩ :=
  Offset.sub_base S h

theorem covers_scr {S : Addr} {wr : List Region} (hs : ⟨S, 65536⟩ ∈ wr) {o len : Nat} (h : o + len ≤ 65536) :
    Covers [⟨at' S o, len⟩] wr :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs, o, rfl, h⟩

section
variable {s : State} {S : Addr} {sk : Nat}

/-- The callee's state's registers. -/
theorem ce_gpr (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) : (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr]; exact State.callEntry_gpr _ h

theorem ce_rsp (rd wr : List Region) : (s.callEntry.withRegions rd wr).gpr .rsp = s.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

/-- The callee's memory is the caller's, but for the return address. -/
theorem ce_frame (rd wr : List Region) : Frame [below (s.gpr .rsp) 8] s.mem (s.callEntry.withRegions rd wr).mem := by
  rw [State.withRegions_mem, State.callEntry_mem]
  exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_arith) (by omega_arith))

theorem below8_sub (hsk : sk ≤ 16) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) (8 + sk)) :=
  below_sub (by omega_using [hsk]) (by omega_using [hsk])

theorem ret_sub (hsk : sk ≤ 16) (rd wr : List Region) :
    Region.Sub (retR (s.callEntry.withRegions rd wr)) (below (s.gpr .rsp) (8 + sk)) := by
  simp only [retR, ce_rsp]
  exact fun x hx => below8_sub hsk x (by simpa [below] using hx)

theorem stk8_sub (_hsk : sk ≤ 16) (rd wr : List Region) :
    Region.Sub (below ((s.callEntry.withRegions rd wr).gpr .rsp) sk) (below (s.gpr .rsp) (8 + sk)) := by
  rw [ce_rsp, Nat.add_comm 8 sk]
  exact below_callee _ _

theorem stk_sub (hsk : sk ≤ 16) (rd wr : List Region) :
    Region.Sub (below ((s.callEntry.withRegions rd wr).gpr .rsp) sk) (below (s.gpr .rsp) (8 + sk)) :=
  stk8_sub hsk rd wr

end

theorem toNat_at {S : Addr} {o : Nat} (hfit : S.toNat + 65536 ≤ 2 ^ 64) (ho : o < 65536) :
    (at' S o).toNat = S.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega_using [ho]),
    Nat.mod_eq_of_lt (by omega_using [hfit, ho])]

/-- The regions a call of `thash4` on the lanes at `S + o` is given: the lanes and `work`. -/
def t4wr (S : Addr) (o st : Nat) : List Region := [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]

/-- They are in the caller's writable regions. -/
theorem t4cov {s : State} {S : Addr} {o st : Nat} (hscr : (⟨S, 65536⟩ : Region) ∈ s.wr) (hol : o + 4 * st ≤ 65536) :
    Covers ([] ++ t4wr S o st) (s.rd ++ s.wr) ∧ Covers (t4wr S o st) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [t4wr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_right _ hscr, o, rfl, by omega_using [hol]⟩
    · exact ⟨_, List.mem_append_right _ hscr, 0, by simp, by simp [workLen]⟩
  · simp only [t4wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hscr, o, rfl, by omega_using [hol]⟩
    · exact ⟨_, hscr, 0, by simp, by simp [workLen]⟩

/-- The callee's precondition, at the entry of a call of `thash4` on the lanes at `S + o`. -/
theorem t4pre {n : Nat} (T : Thash4Impl n) {s : State} {S : Addr} {o st len : Nat}
    (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (ho : 2400 ≤ o) (hol : o + 4 * st ≤ 65536)
    (hdi : s.gpr .rdi = at' S o) (hsi : s.gpr .rsi = BitVec.ofNat 64 st) (hdx : s.gpr .rdx = BitVec.ofNat 64 len)
    (hcx : s.gpr .rcx = at' S (o + n + 32)) (h8 : s.gpr .r8 = S)
    (hstk : (below (s.gpr .rsp) (8 + T.stack)).Disjoint ⟨S, 65536⟩)
    (hrc : RcTable s.mem S) (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st) (hno : n + 32 + n ≤ st) :
    (thash4Contract n T.stack).pre (s.callEntry.withRegions [] (t4wr S o st)) := by
  have hst : st < 2 ^ 32 := by omega_using [hol]
  have hsk := T.stack_le
  have hst' : (BitVec.ofNat 64 st).toNat = st := by rw [BitVec.toNat_ofNat]; omega_using [hst]
  have hlen' : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega_using [hst, hll]
  let rd : List Region := []
  let wr : List Region := [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]
  have lanesS : Region.Sub ⟨at' S o, 4 * st⟩ ⟨S, 65536⟩ := sub_scr hol
  have workS : Region.Sub ⟨S, workLen⟩ ⟨S, 65536⟩ := Region.sub_prefix (by simp [workLen])
  have hcall : (below (s.gpr .rsp) 8).Disjoint ⟨S, 65536⟩ := hstk.sub_left (below8_sub hsk)
  show (thash4Contract n T.stack).pre (s.callEntry.withRegions rd wr)
  -- The callee's memory, in `scratch`, is the caller's.
  have emem : ∀ {a : Addr} {w : Nat}, (⟨S, 65536⟩ : Region).Contains a (w / 8) → w / 8 ≤ 65536 →
      (s.callEntry.withRegions rd wr).mem.readW a w = s.mem.readW a w := fun ha hw =>
    (ce_frame rd wr).readW ha (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hcall.symm) (by omega_using [hw])
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [ce_gpr rd wr (show Reg.rdi ≠ .rsp by decide), ce_gpr rd wr (show Reg.rsi ≠ .rsp by decide),
    ce_gpr rd wr (show Reg.rdx ≠ .rsp by decide), ce_gpr rd wr (show Reg.rcx ≠ .rsp by decide),
    ce_gpr rd wr (show Reg.r8 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, hst', hlen']
  · rfl
  · exact Offset.disjoint_base S (by simp only [workLen]; omega_using [ho]) (by omega_using [hol])
  · exact (hstk.sub_left (ret_sub hsk rd wr)).sub_right lanesS
  · exact (hstk.sub_left (ret_sub hsk rd wr)).sub_right workS
  · exact (hstk.sub_left (stk_sub hsk rd wr)).sub_right lanesS
  · exact (hstk.sub_left (stk_sub hsk rd wr)).sub_right workS
  · rw [toNat_at hfit (by omega_using [hol, ho, hlp, hll])]; omega_using [hol, hfit]
  · simp only [workLen]; omega_using [hfit]
  · exact hlp
  · exact hlm
  · exact hll
  · rw [ofNat_add', Nat.add_assoc]
  · exact hno
  · intro r hr j hj
    rw [emem (Offset.contains_base S (by omega_using [hr, hj]) (by omega_using [hr, hj, hfit])) (by decide)]
    exact hrc r hr j hj

theorem t4call_ok {n : Nat} (T : Thash4Impl n) (name : String) {s : State} {S : Addr} {o st len : Nat}
    (hscr : (⟨S, 65536⟩ : Region) ∈ s.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (ho : 2400 ≤ o) (hol : o + 4 * st ≤ 65536)
    (hdi : s.gpr .rdi = at' S o) (hsi : s.gpr .rsi = BitVec.ofNat 64 st) (hdx : s.gpr .rdx = BitVec.ofNat 64 len)
    (hcx : s.gpr .rcx = at' S (o + n + 32)) (h8 : s.gpr .r8 = S)
    (hstk : (below (s.gpr .rsp) (8 + T.stack)).Disjoint ⟨S, 65536⟩)
    (hrc : RcTable s.mem S) (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st) (hno : n + 32 + n ≤ st)
    {Q : State → Prop}
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      (∀ j < 4, bytesAt s'.mem (at' S (o + j * st + n + 32)) n =
        shake256 (bytesAt s.mem (at' S (o + j * st)) len) n) →
      Frame (wotsT4Changes n S o st (s.gpr .rsp) T.stack) s.mem s'.mem →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call name T.code) s Q := by
  have hst : st < 2 ^ 32 := by omega_using [hol]
  have hsk := T.stack_le
  have hd := T.depth_le
  have hst' : (BitVec.ofNat 64 st).toNat = st := by rw [BitVec.toNat_ofNat]; omega_using [hst]
  have hlen' : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega_using [hst, hll]
  let rd : List Region := []
  let wr : List Region := [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]
  have hcall : (below (s.gpr .rsp) 8).Disjoint ⟨S, 65536⟩ := hstk.sub_left (below8_sub hsk)
  have ebytes : ∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ ⟨S, 65536⟩ → l ≤ 65536 →
      bytesAt (s.callEntry.withRegions rd wr).mem a l = bytesAt s.mem a l := fun ha hl =>
    bytesAt_frame (ce_frame rd wr) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (hcall.sub_right ha).symm) (by omega_using [hl])
  have hpre : (thash4Contract n T.stack).pre (s.callEntry.withRegions rd wr) :=
    t4pre T hfit ho hol hdi hsi hdx hcx h8 hstk hrc hlp hlm hll hno
  have hcov : Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr := t4cov hscr hol
  refine WP.call_mx (hv := T.verified.1) T.nosp (by omega_using [hd]) hpre hcov.1 hcov.2
    fun s' hrd hwr hcs _ _ ⟨s₂, hm₂, _, hpost⟩ hmx => k s' hrd hwr hcs ?_ ?_ hmx
  · intro j hj
    obtain ⟨hout, _⟩ := hpost
    have e1 := hout j hj
    simp only [outAt, msg, ce_gpr rd wr (show Reg.rdi ≠ .rsp by decide), ce_gpr rd wr (show Reg.rsi ≠ .rsp by decide),
      ce_gpr rd wr (show Reg.rdx ≠ .rsp by decide), ce_gpr rd wr (show Reg.rcx ≠ .rsp by decide), hdi, hsi, hdx, hcx,
      hst', hlen', ofNat_add', hm₂] at e1
    rw [show o + j * st + n + 32 = o + n + 32 + j * st by omega_arith, e1,
      ebytes (sub_scr (by have : j * st ≤ 3 * st := Nat.mul_le_mul_right _ (by omega_using [hj]); omega_using [hol, this, hll])) (by omega_using [hol, hll])]
  · obtain ⟨_, hfr⟩ := hpost
    rw [← hm₂]
    refine Frame.trans ((ce_frame rd wr).sub fun r hr => ?_) (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (s.gpr .rsp) (8 + T.stack), (by simp [wotsT4Changes]), below_sub (by omega_arith) (by omega_using [hsk])⟩
    · simp only [thash4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
      · refine ⟨⟨at' S (o + j * st + n + 32), n⟩,
          List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩), ?_⟩
        simp only [outAt, ce_gpr rd wr (show Reg.rcx ≠ .rsp by decide), ce_gpr rd wr (show Reg.rsi ≠ .rsp by decide),
          hcx, hsi, hst', ofNat_add']
        rw [show o + n + 32 + j * st = o + j * st + n + 32 by omega_arith]
        exact fun _ h => h
      · refine ⟨⟨S, 1600⟩, (by simp [wotsT4Changes]), ?_⟩
        simp only [ce_gpr rd wr (show Reg.r8 ≠ .rsp by decide), h8]; exact fun _ h => h
      · refine ⟨⟨at' S 2368, 32⟩, (by simp [wotsT4Changes]), ?_⟩
        simp only [ce_gpr rd wr (show Reg.r8 ≠ .rsp by decide), h8, workLen]; exact fun _ h => h
      · exact ⟨below (s.gpr .rsp) (8 + T.stack), (by simp [wotsT4Changes]), stk8_sub hsk rd wr⟩

end VG.Proof.SlhDsa.X86_64

/-! ## `wotsLeaves4`, the prologue and the setup

The facts of the entry state the proof uses (`Entry`), what holds at every
point of the code (`Base`: the registers that hold the arguments, the
caller's callee-saved registers in frame 0, and the frame of what the
function may change), and the prologue and the setup of the lanes'
addresses.
-/

namespace VG.Proof.SlhDsa.X86_64.Wots4

open VG VG.X86_64 VG.X86_64.Steps
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.SlhDsa (fld)

/-! ## Blocks over the four lanes -/

theorem wp_range_flatMap {f : Nat → List Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s → (∀ j < K, ∀ t, P j t → WP isa (.block (f j)) t (P (j + 1))) →
      WP isa (.block ((List.range K).flatMap f)) s (P K)
  | 0, _, h0, _ => WP.block_nil h0
  | K + 1, _, h0, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (wp_range_flatMap K h0 fun j hj => hs j (by omega_using [hj]))
      fun t ht => hs K (by omega_using []) t ht)

theorem wp_range_map {f : Nat → Instr} {P : Nat → State → Prop} (K : Nat) {s : State} (h0 : P 0 s)
    (hs : ∀ j < K, ∀ t, P j t → WP isa (.block [f j]) t (P (j + 1))) :
    WP isa (.block ((List.range K).map f)) s (P K) := by
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap K h0 hs

/-! ## The layout, as numbers -/

theorem laneA_eq (k : Nat) : Layout.laneA k = 3296 + 128 * k := rfl
theorem laneB_eq (k : Nat) : Layout.laneB k = 3808 + 2208 * k := rfl
theorem oSave_eq (i : Nat) : Layout.oSave 0 i = 2400 + 8 * i := rfl
theorem oN_eq : Layout.oN = 12640 := rfl
theorem oVars_eq : Layout.oVars = 2400 := rfl
theorem oDigits_eq : Layout.oDigits = 30368 := rfl
theorem oSkSeed_eq : Layout.oSkSeed = 3168 := rfl
theorem oSigTmp_eq : Layout.oSigTmp = 31648 := rfl
theorem nodeSlots_eq : Layout.nodeSlots = 520 := rfl
theorem strideA_eq : Layout.strideA = 128 := rfl
theorem strideB_eq : Layout.strideB = 2208 := rfl

/-! ## The entry state -/

variable (p : Params)

/-- The layout of `p`. -/
abbrev L : Layout := ⟨p.n, p.len⟩

/-- What the proof uses of the entry state `σ`: the arguments, and the
values of the working space. -/
structure Entry (stk : Nat) (σ : State) (S sig : Addr) (kp idx : Nat) (pkSeed a16 skSeed : List Byte) : Prop where
  rdi : σ.gpr .rdi = S
  rsi : σ.gpr .rsi = BitVec.ofNat 64 kp
  rdx : σ.gpr .rdx = BitVec.ofNat 64 idx
  rcx : σ.gpr .rcx = sig
  reg : Regions stk σ S [] ⟨sig, p.len * p.n⟩
  env : Env p σ.mem S pkSeed a16
  sk : SkAt p σ.mem S skSeed
  kp4 : kp % 4 = 0
  kpN : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots
  idx32 : idx < 2 ^ 32
  dig : ∀ i < p.len, digitAt σ.mem S i < 16

/-- What `wotsLeaves4` may change: `thash4`'s work, frame 0, the lanes but
their `PK.seed` and `a16`, the four nodes, the signature, and the stack
below `rsp`. -/
def wch (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S Layout.oVars, 128⟩] ++
  (List.range 4).flatMap (fun k =>
    [⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩,
      ⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩]) ++
  [⟨at' S (Layout.oN + kp * p.n), 4 * p.n⟩, ⟨sig, p.len * p.n⟩, below sp stk]

variable {p} {stk : Nat} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-- What holds at every point of the code, from the entry state `σ`. -/
structure Base (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 kp
  r14 : s.gpr .r14 = BitVec.ofNat 64 idx
  r15 : s.gpr .r15 = sig
  saved : ∀ i < 6, s.mem.readW (at' S (Layout.oSave 0 i)) 64 = σ.gpr (savedRegs.getD i .rbx)
  frame : Frame (wch p S sig kp (σ.gpr .rsp) stk) σ.mem s.mem

namespace Entry

variable (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed)
include hE

/-- A range of `scratch` is writable. -/
theorem inScr {s : State} (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ 65536) : InRegions s.wr (at' S o) n :=
  ⟨⟨S, 65536⟩, by rw [hw, hE.reg.wr_eq]; exact List.mem_cons_self .., Offset.contains_base S h (by
    have := hE.reg.scr_fit; simp only [scratchLen] at this; omega_using [this, h])⟩

theorem inScr' {s : State} (_hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ 65536) :
    InRegions (s.rd ++ s.wr) (at' S o) n := by
  obtain ⟨r, hr', hc⟩ := hE.inScr hw h
  exact ⟨r, List.mem_append_right _ hr', hc⟩

/-- A range of the signature is writable. -/
theorem inSig {s : State} (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ p.len * p.n) (hn : 0 < n) :
    InRegions s.wr (sig + BitVec.ofNat 64 o) n :=
  ⟨⟨sig, p.len * p.n⟩, by rw [hw, hE.reg.wr_eq]; simp, Offset.contains_base sig h (by
    have hf := hE.reg.out_fit; simp only at hf; omega_using [hf, h, hn])⟩

theorem scr_fit : S.toNat + 65536 ≤ 2 ^ 64 := by have := hE.reg.scr_fit; simpa [scratchLen] using this

omit hE in
/-- Two ranges of `scratch`. -/
theorem dscr {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 65536) (hb : b + m ≤ 65536) :
    Region.Disjoint ⟨at' S a, n⟩ ⟨at' S b, m⟩ :=
  Offset.disjoint S h (by omega_using [ha]) (by omega_using [hb])

/-- A range of the signature and one of `scratch` below `oSigTmp`. -/
theorem dsig {o l a m : Nat} (hl : o + l ≤ p.len * p.n) (ha : a + m ≤ Layout.oSigTmp) :
    Region.Disjoint ⟨sig + BitVec.ofNat 64 o, l⟩ ⟨at' S a, m⟩ :=
  (hE.reg.out_scr.sub_left (Offset.sub_base sig hl)).sub_right (Offset.sub_base S ha)

/-- The stack below `rsp` and a range of `scratch`. -/
theorem dstk {a m : Nat} (ha : a + m ≤ 65536) : Region.Disjoint (below (σ.gpr .rsp) stk) ⟨at' S a, m⟩ :=
  hE.reg.stk_scr.sub_right (Offset.sub_base S ha)

end Entry

/-! ## The prologue -/

/-- After the saves: the registers as at entry, the first `j` saved. -/
structure SaveInv (σ : State) (S : Addr) (j : Nat) (t : State) : Prop where
  gpr : t.gpr = σ.gpr
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  saved : ∀ i < j, t.mem.readW (at' S (Layout.oSave 0 i)) 64 = σ.gpr (savedRegs.getD i .rbx)
  frame : Frame [⟨at' S Layout.oVars, 128⟩] σ.mem t.mem

theorem saves_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) :
    WP isa (.block (saveRegs 0 .rdi)) σ (SaveInv σ S 6) := by
  refine wp_range_map 6 ⟨rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩
    fun j hj t ht => ?_
  refine wp_store (a := at' S (Layout.oSave 0 j)) (by rw [ea_at, ht.gpr, hE.rdi])
    (hE.inScr ht.wr (by rw [oSave_eq]; omega_using [hj])) fun t' u => WP.block_nil ?_
  refine ⟨by rw [u.gpr, ht.gpr], by rw [u.rd, ht.rd], by rw [u.wr, ht.wr], fun i hi => ?_, ?_⟩
  · rw [u.mem]
    by_cases e : i = j
    · subst e; rw [Mem.readW_writeW_self64, ht.gpr]
    · rw [Mem.readW_writeW_sep (Offset.sep S (by rw [oSave_eq, oSave_eq]; omega_using [e, hi, hj])
        (by rw [oSave_eq]; omega_using [hi, hj]) (by rw [oSave_eq]; omega_using [hj])) (by decide),
        ht.saved i (by omega_using [hi, e])]
  · rw [u.mem]
    refine ht.frame.writeW (List.mem_singleton_self _) _ ?_
    show (⟨S + BitVec.ofNat 64 2400, 128⟩ : Region).Contains (S + BitVec.ofNat 64 (2400 + 8 * j)) 8
    rw [← ofNat_add']
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-! ## Fields of the lanes -/

/-- Field `off` (16, 20, 24 or 28 bytes after `PK.seed`) of the address of
lane `k` of `A`, and of `B`. -/
abbrev fA (p : Params) (m : Mem) (S : Addr) (k off : Nat) : List Byte := bytesAt m (at' S (Layout.laneA k + p.n + off)) 4
abbrev fB (p : Params) (m : Mem) (S : Addr) (k off : Nat) : List Byte := bytesAt m (at' S (Layout.laneB k + p.n + off)) 4

/-- A range of `scratch` that a write of `l` bytes elsewhere in it leaves. -/
theorem keepScr {m m' : Mem} {S : Addr} {a l b k : Nat} (hf : Frame [⟨at' S a, l⟩] m m')
    (h : a + l ≤ b ∨ b + k ≤ a) (ha : a + l ≤ 65536) (hb : b + k ≤ 65536) :
    bytesAt m' (at' S b) k = bytesAt m (at' S b) k :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Entry.dscr (Or.symm h) hb ha) (by omega_using [hb])

/-- A frame of a range of `scratch` within `R` extends a frame of the regions that include `R`. -/
theorem frame_ext {rs : List Region} {m₀ m m' : Mem} (h₀ : Frame rs m₀ m) {R : Region} (hR : R ∈ rs)
    {r : Region} (hr : Region.Sub r R) (h : Frame [r] m m') : Frame rs m₀ m' :=
  h₀.trans (h.sub fun _ hx => by simp only [List.mem_singleton] at hx; subst hx; exact ⟨R, hR, hr⟩)

/-! ## Base, through writes -/

/-- The lane tails are in `wch`. -/
theorem tailA_mem (k : Nat) (hk : k < 4) (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) :
    (⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩ : Region) ∈ wch p S sig kp sp stk := by
  simp only [wch, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, List.mem_cons_self ..⟩)

theorem tailB_mem (k : Nat) (hk : k < 4) (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) :
    (⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩ : Region) ∈ wch p S sig kp sp stk := by
  simp only [wch, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)

/-- A range of `scratch` within a lane tail. -/
theorem sub_tailA {S : Addr} {k a l : Nat} (h₁ : p.n + 16 ≤ a) (h₂ : a + l ≤ Layout.strideA) :
    Region.Sub ⟨at' S (Layout.laneA k + a), l⟩ ⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩ := by
  have e : at' S (Layout.laneA k + a) = at' S (Layout.laneA k + p.n + 16) + BitVec.ofNat 64 (a - (p.n + 16)) := by
    rw [ofNat_add', show Layout.laneA k + p.n + 16 + (a - (p.n + 16)) = Layout.laneA k + a by omega_using [h₁]]
  rw [e]; exact Offset.sub_base _ (by omega_using [h₁, h₂])

theorem sub_tailB {S : Addr} {k a l : Nat} (h₁ : p.n + 16 ≤ a) (h₂ : a + l ≤ Layout.strideB) :
    Region.Sub ⟨at' S (Layout.laneB k + a), l⟩ ⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩ := by
  have e : at' S (Layout.laneB k + a) = at' S (Layout.laneB k + p.n + 16) + BitVec.ofNat 64 (a - (p.n + 16)) := by
    rw [ofNat_add', show Layout.laneB k + p.n + 16 + (a - (p.n + 16)) = Layout.laneB k + a by omega_using [h₁]]
  rw [e]; exact Offset.sub_base _ (by omega_using [h₁, h₂])

/-! ## The setup -/

/-- Lane `k`'s fields after the setup. -/
structure LaneSet (p : Params) (m : Mem) (S : Addr) (kp k : Nat) : Prop where
  a20 : fA p m S k 20 = toByte (kp + k) 4
  b16 : fB p m S k 16 = toByte 1 4
  b20 : fB p m S k 20 = toByte (kp + k) 4
  b24 : fB p m S k 24 = toByte 0 4
  b28 : fB p m S k 28 = toByte 0 4

/-- Sizes of the parameter sets. -/
structure Sz (p : Params) : Prop where
  nv : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  len : p.len = 2 * p.n + 3
  lgw : p.lgw = 4
  shake : p.family = .shake

theorem Sz.n16 (h : Sz p) : 16 ≤ p.n := by rcases h.nv with e | e | e <;> rw [e] <;> decide
theorem Sz.n32 (h : Sz p) : p.n ≤ 32 := by rcases h.nv with e | e | e <;> rw [e] <;> decide
theorem Sz.n8 (h : Sz p) : p.n % 8 = 0 := by rcases h.nv with e | e | e <;> rw [e] <;> decide

theorem Base.step {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} {t t' : State} (hb : Base hE t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r, r ∈ [Reg.rsp, .rbx, .r12, .r14, .r15] → t'.gpr r = t.gpr r)
    {R : Region} (hR : R ∈ wch p S sig kp (σ.gpr .rsp) stk) {r : Region} (hr : Region.Sub r R)
    (hf : Frame [r] t.mem t'.mem) (hsv : ∀ i < 6, t'.mem.readW (at' S (Layout.oSave 0 i)) 64 =
      t.mem.readW (at' S (Layout.oSave 0 i)) 64) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hg _ (by simp), hb.rsp], by rw [hg _ (by simp), hb.rbx],
    by rw [hg _ (by simp), hb.r12], by rw [hg _ (by simp), hb.r14], by rw [hg _ (by simp), hb.r15],
    fun i hi => by rw [hsv i hi, hb.saved i hi], frame_ext hb.frame hR hr hf⟩

/-- A write of 4 bytes in a lane tail keeps the saved registers. -/
theorem saved_keep {m m' : Mem} {S : Addr} {a : Nat} (hf : Frame [⟨at' S a, 4⟩] m m') (ha : 3296 ≤ a) (ha' : a + 4 ≤ 65536)
    (i : Nat) (hi : i < 6) : m'.readW (at' S (Layout.oSave 0 i)) 64 = m.readW (at' S (Layout.oSave 0 i)) 64 :=
  hf.readW (r := ⟨at' S (Layout.oSave 0 i), 8⟩) (by simp [Region.Contains])
    (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact Entry.dscr (Or.inl (by rw [oSave_eq]; omega_using [hi, ha])) (by rw [oSave_eq]; omega_using [hi]) ha')
    (by decide)

theorem frame_cat {rs rs' : List Region} {m₁ m₂ m₃ : Mem} (h₁ : Frame rs m₁ m₂) (h₂ : Frame rs' m₂ m₃) :
    Frame (rs ++ rs') m₁ m₃ :=
  (h₁.mono fun _ hr => List.mem_append_left _ hr).trans (h₂.mono fun _ hr => List.mem_append_right _ hr)

/-- `Base` through a change of registers only. -/
theorem Base.regs {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} {t t' : State} (hb : Base hE t)
    (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hg : ∀ r, r ∈ [Reg.rsp, .rbx, .r12, .r14, .r15] → t'.gpr r = t.gpr r) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hg _ (by simp), hb.rsp], by rw [hg _ (by simp), hb.rbx],
    by rw [hg _ (by simp), hb.r12], by rw [hg _ (by simp), hb.r14], by rw [hg _ (by simp), hb.r15],
    fun i hi => by rw [hm, hb.saved i hi], by rw [hm]; exact hb.frame⟩

theorem base_regs_ne {r : Reg} (h : r ∈ [Reg.rsp, .rbx, .r12, .r14, .r15]) : r ≠ .rax := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- A 4-byte range of a lane tail of `A` or `B` is in `wch`. -/
def InTail (p : Params) (a : Nat) : Prop :=
  ∃ k < 4, (Layout.laneA k + p.n + 16 ≤ a ∧ a + 4 ≤ Layout.laneA k + Layout.strideA) ∨
    (Layout.laneB k + p.n + 16 ≤ a ∧ a + 4 ≤ Layout.laneB k + Layout.strideB)

theorem InTail.sub {a : Nat} (h : InTail p a) (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) :
    ∃ R ∈ wch p S sig kp sp stk, Region.Sub ⟨at' S a, 4⟩ R := by
  obtain ⟨k, hk, hA | hB⟩ := h
  · refine ⟨_, tailA_mem k hk S sig kp sp stk, ?_⟩
    have e := sub_tailA (p := p) (S := S) (k := k) (a := a - Layout.laneA k) (l := 4) (by omega_using [hA])
      (by omega_using [hA])
    rwa [Nat.add_sub_cancel' (by omega_using [hA])] at e
  · refine ⟨_, tailB_mem k hk S sig kp sp stk, ?_⟩
    have e := sub_tailB (p := p) (S := S) (k := k) (a := a - Layout.laneB k) (l := 4) (by omega_using [hB])
      (by omega_using [hB])
    rwa [Nat.add_sub_cancel' (by omega_using [hB])] at e

theorem InTail.lo {a : Nat} (h : InTail p a) : 3296 ≤ a := by
  obtain ⟨k, hk, hA | hB⟩ := h
  · rw [laneA_eq] at hA; omega_using [hA]
  · rw [laneB_eq] at hB; omega_using [hB]

theorem InTail.hi {a : Nat} (h : InTail p a) : a + 4 ≤ 65536 := by
  obtain ⟨k, hk, hA | hB⟩ := h
  · rw [laneA_eq, strideA_eq] at hA; omega_using [hA, hk]
  · rw [laneB_eq, strideB_eq] at hB; omega_using [hB, hk]

variable {is : List Instr} {Q : State → Prop}

/-- `setFieldR` in a lane tail, with `Base`. -/
theorem setFieldR_base (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) {t : State} (hb : Base hE t) {a : Nat}
    {r : Reg} (ha : InTail p a) (hr : (t.gpr r).toNat < 2 ^ 32)
    (k : ∀ t', Base hE t' → (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) →
      bytesAt t'.mem (at' S a) 4 = toByte (t.gpr r).toNat 4 → Frame [⟨at' S a, 4⟩] t.mem t'.mem →
      WP isa (.block is) t' Q) :
    WP isa (.block (setFieldR .rbx a r ++ is)) t Q := by
  refine setFieldR_ok (by decide) hr (by rw [hb.rbx]; exact hE.inScr hb.wr ha.hi) fun t' f => ?_
  rw [hb.rbx] at f
  obtain ⟨R, hR, hs⟩ := ha.sub S sig kp (σ.gpr .rsp) stk
  exact k t' (hb.step f.rd f.wr (fun g hg => f.gpr g (base_regs_ne hg)) hR hs f.frame
    (saved_keep f.frame ha.lo ha.hi)) f.gpr f.bytes f.frame

/-- `setField` in a lane tail, with `Base`. -/
theorem setField_base (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) {t : State} (hb : Base hE t) {a v : Nat}
    (ha : InTail p a) (hv : v < 2 ^ 31)
    (k : ∀ t', Base hE t' → (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) →
      bytesAt t'.mem (at' S a) 4 = toByte v 4 → Frame [⟨at' S a, 4⟩] t.mem t'.mem →
      WP isa (.block is) t' Q) :
    WP isa (.block (setField .rbx a v ++ is)) t Q := by
  refine setField_ok (by decide) hv (by rw [hb.rbx]; exact hE.inScr hb.wr ha.hi) fun t' f => ?_
  rw [hb.rbx] at f
  obtain ⟨R, hR, hs⟩ := ha.sub S sig kp (σ.gpr .rsp) stk
  exact k t' (hb.step f.rd f.wr (fun g hg => f.gpr g (base_regs_ne hg)) hR hs f.frame
    (saved_keep f.frame ha.lo ha.hi)) f.gpr f.bytes f.frame

/-- Four bytes of `scratch` that writes of four bytes elsewhere leave. -/
theorem keep4 {m m' : Mem} {S : Addr} {as : List Nat} (hf : Frame (as.map fun a => ⟨at' S a, 4⟩) m m') {b : Nat}
    (h : ∀ a ∈ as, (a + 4 ≤ b ∨ b + 4 ≤ a) ∧ a + 4 ≤ 65536) (hb : b + 4 ≤ 65536) :
    bytesAt m' (at' S b) 4 = bytesAt m (at' S b) 4 :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact Entry.dscr (Or.symm (h a ha).1) hb (h a ha).2) (by decide)

theorem Entry.kp_lt (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) : kp + 4 ≤ 1040 := by
  have h2 : (kp + 4) * 16 ≤ (kp + 4) * p.n := Nat.mul_le_mul_left _ hz.n16
  have h3 := hE.kpN
  rw [nodeSlots_eq] at h3
  omega_using [h2, h3]

theorem sext_ofNat {k : Nat} (hk : k < 2 ^ 31) : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
  have hm : (BitVec.ofNat 32 k).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
    rw [Nat.mod_eq_of_lt (by omega_using [hk])]; omega_using [hk]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hk]), Nat.mod_eq_of_lt (by omega_using [hk]), Nat.mod_eq_of_lt (by omega_using [hk])]

/-- The fields of lane `k` that the setup writes. -/
def setupOffs (p : Params) (k : Nat) : List Nat :=
  [Layout.laneA k + p.n + 20, Layout.laneB k + p.n + 20, Layout.laneB k + p.n + 16, Layout.laneB k + p.n + 24,
    Layout.laneB k + p.n + 28]

theorem setupOffs_tail (hz : Sz p) {k : Nat} (hk : k < 4) : ∀ a ∈ setupOffs p k, InTail p a := by
  have := hz.n32
  intro a ha
  simp only [setupOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨k, hk, Or.inl (by rw [strideA_eq]; omega_using [this])⟩
  all_goals exact ⟨k, hk, Or.inr (by rw [strideB_eq]; omega_using [this])⟩

theorem setupOffs_far (hz : Sz p) {k k' : Nat} (hk : k < 4) (hk' : k' < k) :
    ∀ a ∈ setupOffs p k, ∀ off, 16 ≤ off → off ≤ 28 →
      ((a + 4 ≤ Layout.laneA k' + p.n + off ∨ Layout.laneA k' + p.n + off + 4 ≤ a) ∧ a + 4 ≤ 65536) ∧
      ((a + 4 ≤ Layout.laneB k' + p.n + off ∨ Layout.laneB k' + p.n + off + 4 ≤ a) ∧ a + 4 ≤ 65536) := by
  have := hz.n32
  intro a ha off h₁ h₂
  simp only [setupOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp only [laneA_eq, laneB_eq] <;> omega_using [this, hk, hk', h₁, h₂]

theorem LaneSet.keep {m m' : Mem} {k k' : Nat} (hz : Sz p) (hk : k < 4) (hk' : k' < k)
    (hl : LaneSet p m S kp k') (hf : Frame ((setupOffs p k).map fun a => ⟨at' S a, 4⟩) m m') :
    LaneSet p m' S kp k' := by
  have := hz.n32
  have hA : ∀ off, 16 ≤ off → off ≤ 28 → fA p m' S k' off = fA p m S k' off := fun off h₁ h₂ =>
    keep4 hf (fun a ha => (setupOffs_far hz hk hk' a ha off h₁ h₂).1) (by rw [laneA_eq]; omega_using [this, hk, hk', h₂])
  have hB : ∀ off, 16 ≤ off → off ≤ 28 → fB p m' S k' off = fB p m S k' off := fun off h₁ h₂ =>
    keep4 hf (fun a ha => (setupOffs_far hz hk hk' a ha off h₁ h₂).2) (by rw [laneB_eq]; omega_using [this, hk, hk', h₂])
  exact ⟨by rw [hA 20 (by decide) (by decide), hl.a20], by rw [hB 16 (by decide) (by decide), hl.b16],
    by rw [hB 20 (by decide) (by decide), hl.b20], by rw [hB 24 (by decide) (by decide), hl.b24],
    by rw [hB 28 (by decide) (by decide), hl.b28]⟩

/-- Ranges of lanes apart. -/
local macro "lane_far" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
  forall_eq_or_imp, forall_eq, laneA_eq, laneB_eq]; omega))

local macro "lane_bnd" : tactic => `(tactic| (simp only [laneA_eq, laneB_eq]; omega))

theorem setupLane_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k : Nat} (hk : k < 4)
    {t : State} (hb : Base hE t) (hl : ∀ k' < k, LaneSet p t.mem S kp k') :
    WP isa (.block (([.mov .r10 (.reg .r12), .alu .add .r10 (.imm (BitVec.ofNat 32 k))] : List Instr) ++
      setFieldR .rbx (Layout.laneA k + (L p).adrsOff + 20) .r10 ++
      setFieldR .rbx (Layout.laneB k + (L p).adrsOff + 20) .r10 ++
      setField .rbx (Layout.laneB k + (L p).adrsOff + 16) 1 ++ setField .rbx (Layout.laneB k + (L p).adrsOff + 24) 0 ++
      setField .rbx (Layout.laneB k + (L p).adrsOff + 28) 0)) t
      (fun t' => (Base hE t' ∧ ∀ k' < k + 1, LaneSet p t'.mem S kp k') ∧
        Frame ((setupOffs p k).map fun a => (⟨at' S a, 4⟩ : Region)) t.mem t'.mem) := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have ht := setupOffs_tail hz hk
  simp only [List.append_assoc, List.cons_append, List.nil_append, Layout.adrsOff]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => ?_
  have hr10 : t₂.gpr .r10 = BitVec.ofNat 64 (kp + k) := by
    rw [u₂.gpr, u₁.gpr, hb.r12, sext_ofNat (by omega_using [hk]), ← BitVec.ofNat_add]
  have hb₂ : Base hE t₂ := hb.regs (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    (fun g hg => by
      have : g ≠ .r10 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₂.other _ this, u₁.other _ this])
  have hv : (t₂.gpr .r10).toNat = kp + k := by
    rw [hr10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hkp, hk])]
  have hlt : (t₂.gpr .r10).toNat < 2 ^ 32 := by rw [hv]; omega_using [hkp, hk]
  rw [← List.append_nil (setField .rbx (Layout.laneB k + p.n + 28) 0)]
  refine setFieldR_base hE hb₂ (ht _ (by simp [setupOffs])) hlt fun t₃ b₃ g₃ y₃ f₃ => ?_
  have hr3 : t₃.gpr .r10 = t₂.gpr .r10 := g₃ _ (by decide)
  refine setFieldR_base hE b₃ (ht _ (by simp [setupOffs])) (by rw [hr3]; exact hlt) fun t₄ b₄ _ y₄ f₄ => ?_
  refine setField_base hE b₄ (ht _ (by simp [setupOffs])) (by decide) fun t₅ b₅ _ y₅ f₅ => ?_
  refine setField_base hE b₅ (ht _ (by simp [setupOffs])) (by decide) fun t₆ b₆ _ y₆ f₆ => ?_
  refine setField_base hE b₆ (ht _ (by simp [setupOffs])) (by decide) fun t₇ b₇ _ y₇ f₇ => ?_
  rw [hr3, hv] at y₄
  rw [hv] at y₃
  have hf : Frame ((setupOffs p k).map fun a => (⟨at' S a, 4⟩ : Region)) t.mem t₇.mem := by
    have := frame_cat (frame_cat (frame_cat (frame_cat f₃ f₄) f₅) f₆) f₇
    rw [u₂.mem, u₁.mem] at this; exact this
  refine WP.block_nil ⟨⟨b₇, ?_⟩, hf⟩
  intro k' hk'
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hlt' | rfl
  · exact (hl k' hlt').keep hz hk hlt' hf
  · have far : ∀ (as : List Nat) {m m' : Mem}, Frame (as.map fun a => (⟨at' S a, 4⟩ : Region)) m m' →
        ∀ b, (∀ a ∈ as, (a + 4 ≤ b ∨ b + 4 ≤ a) ∧ a + 4 ≤ 65536) → b + 4 ≤ 65536 →
        bytesAt m' (at' S b) 4 = bytesAt m (at' S b) 4 := fun _ _ _ hf' _ h hb' => keep4 hf' h hb'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [fA, far [Layout.laneB k' + p.n + 20, Layout.laneB k' + p.n + 16, Layout.laneB k' + p.n + 24,
        Layout.laneB k' + p.n + 28] (frame_cat (frame_cat (frame_cat f₄ f₅) f₆) f₇) _ (by lane_far) (by lane_bnd), y₃]
    · rw [fB, far [Layout.laneB k' + p.n + 24, Layout.laneB k' + p.n + 28] (frame_cat f₆ f₇) _ (by lane_far)
        (by lane_bnd), y₅]
    · rw [fB, far [Layout.laneB k' + p.n + 16, Layout.laneB k' + p.n + 24, Layout.laneB k' + p.n + 28]
        (frame_cat (frame_cat f₅ f₆) f₇) _ (by lane_far) (by lane_bnd), y₄]
    · rw [fB, far [Layout.laneB k' + p.n + 28] f₇ _ (by lane_far) (by lane_bnd), y₆]
    · rw [fB, y₇]

/-- What holds after the setup. -/
structure SetupPost (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (t : State) : Prop where
  base : Base hE t
  r13 : t.gpr .r13 = 0
  lanes : ∀ k < 4, LaneSet p t.mem S kp k
  scr : Frame [⟨S, Layout.oSigTmp⟩] σ.mem t.mem

theorem oVars_mem (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) :
    (⟨at' S Layout.oVars, 128⟩ : Region) ∈ wch p S sig kp sp stk := by
  simp [wch]

theorem setup_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) :
    WP isa (.block (Wots.pro ++ Wots.setup (L p))) σ (SetupPost hE) := by
  rw [Wots.pro, List.append_assoc]
  refine WP.block_append (WP.mono (saves_ok hE) fun t ht => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => ?_
  have hb : Base hE t₄ := by
    refine ⟨by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, ht.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, ht.wr],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht.gpr],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ht.gpr, hE.rdi],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), ht.gpr, hE.rsi],
      by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), ht.gpr, hE.rdx],
      by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht.gpr, hE.rcx],
      fun i hi => by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, ht.saved i hi], ?_⟩
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact ht.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact oVars_mem S sig kp _ stk
  rw [Wots.setup]
  have hn := hz.n32
  have hsub : ∀ {a l : Nat}, a + l ≤ Layout.oSigTmp → Region.Sub ⟨at' S a, l⟩ ⟨S, Layout.oSigTmp⟩ :=
    fun h => Offset.sub_base S h
  refine WP.block_append (WP.mono (wp_range_flatMap 4 (P := fun j t => (Base hE t ∧ ∀ k' < j, LaneSet p t.mem S kp k') ∧
      Frame [⟨S, Layout.oSigTmp⟩] σ.mem t.mem)
    ⟨⟨hb, fun _ h => absurd h (by omega_using [])⟩, by
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact ht.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hsub (by rw [oVars_eq, oSigTmp_eq]; decide)⟩⟩
    fun j hj t ht => WP.mono (setupLane_ok hE hz hj ht.1.1 ht.1.2) fun t' h => ⟨h.1, ht.2.trans (h.2.sub fun r hr => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      refine ⟨_, List.mem_singleton_self _, hsub ?_⟩
      simp only [setupOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp only [laneA_eq, laneB_eq, oSigTmp_eq] <;>
        omega_using [hj, hn])⟩) fun t ht => ?_)
  refine wp_mov32i fun t' u => WP.block_nil ⟨ht.1.1.regs u.mem u.rd u.wr (fun g hg => u.other g (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide)),
    by rw [u.gpr]; rfl, by rw [u.mem]; exact ht.1.2, by rw [u.mem]; exact ht.2⟩

/-! ## What `wotsLeaves4` never changes -/

/-- A range of `scratch` outside what `wch` allows to change: the round
constants, `SK.seed`, the lanes' `PK.seed` and `a16`, the digits. -/
def Out (p : Params) (a l : Nat) : Prop :=
  (1600 ≤ a ∧ a + l ≤ 2368) ∨ (2528 ≤ a ∧ a + l ≤ 3296) ∨
    (3296 ≤ a ∧ a + l ≤ 3808 ∧ (a - 3296) % 128 + l ≤ p.n + 16) ∨
    (3808 ≤ a ∧ a + l ≤ 12640 ∧ (a - 3808) % 2208 + l ≤ p.n + 16) ∨ (29280 ≤ a ∧ a + l ≤ 31648)

theorem Out.disj (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {a l : Nat} (h : Out p a l) :
    ∀ R ∈ wch p S sig kp (σ.gpr .rsp) stk, Region.Disjoint ⟨at' S a, l⟩ R := by
  have hn := hz.n32
  have hkp : kp * p.n + 4 * p.n ≤ 16640 := by have := hE.kpN; rw [nodeSlots_eq, Nat.add_mul] at this; exact this
  have ha : a + l ≤ 31648 := by unfold Out at h; omega_using [h]
  intro R hR
  simp only [wch, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false]
    at hR
  rcases hR with ((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl | rfl | rfl
  · exact Offset.disjoint_base S (by unfold Out at h; omega_using [h]) (by omega_using [ha])
  · exact Entry.dscr (by unfold Out at h; omega_using [h]) (by omega_using [ha]) (by decide)
  · exact Entry.dscr (by unfold Out at h; rw [oVars_eq]; omega_using [h]) (by omega_using [ha]) (by decide)
  · exact Entry.dscr (by unfold Out at h; rw [laneA_eq, strideA_eq]; omega_using [h, hk, hn]) (by omega_using [ha])
      (by rw [laneA_eq, strideA_eq]; omega_using [hk, hn])
  · exact Entry.dscr (by unfold Out at h; rw [laneB_eq, strideB_eq]; omega_using [h, hk, hn]) (by omega_using [ha])
      (by rw [laneB_eq, strideB_eq]; omega_using [hk, hn])
  · exact Entry.dscr (by unfold Out at h; rw [oN_eq]; omega_using [h, hkp]) (by omega_using [ha])
      (by rw [oN_eq]; omega_using [hkp])
  · exact (hE.reg.out_scr.sub_right (Offset.sub_base S (by rw [oSigTmp_eq]; exact ha))).symm
  · exact (hE.dstk (by omega_using [ha])).symm

theorem Base.bytes {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t)
    {a l : Nat} (h : Out p a l) : bytesAt t.mem (at' S a) l = bytesAt σ.mem (at' S a) l :=
  bytesAt_frame hb.frame (h.disj hE hz) (by unfold Out at h; omega_using [h])

theorem Base.readW {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t)
    {a : Nat} (h : Out p a 8) : t.mem.readW (at' S a) 64 = σ.mem.readW (at' S a) 64 :=
  hb.frame.readW (r := ⟨at' S a, 8⟩) (by simp [Region.Contains]) (h.disj hE hz) (by decide)

theorem Base.env {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t) :
    Env p t.mem S pkSeed a16 := by
  have hn := hz.n32
  refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [show S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k) = at' S (1600 + 32 * r + 8 * k) from rfl,
      hb.readW hz (Or.inl (by omega_using [hr, hk]))]
    exact hE.env.rc r hr k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneA_eq]; right; right; left; omega_using [hk, hn])]; exact hE.env.seedA k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneB_eq]; right; right; right; left; omega_using [hk, hn])]
    exact hE.env.seedB k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneA_eq]; right; right; left; omega_using [hk, hn])]; exact hE.env.adrsA k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneB_eq]; right; right; right; left; omega_using [hk, hn])]
    exact hE.env.adrsB k hk

theorem Base.sk {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t) :
    SkAt p t.mem S skSeed := by
  have hn := hz.n32
  unfold SkAt; rw [hb.bytes hz (by unfold Out; rw [oSkSeed_eq]; right; left; omega_using [hn])]; exact hE.sk

theorem Base.digit {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t)
    {i : Nat} (hi : i < p.len) : t.mem (at' S (Layout.oDigits + i)) = σ.mem (at' S (Layout.oDigits + i)) := by
  have hn := hz.n32; have hl := hz.len
  have := hb.frame.bytes (R := ⟨at' S (Layout.oDigits + i), 1⟩) (Out.disj hE hz (by unfold Out; rw [oDigits_eq]; right; right; right; right; omega_using [hi, hn, hl])) (by show 1 ≤ 2 ^ 64; decide) (i := 0) (by show 0 < 1; decide)
  simpa using this

/-! ## The calls of `thash4` -/

/-- `Base` through a change of memory in ranges of `wch` away from frame 0. -/
theorem Base.ofFrame {hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed} {t t' : State} (hb : Base hE t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r, r ∈ [Reg.rsp, .rbx, .r12, .r14, .r15] → t'.gpr r = t.gpr r)
    {rs : List Region} (hf : Frame rs t.mem t'.mem) (hs : ∀ r ∈ rs, ∃ R ∈ wch p S sig kp (σ.gpr .rsp) stk, Region.Sub r R)
    (hsv : ∀ r ∈ rs, Region.Disjoint ⟨at' S 2400, 48⟩ r) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hg _ (by simp), hb.rsp], by rw [hg _ (by simp), hb.rbx],
    by rw [hg _ (by simp), hb.r12], by rw [hg _ (by simp), hb.r14], by rw [hg _ (by simp), hb.r15],
    fun i hi => by
      rw [hf.readW (r := ⟨at' S (Layout.oSave 0 i), 8⟩) (by simp [Region.Contains])
        (fun r hr => (hsv r hr).sub_left (by
          rw [oSave_eq]
          show Region.Sub ⟨S + BitVec.ofNat 64 (2400 + 8 * i), 8⟩ ⟨S + BitVec.ofNat 64 2400, 48⟩
          rw [← ofNat_add']; exact Offset.sub_base _ (by omega_using [hi]))) (by decide), hb.saved i hi],
    hb.frame.trans (hf.sub hs)⟩

/-- The lanes of `A` or of `B`. -/
def Lanes (o st : Nat) : Prop := (o = 3296 ∧ st = 128) ∨ (o = 3808 ∧ st = 2208)

theorem Lanes.out_sub {o st : Nat} (h : Lanes o st) (hz : Sz p) {j : Nat} (hj : j < 4) (S sig : Addr) (kp : Nat)
    (sp : Addr) (stk : Nat) : ∃ R ∈ wch p S sig kp sp stk, Region.Sub ⟨at' S (o + j * st + p.n + 32), p.n⟩ R := by
  have hn := hz.n32
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨_, tailA_mem j hj S sig kp sp stk, ?_⟩
    have e := sub_tailA (p := p) (S := S) (k := j) (a := p.n + 32) (l := p.n) (by omega_using [])
      (by rw [strideA_eq]; omega_using [hn])
    rwa [laneA_eq, show 3296 + 128 * j + (p.n + 32) = 3296 + j * 128 + p.n + 32 by omega_using []] at e
  · refine ⟨_, tailB_mem j hj S sig kp sp stk, ?_⟩
    have e := sub_tailB (p := p) (S := S) (k := j) (a := p.n + 32) (l := p.n) (by omega_using [])
      (by rw [strideB_eq]; omega_using [hn])
    rwa [laneB_eq, show 3808 + 2208 * j + (p.n + 32) = 3808 + j * 2208 + p.n + 32 by omega_using []] at e

/-- What a call of `thash4` changes is in `wch`, away from frame 0. -/
theorem t4Changes_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {o st stk' : Nat}
    (hl : Lanes o st) (hs : stk = 8 + stk') :
    ∀ r ∈ wotsT4Changes p.n S o st (σ.gpr .rsp) stk', (∃ R ∈ wch p S sig kp (σ.gpr .rsp) stk, Region.Sub r R) ∧
      Region.Disjoint ⟨at' S 2400, 48⟩ r := by
  have hn := hz.n32
  intro r hr
  simp only [wotsT4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · refine ⟨hl.out_sub hz hj S sig kp _ stk, Entry.dscr ?_ (by decide) ?_⟩ <;>
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega_using [hj, hn]
  · exact ⟨⟨_, by simp [wch], fun _ h => h⟩, Offset.disjoint_base S (by decide) (by decide)⟩
  · exact ⟨⟨_, by simp [wch], fun _ h => h⟩, Entry.dscr (by decide) (by decide) (by decide)⟩
  · subst hs
    exact ⟨⟨below (σ.gpr .rsp) (8 + stk'), by simp [wch], fun _ h => h⟩, (hE.dstk (a := 2400) (m := 48) (by decide)).symm⟩

theorem zext_ofNat {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x).setWidth 64 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega_using [hx])]

/-- A block that never loads MXCSR keeps it. -/
theorem wp_mx {is : List Instr} (h : is.all (fun i => !loadsMxcsr i) = true) {s : State} {Q : State → Prop}
    (hw : WP isa (.block is) s fun t => t.mxcsr = s.mxcsr → Q t) : WP isa (.block is) s Q :=
  WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using h) hw fun _ h₁ h₂ => h₁ h₂

theorem regs8 {g : Reg} (h : g ∈ [Reg.rsp, .rbx, .r12, .r14, .r15]) :
    g ≠ .rdi ∧ g ≠ .rsi ∧ g ≠ .rdx ∧ g ≠ .rcx ∧ g ≠ .r8 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- What the arguments of a call of `thash4` on the lanes at `o` leave, from `t`. -/
structure ArgsPost (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (t u : State) (o st len : Nat) : Prop where
  base : Base hE u
  mem : u.mem = t.mem
  mx : u.mxcsr = t.mxcsr
  gpr : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g
  rdi : u.gpr .rdi = at' S o
  rsi : u.gpr .rsi = BitVec.ofNat 64 st
  rdx : u.gpr .rdx = BitVec.ofNat 64 len
  rcx : u.gpr .rcx = at' S (o + p.n + 32)
  r8 : u.gpr .r8 = S

/-- The arguments of a call of `thash4` on the lanes at `o`, from a state with `Base`. -/
theorem targs_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {o st len : Nat} (hl : Lanes o st)
    (hll : len ≤ st) {t : State} (hb : Base hE t) :
    WP isa (.block (thashArgs (L p) o st len)) t (fun u => ArgsPost hE t u o st len) := by
  have hn := hz.n32
  have hst : st < 2 ^ 31 := by rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have ho : o < 2 ^ 31 := by rcases hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  refine wp_mx (by simp [thashArgs, loadsMxcsr]) ?_
  simp only [thashArgs]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => wp_mov32i fun t₃ u₃ => wp_mov32i fun t₄ u₄ =>
    wp_mov fun t₅ u₅ => wp_addi fun t₆ u₆ => wp_mov fun t₇ u₇ => WP.block_nil fun hmx => ?_
  have hm : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → t₇.gpr g = t.gpr g := fun g h₁ h₂ h₃ h₄ h₅ => by
    rw [u₇.other _ h₅, u₆.other _ h₄, u₅.other _ h₄, u₄.other _ h₃, u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]
  have hdi2 : t₂.gpr .rdi = at' S o := by rw [u₂.gpr, u₁.gpr, hb.rbx, sext_ofNat ho]
  refine ⟨hb.regs hm (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun g h' =>
      have h'' := regs8 h'; hg g h''.1 h''.2.1 h''.2.2.1 h''.2.2.2.1 h''.2.2.2.2), hm, hmx, hg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), hdi2]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    exact zext_ofNat (by omega_using [hst])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact zext_ofNat (by omega_using [hst, hll])
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hdi2]
    simp only [Layout.msgOff]
    rw [sext_ofNat (by omega_using [hn]), ofNat_add', Nat.add_assoc]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hb.rbx]

/-- A call of `thash4` on the lanes at `o`, from a state with `Base`. -/
theorem tcall_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    (hs : stk = 8 + T.stack) {o st len : Nat} (hl : Lanes o st) (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    {t : State} (hb : Base hE t) {Q : State → Prop}
    (k : ∀ t', Base hE t' → (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) →
      (∀ j < 4, bytesAt t'.mem (at' S (o + j * st + p.n + 32)) p.n =
        Spec.Sha3.shake256 (bytesAt t.mem (at' S (o + j * st)) len) p.n) →
      Frame (wotsT4Changes p.n S o st (σ.gpr .rsp) T.stack) t.mem t'.mem →
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 → Q t') :
    WP isa (thashCall (L p) name T.code o st len) t Q := by
  have hn := hz.n32
  refine WP.seq (WP.mono (targs_ok hE hz hl hll hb) fun t₇ a => ?_)
  have hb₇ := a.base
  have hm := a.mem
  refine t4call_ok T name (s := t₇) (S := S) (o := o) (st := st) (len := len)
    (by rw [hb₇.wr, hE.reg.wr_eq]; exact List.mem_cons_self ..) hE.scr_fit
    (by rcases hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide)
    (by rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) a.rdi a.rsi a.rdx a.rcx a.r8
    (by rw [hb₇.rsp]; have := hE.reg.stk_scr; rw [hs] at this; exact this) (by rw [hm]; exact (hb.env hz).rc)
    hlp hlm hll (by rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega_using [hn]) fun t' h₁ h₂ h₃ h₄ h₅ h₆ => ?_
  rw [hm] at h₄ h₅
  rw [hb₇.rsp] at h₅
  have hc := t4Changes_ok hE hz hl hs
  refine k t' (hb₇.ofFrame h₁ h₂ (fun g hg' => h₃ g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl | rfl <;> decide)) (by rw [hm]; exact h₅) (fun r hr => (hc r hr).1) fun r hr => (hc r hr).2)
    (fun r hr => by
      rw [h₃ r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact a.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide))
    h₄ h₅ (by rw [h₆, a.mx])

end VG.Proof.SlhDsa.X86_64.Wots4

/-! ## `wotsLeaves4`, the chains

What the lanes of `A` hold (`la`, `LaneA`): an address of the type `ty`,
key pair `κ`, chain `c`, hash `h`, and the message `M`, so that `thash4`
computes `F`, or `PRF` (`laneA_msg`); and the blocks of a chain: the private
key values (`prfLanes`), the type `WOTS_HASH` (`hashType`), the hash
addresses (`hashAdrs`) and the masked capture of the signature (`capture`).
-/

namespace VG.Proof.SlhDsa.X86_64.Wots4

open VG VG.X86_64 VG.X86_64.Steps
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.SlhDsa (fld)

variable {p : Params} {stk : Nat} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-! ## Bytes, split -/

theorem bytesAt_split (m : Mem) (S : Addr) (a x y : Nat) :
    bytesAt m (at' S a) (x + y) = bytesAt m (at' S a) x ++ bytesAt m (at' S (a + x)) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, ofNat_add', Nat.add_assoc]

/-- A lane's `PK.seed`, address and message. -/
theorem lane_msg (m : Mem) (S : Addr) (b n L : Nat) :
    bytesAt m (at' S b) (n + 32 + L) = bytesAt m (at' S b) n ++ (bytesAt m (at' S (b + n)) 16 ++
      (bytesAt m (at' S (b + n + 16)) 4 ++ (bytesAt m (at' S (b + n + 20)) 4 ++ (bytesAt m (at' S (b + n + 24)) 4 ++
        (bytesAt m (at' S (b + n + 28)) 4 ++ bytesAt m (at' S (b + n + 32)) L))))) := by
  rw [show n + 32 + L = n + (16 + (4 + (4 + (4 + (4 + L))))) by omega_using [], bytesAt_split, bytesAt_split,
    bytesAt_split, bytesAt_split, bytesAt_split, bytesAt_split]

/-! ## The lanes of `A` -/

/-- `l` bytes at `off` (from 16) after lane `k`'s `PK.seed` in `A`. -/
abbrev la (p : Params) (m : Mem) (S : Addr) (k off l : Nat) : List Byte :=
  bytesAt m (at' S (Layout.laneA k + p.n + off)) l

/-- Lane `k` of `A`: the type `ty`, key pair `κ`, chain `c`, hash `h`, message `M`. -/
structure LaneA (p : Params) (m : Mem) (S : Addr) (k ty κ c h : Nat) (M : List Byte) : Prop where
  f16 : la p m S k 16 4 = toByte ty 4
  f20 : la p m S k 20 4 = toByte κ 4
  f24 : la p m S k 24 4 = toByte c 4
  f28 : la p m S k 28 4 = toByte h 4
  msg : la p m S k 32 p.n = M

/-- A range of lane `k₂` that a change of a range of lane `k₁` leaves. -/
theorem la_keep (hz : Sz p) {m m' : Mem} {S : Addr} {k₁ o₁ l₁ k₂ o₂ l₂ : Nat}
    (hf : Frame [⟨at' S (Layout.laneA k₁ + p.n + o₁), l₁⟩] m m') (hk₁ : k₁ < 4) (hk₂ : k₂ < 4)
    (h₁ : 16 ≤ o₁) (h₁' : o₁ + l₁ ≤ p.n + 32) (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32)
    (h : k₁ ≠ k₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) : la p m' S k₂ o₂ l₂ = la p m S k₂ o₂ l₂ := by
  have hn := hz.n32
  exact keepScr hf (by rw [laneA_eq, laneA_eq]; omega_using [h, hk₁, hk₂, h₁, h₁', h₂, h₂', hn])
    (by rw [laneA_eq]; omega_using [hk₁, h₁', hn]) (by rw [laneA_eq]; omega_using [hk₂, h₂', hn])

/-- The fields and message of lane `k`, after its `PK.seed` and `a16`. -/
abbrev laneR (p : Params) (S : Addr) (k : Nat) : Region := ⟨at' S (Layout.laneA k + p.n + 16), p.n + 16⟩

theorem LaneA.keep (hz : Sz p) {m m' : Mem} {S : Addr} {k k' ty κ c h : Nat} {M : List Byte}
    (hl : LaneA p m S k' ty κ c h M) (hf : Frame [laneR p S k] m m') (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k') :
    LaneA p m' S k' ty κ c h M := by
  have hn := hz.n32
  have e : ∀ o l, 16 ≤ o → o + l ≤ p.n + 32 → la p m' S k' o l = la p m S k' o l := fun o l h₁ h₂ =>
    la_keep hz (o₁ := 16) hf hk hk' (by omega_using []) (by omega_using []) h₁ h₂ (Or.inl hne)
  exact ⟨by rw [e 16 4 (by omega_using []) (by omega_using [hn]), hl.f16],
    by rw [e 20 4 (by omega_using []) (by omega_using [hn]), hl.f20],
    by rw [e 24 4 (by omega_using []) (by omega_using [hn]), hl.f24],
    by rw [e 28 4 (by omega_using []) (by omega_using [hn]), hl.f28],
    by rw [e 32 p.n (by omega_using []) (by omega_using []), hl.msg]⟩

theorem laneR_tail (hz : Sz p) {k : Nat} (hk : k < 4) (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) :
    ∃ R ∈ wch p S sig kp sp stk, Region.Sub (laneR p S k) R := by
  have hn := hz.n32
  refine ⟨_, tailA_mem k hk S sig kp sp stk, ?_⟩
  have e := sub_tailA (p := p) (S := S) (k := k) (a := p.n + 16) (l := p.n + 16) (by omega_using [])
    (by rw [strideA_eq]; omega_using [hn])
  rwa [← Nat.add_assoc] at e

/-- A range of lane `k` is in `laneR`. -/
theorem la_sub {S : Addr} {k o l : Nat} (h₁ : 16 ≤ o) (h₂ : o + l ≤ p.n + 32) :
    Region.Sub ⟨at' S (Layout.laneA k + p.n + o), l⟩ (laneR p S k) := by
  have e : at' S (Layout.laneA k + p.n + o) = at' S (Layout.laneA k + p.n + 16) + BitVec.ofNat 64 (o - 16) := by
    rw [ofNat_add', show Layout.laneA k + p.n + 16 + (o - 16) = Layout.laneA k + p.n + o by omega_using [h₁]]
  rw [e]; exact Offset.sub_base _ (by omega_using [h₁, h₂])

theorem laneR_save (hz : Sz p) {k : Nat} (hk : k < 4) (S : Addr) : Region.Disjoint ⟨at' S 2400, 48⟩ (laneR p S k) := by
  have hn := hz.n32
  exact Entry.dscr (Or.inl (by rw [laneA_eq]; omega_using [])) (by decide) (by rw [laneA_eq]; omega_using [hk, hn])

/-- The message of lane `k` of `A` to `thash4`. -/
theorem laneA_msg {m : Mem} (henv : Env p m S pkSeed a16) {k ty κ c h : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneA p m S k ty κ c h M) :
    bytesAt m (at' S (Layout.laneA k)) (2 * p.n + 32) = pkSeed ++ fld a16 ty κ c h ++ M := by
  rw [show 2 * p.n + 32 = p.n + 32 + p.n by omega_using [], lane_msg, henv.seedA k hk, henv.adrsA k hk]
  obtain ⟨f16, f20, f24, f28, fm⟩ := hl
  simp only [la] at f16 f20 f24 f28 fm
  rw [f16, f20, f24, f28, fm]
  simp only [fld, List.append_assoc]

/-! ## The chains, in the specification -/

theorem a16_length {m : Mem} (henv : Env p m S pkSeed a16) : a16.length = 16 := by
  rw [← henv.adrsA 0 (by decide), bytesAt_length']

/-- The private key value. -/
theorem chainAt_zero (hz : Sz p) (h16 : a16.length = 16) {κ : Nat} (hκ : κ < 2 ^ 32) (i : Nat) :
    wotsChainAt p skSeed pkSeed a16 κ i 0 = shake256 (pkSeed ++ fld a16 WOTS_PRF κ i 0 ++ skSeed) p.n := by
  simp only [wotsChainAt, chain, List.range_zero, List.foldl_nil, prf, hz.shake, shakeAdrs]
  rw [VG.Proof.SlhDsa.wotsAdrs_fld h16, VG.Proof.SlhDsa.wotsSkAdrs_fld h16 _ _ _ _ hκ,
    VG.Proof.SlhDsa.setChainAddress_fld h16]

/-- A step of the chain: `F` with the hash address `j`. -/
theorem chainAt_succ (hz : Sz p) (h16 : a16.length = 16) (κ i j : Nat) :
    wotsChainAt p skSeed pkSeed a16 κ i (j + 1) =
      shake256 (pkSeed ++ fld a16 WOTS_HASH κ i j ++ wotsChainAt p skSeed pkSeed a16 κ i j) p.n := by
  simp only [wotsChainAt, chain, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
  rw [VG.Proof.SlhDsa.wotsAdrs_fld h16, VG.Proof.SlhDsa.setChainAddress_fld h16,
    VG.Proof.SlhDsa.setHashAddress_fld h16]
  simp only [F, hz.shake, shakeAdrs]

/-! ## Writes in a lane of `A`, with `Base` -/

theorem tailA_of (hz : Sz p) {k o : Nat} (hk : k < 4) (h₁ : 16 ≤ o) (h₂ : o ≤ 28) : InTail p (Layout.laneA k + p.n + o) :=
  ⟨k, hk, Or.inl ⟨by omega_using [h₁], by rw [strideA_eq]; have := hz.n32; omega_using [h₂, this]⟩⟩

/-- A copy into lane `k`'s message, with `Base`. -/
theorem copyA_base (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {t : State} (hb : Base hE t)
    {k src : Nat} (hk : k < 4) (hsrc : src + p.n ≤ 65536)
    (hd : Region.Disjoint ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ ⟨at' S src, p.n⟩) {Q : State → Prop}
    (kk : ∀ t', Base hE t' → (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) →
      la p t'.mem S k 32 p.n = bytesAt t.mem (at' S src) p.n →
      Frame [⟨at' S (Layout.laneA k + p.n + 32), p.n⟩] t.mem t'.mem → Q t') :
    WP isa (.block (copyWords .rbx (Layout.laneA k + (L p).msgOff) .rbx src (p.n / 8))) t Q := by
  have hn := hz.n32
  have h8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega_using [this]
  have hdst : at' S (Layout.laneA k + (L p).msgOff) = at' S (Layout.laneA k + p.n + 32) := by
    simp only [Layout.msgOff, Nat.add_assoc]
  refine WP.mono (copyWords_ok (s := t) (by decide) (by decide) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ ?_) fun t' c => ?_
  · rw [hb.rbx]
    exact hE.inScr hb.wr (by rw [laneA_eq]; simp only [Layout.msgOff]; omega_using [hj, h8, hn, hk])
  · rw [hb.rbx]
    exact hE.inScr' hb.rd hb.wr (by omega_using [hj, h8, hsrc])
  · rw [hb.rbx, h8]; show Region.Disjoint ⟨at' S _, _⟩ ⟨at' S _, _⟩; rw [hdst]; exact hd
  · omega_using [h8, hn]
  · rw [laneA_eq]; simp only [Layout.msgOff]; omega_using [h8, hn, hk]
  rw [hb.rbx, h8] at c
  change CopyPost t t' (at' S _) (at' S _) _ at c
  rw [hdst] at c
  obtain ⟨R, hR, hs⟩ := laneR_tail hz hk S sig kp (σ.gpr .rsp) stk
  refine kk t' (hb.ofFrame c.rd c.wr (fun g hg => c.gpr g (base_regs_ne hg)) c.frame
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨R, hR, fun x hx => hs x (la_sub (by omega_using []) (by omega_using []) x hx)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (laneR_save hz hk S).sub_right (la_sub (by omega_using []) (by omega_using []))))
    c.gpr (bytesAt_ext fun q hq => c.bytes q hq) c.frame

/-- Lane `k` of `A` for `PRF`. -/
theorem prfLane_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i : Nat} (hk : k < 4)
    (hi : i < 2 ^ 32) {t : State} (hb : Base hE t) (hr : t.gpr .r13 = BitVec.ofNat 64 i) :
    WP isa (.block (Wots.prfLane (L p) k)) t (fun t' => Base hE t' ∧ (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧
      la p t'.mem S k 16 4 = toByte WOTS_PRF 4 ∧ la p t'.mem S k 24 4 = toByte i 4 ∧
      la p t'.mem S k 28 4 = toByte 0 4 ∧ la p t'.mem S k 32 p.n = skSeed ∧
      la p t'.mem S k 20 4 = la p t.mem S k 20 4 ∧ Frame [laneR p S k] t.mem t'.mem) := by
  have hn := hz.n32
  simp only [Wots.prfLane, List.append_assoc, Layout.adrsOff]
  refine setField_base hE hb (tailA_of hz hk (by decide) (by decide)) (by decide) fun t₁ b₁ g₁ y₁ f₁ => ?_
  have hi' : (t₁.gpr .r13).toNat < 2 ^ 32 := by
    rw [g₁ _ (by decide), hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]; exact hi
  refine setFieldR_base hE b₁ (tailA_of hz hk (by decide) (by decide)) hi' fun t₂ b₂ g₂ y₂ f₂ => ?_
  refine setField_base hE b₂ (tailA_of hz hk (by decide) (by decide)) (by decide) fun t₃ b₃ g₃ y₃ f₃ => ?_
  refine copyA_base hE hz b₃ hk (src := Layout.oSkSeed) (by rw [oSkSeed_eq]; omega_using [hn])
    (Entry.dscr (Or.inr (by rw [laneA_eq, oSkSeed_eq]; omega_using [hn])) (by rw [laneA_eq]; omega_using [hk, hn])
      (by rw [oSkSeed_eq]; omega_using [hn])) fun t₄ b₄ g₄ y₄ f₄ => ?_
  have hv : (t₁.gpr .r13).toNat = i := by rw [g₁ _ (by decide), hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]
  rw [hv] at y₂
  have K := fun {m m' : Mem} {o₁ l₁ o₂ l₂ : Nat} (hf : Frame [⟨at' S (Layout.laneA k + p.n + o₁), l₁⟩] m m')
    (h₁ : 16 ≤ o₁) (h₁' : o₁ + l₁ ≤ p.n + 32) (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32)
    (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) => la_keep hz hf hk hk h₁ h₁' h₂ h₂' (Or.inr h)
  refine ⟨b₄, fun g hg => by rw [g₄ g hg, g₃ g hg, g₂ g hg, g₁ g hg], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₃ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₂ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
    exact y₁
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₃ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
    exact y₂
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
    exact y₃
  · rw [y₄]; exact (b₃.sk hz)
  · rw [K f₄ (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₃ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₂ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using []),
      K f₁ (by omega_using []) (by omega_using [hn]) (by omega_using []) (by omega_using [hn]) (by omega_using [])]
  · have s : ∀ {o l : Nat}, 16 ≤ o → o + l ≤ p.n + 32 → ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + o), l⟩ : Region)],
        ∃ R ∈ [laneR p S k], Region.Sub r R := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, la_sub h₁ h₂⟩
    exact (((f₁.sub (s (by omega_using []) (by omega_using [hn]))).trans (f₂.sub (s (by omega_using [])
      (by omega_using [hn])))).trans (f₃.sub (s (by omega_using []) (by omega_using [hn])))).trans
      (f₄.sub (s (by omega_using []) (by omega_using [])))

/-! ## The capture -/

/-- Chain `i` of the signature. -/
abbrev sigC (p : Params) (m : Mem) (sig : Addr) (i : Nat) : List Byte := bytesAt m (sig + BitVec.ofNat 64 (i * p.n)) p.n

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b :=
  ⟨fun h => by
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this,
   fun h => by rw [h]⟩

theorem toNat_lt_of {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 64 a).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h])]; exact h

/-- The masked copy of lane `k`'s value into chain `i` of the signature (at `rsi`). -/
theorem capLane_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i j : Nat} {D : BitVec 64}
    (hk : k < 4) (hi : i < p.len) (hj : j < 2 ^ 32) (hD : D.toNat < 2 ^ 32) {t : State} (hb : Base hE t)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 j ^^^ D) (hsi : t.gpr .rsi = sig + BitVec.ofNat 64 (i * p.n)) :
    WP isa (.block (Wots.captureLane (L p) k)) t (fun t' => Base hE t' ∧
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → t'.gpr g = t.gpr g) ∧
      sigC p t'.mem sig i = (if kp + k = idx ∧ j = D.toNat then la p t.mem S k 32 p.n else sigC p t.mem sig i) ∧
      Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem t'.mem) := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have h8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega_using [this]
  have hlen : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  simp only [Wots.captureLane, List.cons_append, List.nil_append]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => wp_xor fun t₃ u₃ => wp_or fun t₄ u₄ => wp_subi fun t₅ u₅ =>
    wp_shr (by decide) (by decide) fun t₆ u₆ => wp_mov32i fun t₇ u₇ => wp_sub fun t₈ u₈ => ?_
  have hg : ∀ g, g ≠ .rax → g ≠ .rdi → t₈.gpr g = t.gpr g := fun g h₁ h₂ => by
    rw [u₈.other _ h₂, u₇.other _ h₂, u₆.other _ h₁, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁,
      u₁.other _ h₁]
  have hm₈ : t₈.mem = t.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hb₈ : Base hE t₈ := hb.regs hm₈ (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) fun g h' =>
      hg g (base_regs_ne h') (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with rfl | rfl | rfl | rfl | rfl <;> decide)
  let P := kp + k = idx ∧ j = D.toNat
  have hmask : t₈.gpr .rdi = if decide P then BitVec.allOnes 64 else 0 := by
    have a2 : t₂.gpr .rax = BitVec.ofNat 64 (kp + k) := by
      rw [u₂.gpr, u₁.gpr, hb.r12, sext_ofNat (by omega_using [hk]), ← BitVec.ofNat_add]
    have a3 : t₃.gpr .rax = BitVec.ofNat 64 (kp + k) ^^^ BitVec.ofNat 64 idx := by
      rw [u₃.gpr, a2, u₂.other _ (by decide), u₁.other _ (by decide), hb.r14]
    have a4 : t₄.gpr .rax = (BitVec.ofNat 64 (kp + k) ^^^ BitVec.ofNat 64 idx) ||| (BitVec.ofNat 64 j ^^^ D) := by
      rw [u₄.gpr, a3, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdx]
    have a6 : t₆.gpr .rax = ((((BitVec.ofNat 64 (kp + k) ^^^ BitVec.ofNat 64 idx) |||
        (BitVec.ofNat 64 j ^^^ D)) - 1) >>> 63) := by
      rw [u₆.gpr, u₅.gpr, a4, show BitVec.signExtend 64 (1 : BitVec 32) = 1 from by decide]
    have d7 : t₇.gpr .rdi = 0 := by rw [u₇.gpr]; rfl
    rw [u₈.gpr, d7, u₇.other _ (by decide), a6,
      mask_eq (toNat_lt_of (by omega_using [hkp, hk])) (toNat_lt_of hE.idx32) (toNat_lt_of hj) hD]
    have e : (BitVec.ofNat 64 (kp + k) = BitVec.ofNat 64 idx ∧ BitVec.ofNat 64 j = D) ↔ P := by
      rw [ofNat_eq_iff (by omega_using [hkp, hk]) (by have := hE.idx32; omega_using [this])]
      refine and_congr Iff.rfl ⟨fun h => by rw [← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])],
        fun h => by rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
    by_cases c : P
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (e.mpr c)), decide_eq_true c]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => c (e.mp h))), decide_eq_false c]; rfl
  have hsi₈ : t₈.gpr .rsi = sig + BitVec.ofNat 64 (i * p.n) := by rw [hg _ (by decide) (by decide), hsi]
  have hfit : (sig + BitVec.ofNat 64 (i * p.n)).toNat + p.n ≤ 2 ^ 64 := by
    have hf := hE.reg.out_fit; simp only at hf
    have h16 := hz.n16
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hf, hlen, h16]),
      Nat.mod_eq_of_lt (by omega_using [hf, hlen, h16])]
    omega_using [hf, hlen]
  refine WP.mono (selWords_ok (s := t₈) (dst := .rsi) (src := .rbx) (d₁ := Layout.laneA k + (L p).msgOff)
    (w := p.n / 8) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ hmask (fun w hw => ?_) (fun w hw => ?_) ?_
    (by omega_using [h8, hn]) (by rw [hsi₈, h8]; exact hfit)) fun t' c => ?_
  · rw [hsi₈, ofNat_add']
    exact hE.inSig hb₈.wr (by omega_using [hw, h8, hlen]) (by decide)
  · rw [hb₈.rbx]
    exact hE.inScr' hb₈.rd hb₈.wr (by rw [laneA_eq]; simp only [Layout.msgOff]; omega_using [hw, h8, hn, hk])
  · rw [hsi₈, hb₈.rbx, h8]
    have := hE.dsig (o := i * p.n) (l := p.n) (a := Layout.laneA k + p.n + 32) (m := p.n) (by omega_using [hlen])
      (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])
    simp only [Layout.msgOff, ← Nat.add_assoc]; exact this
  rw [hsi₈, hb₈.rbx, h8] at c
  have hsub : ∀ r ∈ [(⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ : Region)], ∃ R ∈ wch p S sig kp (σ.gpr .rsp) stk,
      Region.Sub r R := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨sig, p.len * p.n⟩, by simp [wch], Offset.sub_base _ (by omega_using [hlen])⟩
  refine ⟨hb₈.ofFrame c.rd c.wr (fun g hg' => by
      rw [c.gpr g (base_regs_ne hg') (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl <;> decide)])
      c.frame hsub (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hE.dsig (o := i * p.n) (l := p.n) (a := 2400) (m := 48) (by omega_using [hlen])
          (by rw [oSigTmp_eq]; decide)).symm),
    fun g h₁ h₂ h₃ => by rw [c.gpr g h₁ h₂, hg g h₁ h₃], ?_, by rw [← hm₈]; exact c.frame⟩
  have hsrc : at' S (Layout.laneA k + p.n + 32) = S + BitVec.ofNat 64 (Layout.laneA k + (L p).msgOff) := by
    simp only [Layout.msgOff, Nat.add_assoc]
  by_cases hc : P
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    exact bytesAt_ext fun q hq => by rw [c.bytes q hq, decide_eq_true hc, ite_eq_left_of_eq_true _ _ (eq_self true), hm₈, hsrc]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact bytesAt_ext fun q hq => by rw [c.bytes q hq, decide_eq_false hc, hm₈]; rfl

/-- The value chain `i` of lane `k` holds after `j` steps. -/
abbrev cv (p : Params) (skSeed pkSeed a16 : List Byte) (kp k i j : Nat) : List Byte :=
  wotsChainAt p skSeed pkSeed a16 (kp + k) i j

/-- Whether the signature's key pair is one of the four. -/
abbrev InR (kp idx : Nat) : Prop := kp ≤ idx ∧ idx < kp + 4

theorem ea_digit (s : State) {i : Nat} (hb : s.gpr .rbx = S) (hi : s.gpr .r13 = BitVec.ofNat 64 i) :
    s.ea Wots.digitOp = at' S (Layout.oDigits + i) := by
  simp only [State.ea, Wots.digitOp, hb, hi, ofInt_nat, BitVec.mul_one]
  rw [ofNat_add', Nat.add_comm]

/-- The capture at step `j` of chain `i`: the signature's chain `i` gets
lane `k`'s value if `kp + k = idx` and `j` is digit `i`. -/
theorem capture_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i j : Nat} (hi : i < p.len)
    (hj : j < 16) {t : State} (hb : Base hE t) (hr13 : t.gpr .r13 = BitVec.ofNat 64 i)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 j) (hl : ∀ k < 4, la p t.mem S k 32 p.n = cv p skSeed pkSeed a16 kp k i j) :
    WP isa (.block (Wots.capture (L p))) t (fun t' => Base hE t' ∧
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .rdi → t'.gpr g = t.gpr g) ∧
      sigC p t'.mem sig i = (if InR kp idx ∧ j = digitAt σ.mem S i then
        wotsChainAt p skSeed pkSeed a16 idx i j else sigC p t.mem sig i) ∧
      Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem t'.mem) := by
  have hn := hz.n32
  have hlen : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  have hdig := hE.dig i hi
  have hlt : Layout.oDigits + i + 1 ≤ 65536 := by rw [oDigits_eq]; have := hz.len; omega_using [hi, this, hn]
  simp only [Wots.capture, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_movzx8 (a := at' S (Layout.oDigits + i)) (ea_digit t hb.rbx hr13) (hE.inScr' hb.rd hb.wr hlt)
    fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_xor fun t₃ u₃ => wp_mov fun t₄ u₄ => ?_
  let D : BitVec 64 := (σ.mem (at' S (Layout.oDigits + i))).setWidth 64
  have hD : D.toNat = digitAt σ.mem S i := by
    simp only [D, digitAt, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))
  have hg₄ : ∀ g, g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → t₄.gpr g = t.gpr g := fun g h₁ h₂ h₃ => by
    rw [u₄.other _ h₃, u₃.other _ h₂, u₂.other _ h₂, u₁.other _ h₁]
  have hdx : t₄.gpr .rdx = BitVec.ofNat 64 j ^^^ D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide), hbp,
      hb.digit hz hi]
  refine mulN_ok hz.nv (r := .rsi) (tmp := .rax) (x := i) (by decide) (by rw [u₄.gpr, u₃.other _ (by decide),
    u₂.other _ (by decide), u₁.other _ (by decide), hr13]) fun t₅ h₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_add fun t₆ u₆ => ?_
  have hm₆ : t₆.mem = t.mem := by rw [u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg₆ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → t₆.gpr g = t.gpr g := fun g h₀ h₁ h₂ h₃ => by
    rw [u₆.other _ h₃, g₅ _ h₃ h₀, hg₄ _ h₁ h₂ h₃]
  have hb₆ : Base hE t₆ := hb.regs hm₆ (by rw [u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) fun g h' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl | rfl <;> exact hg₆ _ (by decide) (by decide) (by decide) (by decide)
  have hsi : t₆.gpr .rsi = sig + BitVec.ofNat 64 (i * p.n) := by
    rw [u₆.gpr, h₅, u₆.other _ (by decide) |>.symm.trans (u₆.other _ (by decide)), g₅ _ (by decide) (by decide),
      hg₄ _ (by decide) (by decide) (by decide), hb.r15, BitVec.add_comm]
  have hdx₆ : t₆.gpr .rdx = BitVec.ofNat 64 j ^^^ D := by
    rw [u₆.other _ (by decide), g₅ _ (by decide) (by decide), hdx]
  have hD32 : D.toNat < 2 ^ 32 := by rw [hD]; omega_using [hdig]
  refine WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdi → u.gpr g = t₆.gpr g) ∧ (∀ k < 4, la p u.mem S k 32 p.n = la p t.mem S k 32 p.n) ∧
      sigC p u.mem sig i = (if ∃ k < K, kp + k = idx ∧ j = D.toNat then wotsChainAt p skSeed pkSeed a16 idx i j
        else sigC p t.mem sig i) ∧ Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem u.mem)
    ⟨hb₆, fun _ _ _ _ => rfl, fun k _ => by rw [hm₆], by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun ⟨k, hk, _⟩ => absurd hk (by omega_using []))), hm₆],
      by rw [hm₆]; exact Frame.refl _ _⟩ fun K hK u hu => ?_) fun u hu => ?_
  · refine WP.mono (capLane_ok hE hz (D := D) (i := i) (j := j) hK hi (by omega_using [hj]) hD32 hu.1
      (by rw [hu.2.1 _ (by decide) (by decide) (by decide), hdx₆])
      (by rw [hu.2.1 _ (by decide) (by decide) (by decide), hsi])) fun u' hu' => ?_
    have hkeep : ∀ k < 4, la p u'.mem S k 32 p.n = la p u.mem S k 32 p.n := fun k hk =>
      bytesAt_frame hu'.2.2.2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hE.dsig (o := i * p.n) (l := p.n) (a := Layout.laneA k + p.n + 32) (m := p.n) (by omega_using [hlen])
          (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])).symm) (by omega_using [hn])
    refine ⟨hu'.1, fun g h₁ h₂ h₃ => by rw [hu'.2.1 g h₁ h₂ h₃, hu.2.1 g h₁ h₂ h₃],
      fun k hk => by rw [hkeep k hk, hu.2.2.1 k hk], ?_, hu.2.2.2.2.trans hu'.2.2.2⟩
    rw [hu'.2.2.1]
    by_cases c : kp + K = idx ∧ j = D.toNat
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c), ite_eq_left_of_eq_true _ _ (eq_true ⟨K, by omega_using [], c⟩),
        hu.2.2.1 K hK, hl K hK, cv, c.1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c), hu.2.2.2.1]
      have e : (∃ k < K + 1, kp + k = idx ∧ j = D.toNat) ↔ (∃ k < K, kp + k = idx ∧ j = D.toNat) :=
        ⟨fun ⟨k, hk, h⟩ => ⟨k, by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | h'
          · exact h'
          · subst h'; exact absurd h c, h⟩, fun ⟨k, hk, h⟩ => ⟨k, by omega_using [hk], h⟩⟩
      simp only [e]
  · refine ⟨hu.1, fun g h₀ h₁ h₂ h₃ h₄ => by rw [hu.2.1 g h₀ h₁ h₄, hg₆ g h₀ h₁ h₂ h₃], ?_, hu.2.2.2.2⟩
    rw [hu.2.2.2.1]
    have e : (∃ k < 4, kp + k = idx ∧ j = D.toNat) ↔ (InR kp idx ∧ j = digitAt σ.mem S i) := by
      rw [hD]
      exact ⟨fun ⟨k, hk, h₁, h₂⟩ => ⟨⟨by omega_using [h₁], by omega_using [h₁, hk]⟩, h₂⟩,
        fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨idx - kp, by omega_using [h₁, h₂], by omega_using [h₁], h₃⟩⟩
    simp only [e]

end VG.Proof.SlhDsa.X86_64.Wots4

/-! ## `wotsLeaves4`, the loops

A chain of the four lanes (`chainBody`): the private key values, `PRF` of
them, the steps (`stepBody`, a loop of 15 `F`s with the captures), the last
capture, and the chain ends to the lanes of `B` (`toB`); and the loop of the
`len` chains. Within a chain, the memory changes only in `AZ`: the lanes
of `A` after their `a16`, `thash4`'s work, the stack, and the chain of the
signature.
-/

namespace VG.Proof.SlhDsa.X86_64.Wots4

open VG VG.X86_64 VG.X86_64.Steps
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.SlhDsa (fld)

variable {p : Params} {stk : Nat} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-- What a chain changes, but the lanes of `B`. -/
def AZ (p : Params) (S sig sp : Addr) (stk i : Nat) : List Region :=
  (List.range 4).map (laneR p S) ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp stk, ⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩]

theorem laneR_AZ {k : Nat} (hk : k < 4) (S sig sp : Addr) (stk i : Nat) : laneR p S k ∈ AZ p S sig sp stk i := by
  simp only [AZ, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl ⟨k, hk, rfl⟩

/-- Frames of lists within `AZ`. -/
theorem frame_AZ {rs : List Region} {m m' : Mem} {S sig sp : Addr} {stk i : Nat} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ R ∈ AZ p S sig sp stk i, Region.Sub r R) : Frame (AZ p S sig sp stk i) m m' := hf.sub hs

theorem sub_AZ_lane {S sig sp : Addr} {stk i k o l : Nat} (hk : k < 4) (h₁ : 16 ≤ o) (h₂ : o + l ≤ p.n + 32) :
    ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + o), l⟩ : Region)], ∃ R ∈ AZ p S sig sp stk i, Region.Sub r R := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, laneR_AZ hk S sig sp stk i, la_sub h₁ h₂⟩

theorem sub_AZ_lanes {S sig sp : Addr} {stk i : Nat} :
    ∀ r ∈ (List.range 4).map (laneR p S), ∃ R ∈ AZ p S sig sp stk i, Region.Sub r R := by
  intro r hr
  exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

theorem sub_AZ_sig {S sig sp : Addr} {stk i : Nat} :
    ∀ r ∈ [(⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ : Region)], ∃ R ∈ AZ p S sig sp stk i, Region.Sub r R := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, by simp [AZ], fun _ h => h⟩

/-- `thash4` on `A` changes only `AZ`. -/
theorem sub_AZ_t4 (hz : Sz p) {S sig sp : Addr} {stk stk' i : Nat} (hs : stk = 8 + stk') :
    ∀ r ∈ wotsT4Changes p.n S 3296 128 sp stk', ∃ R ∈ AZ p S sig sp stk i, Region.Sub r R := by
  have hn := hz.n32
  intro r hr
  simp only [wotsT4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · refine ⟨_, laneR_AZ hj S sig sp stk i, ?_⟩
    have e := la_sub (p := p) (S := S) (k := j) (o := 32) (l := p.n) (by omega_using []) (by omega_using [])
    rwa [laneA_eq, show 3296 + 128 * j + p.n + 32 = 3296 + j * 128 + p.n + 32 by omega_using []] at e
  · exact ⟨_, by simp [AZ], fun _ h => h⟩
  · exact ⟨_, by simp [AZ], fun _ h => h⟩
  · subst hs; exact ⟨_, by simp [AZ], fun _ h => h⟩

/-- A range of the lanes of `B` is apart from `AZ`. -/
theorem B_AZ (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {a l i : Nat} (h₁ : 3808 ≤ a)
    (h₂ : a + l ≤ 12640) (hi : i < p.len) : ∀ r ∈ AZ p S sig (σ.gpr .rsp) stk i, Region.Disjoint ⟨at' S a, l⟩ r := by
  have hn := hz.n32
  have hlen : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  intro r hr
  simp only [AZ, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
  · exact Entry.dscr (Or.inr (by rw [laneA_eq]; omega_using [hk, hn, h₁])) (by omega_using [h₂])
      (by rw [laneA_eq]; omega_using [hk, hn])
  · exact Offset.disjoint_base S (by omega_using [h₁]) (by omega_using [h₂])
  · exact Entry.dscr (Or.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
  · exact (hE.dstk (by omega_using [h₂])).symm
  · exact (hE.dsig (o := i * p.n) (l := p.n) (by omega_using [hlen]) (by rw [oSigTmp_eq]; omega_using [h₂])).symm

/-- Another chain of the signature is apart from `AZ`. -/
theorem sig_AZ (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i i' : Nat} (hi : i < p.len)
    (hi' : i' < p.len) (hne : i' ≠ i) :
    ∀ r ∈ AZ p S sig (σ.gpr .rsp) stk i, Region.Disjoint ⟨sig + BitVec.ofNat 64 (i' * p.n), p.n⟩ r := by
  have hn := hz.n32
  have hl : ∀ {x}, x < p.len → x * p.n + p.n ≤ p.len * p.n := fun {x} hx => by
    have := Nat.mul_le_mul_right p.n (show x + 1 ≤ p.len by omega_using [hx]); rwa [Nat.add_mul, Nat.one_mul] at this
  have hfit := hE.reg.out_fit; simp only at hfit
  intro r hr
  simp only [AZ, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
  · exact hE.dsig (hl hi') (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])
  · exact (hE.reg.out_scr.sub_left (Offset.sub_base sig (hl hi'))).sub_right
      (Region.sub_prefix (by rw [oSigTmp_eq]; decide))
  · exact hE.dsig (hl hi') (by rw [oSigTmp_eq]; decide)
  · exact (hE.reg.stk_out.sub_right (Offset.sub_base sig (hl hi'))).symm
  · have hc : i' * p.n + p.n ≤ i * p.n ∨ i * p.n + p.n ≤ i' * p.n := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · left; have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ i by omega_using [h])
        rwa [Nat.add_mul, Nat.one_mul] at this
      · right; have := Nat.mul_le_mul_right p.n (show i + 1 ≤ i' by omega_using [h])
        rwa [Nat.add_mul, Nat.one_mul] at this
    exact Offset.disjoint sig hc (by omega_using [hl hi', hfit]) (by omega_using [hl hi, hfit])

/-! ## Updates of a lane's address -/

theorem LaneA.set16 (hz : Sz p) {m m' : Mem} {S : Addr} {k ty κ c h ty' : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneA p m S k ty κ c h M) (hf : Frame [⟨at' S (Layout.laneA k + p.n + 16), 4⟩] m m')
    (hv : la p m' S k 16 4 = toByte ty' 4) : LaneA p m' S k ty' κ c h M := by
  have hn := hz.n32
  have K := fun {o₂ l₂ : Nat} (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32) (h : 16 + 4 ≤ o₂) =>
    la_keep hz (o₁ := 16) (l₁ := 4) (o₂ := o₂) (l₂ := l₂) hf hk hk (by omega_using []) (by omega_using [])
      h₂ h₂' (Or.inr (Or.inl h))
  exact ⟨hv, by rw [K (by omega_using []) (by omega_using [hn]) (by omega_using []), hl.f20],
    by rw [K (by omega_using []) (by omega_using [hn]) (by omega_using []), hl.f24],
    by rw [K (by omega_using []) (by omega_using [hn]) (by omega_using []), hl.f28],
    by rw [K (by omega_using []) (by omega_using []) (by omega_using []), hl.msg]⟩

theorem LaneA.set28 (hz : Sz p) {m m' : Mem} {S : Addr} {k ty κ c h h' : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneA p m S k ty κ c h M) (hf : Frame [⟨at' S (Layout.laneA k + p.n + 28), 4⟩] m m')
    (hv : la p m' S k 28 4 = toByte h' 4) : LaneA p m' S k ty κ c h' M := by
  have hn := hz.n32
  have K := fun {o₂ l₂ : Nat} (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ p.n + 32) (h : 28 + 4 ≤ o₂ ∨ o₂ + l₂ ≤ 28) =>
    la_keep hz (o₁ := 28) (l₁ := 4) (o₂ := o₂) (l₂ := l₂) hf hk hk (by omega_using []) (by omega_using [hn])
      h₂ h₂' (Or.inr h)
  exact ⟨by rw [K (by omega_using []) (by omega_using [hn]) (Or.inr (by omega_using [])), hl.f16],
    by rw [K (by omega_using []) (by omega_using [hn]) (Or.inr (by omega_using [])), hl.f20],
    by rw [K (by omega_using []) (by omega_using [hn]) (Or.inr (by omega_using [])), hl.f24], hv,
    by rw [K (by omega_using []) (by omega_using []) (Or.inl (by omega_using [])), hl.msg]⟩

/-- A frame within lane `k` keeps the other lanes. -/
theorem LaneA.keep' (hz : Sz p) {m m' : Mem} {S : Addr} {k k' ty κ c h o l : Nat} {M : List Byte}
    (hl : LaneA p m S k' ty κ c h M) (hf : Frame [⟨at' S (Layout.laneA k + p.n + o), l⟩] m m') (hk : k < 4)
    (hk' : k' < 4) (hne : k ≠ k') (h₁ : 16 ≤ o) (h₂ : o + l ≤ p.n + 32) : LaneA p m' S k' ty κ c h M :=
  hl.keep hz (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, la_sub h₁ h₂⟩) hk hk' hne

/-- `thash4` on `A` leaves the addresses of the lanes. -/
theorem t4_fields (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {stk' : Nat} (hs : stk = 8 + stk')
    {m m' : Mem} (hf : Frame (wotsT4Changes p.n S 3296 128 (σ.gpr .rsp) stk') m m') {k o : Nat} (hk : k < 4) (h₁ : 16 ≤ o)
    (h₂ : o ≤ 28) : la p m' S k o 4 = la p m S k o 4 := by
  have hn := hz.n32
  refine bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [wotsT4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · refine Entry.dscr ?_ (by rw [laneA_eq]; omega_using [hk, hn, h₂]) (by omega_using [hj, hn])
    rw [laneA_eq]
    rcases Nat.lt_or_ge j k with h | h
    · right; omega_using [h, h₁, hn]
    · rcases Nat.lt_or_ge k j with h' | h'
      · left; omega_using [h', h₂, hn]
      · left; have : j = k := by omega_using [h, h']
        subst this; omega_using [h₂]
  · exact Offset.disjoint_base S (by rw [laneA_eq]; omega_using []) (by rw [laneA_eq]; omega_using [hk, hn, h₂])
  · exact Entry.dscr (Or.inr (by rw [laneA_eq]; omega_using [])) (by rw [laneA_eq]; omega_using [hk, hn, h₂]) (by decide)
  · subst hs; exact (hE.dstk (by rw [laneA_eq]; omega_using [hk, hn, h₂])).symm

theorem nm_setField (b : Reg) (d v : Nat) : (setField b d v).all (fun i => !loadsMxcsr i) = true := rfl
theorem nm_setFieldR (b : Reg) (d : Nat) (r : Reg) : (setFieldR b d r).all (fun i => !loadsMxcsr i) = true := rfl
theorem nm_copyWords (t : Reg) (d₂ : Nat) (s : Reg) (d₁ w : Nat) :
    (copyWords t d₂ s d₁ w).all (fun i => !loadsMxcsr i) = true := by
  simp [copyWords, List.all_flatMap, loadsMxcsr]
theorem nm_mulN (n : Nat) (r t : Reg) : (Wots.mulN n r t).all (fun i => !loadsMxcsr i) = true := by
  unfold Wots.mulN; split <;> rfl
theorem nm_captureLane (L : Layout) (k : Nat) : (Wots.captureLane L k).all (fun i => !loadsMxcsr i) = true := by
  simp [Wots.captureLane, List.all_flatMap, loadsMxcsr]
theorem nm_flatMap {f : Nat → List Instr} (K : Nat) (h : ∀ k, (f k).all (fun i => !loadsMxcsr i) = true) :
    ((List.range K).flatMap f).all (fun i => !loadsMxcsr i) = true := by
  simp only [List.all_flatMap, List.all_eq_true, List.mem_range]
  exact fun k _ => List.all_eq_true.mp (h k)

theorem Frame.trans_sub {rs : List Region} {m₁ m₂ m₃ : Mem} {S sig sp : Addr} {stk i : Nat}
    (h₁ : Frame rs m₁ m₂) {rs' : List Region} (h₂ : Frame rs' m₂ m₃)
    (hs : ∀ r ∈ rs', ∃ R ∈ AZ p S sig sp stk i, Region.Sub r R) (hrs : rs = (List.range 4).map (laneR p S)) :
    Frame (AZ p S sig sp stk i) m₁ m₃ := by
  subst hrs; exact (frame_AZ h₁ sub_AZ_lanes).trans (frame_AZ h₂ hs)

/-- The signature's chains are apart from the lanes of `A` and from what `thash4` changes. -/
theorem sig_lanes (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {m m' : Mem} {i : Nat}
    (hi : i < p.len) (hf : Frame ((List.range 4).map (laneR p S)) m m') : sigC p m' sig i = sigC p m sig i := by
  have hn := hz.n32
  have hl : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
  exact hE.dsig hl (by rw [laneA_eq, oSigTmp_eq]; have := List.mem_range.mp hk; omega_using [this, hn])

theorem sig_t4 (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {stk' : Nat} (hs : stk = 8 + stk')
    {o st : Nat} (hlo : Lanes o st) {m m' : Mem} {i : Nat} (hi : i < p.len)
    (hf : Frame (wotsT4Changes p.n S o st (σ.gpr .rsp) stk') m m') : sigC p m' sig i = sigC p m sig i := by
  have hn := hz.n32
  have hl : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  simp only [wotsT4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · exact hE.dsig hl (by rw [oSigTmp_eq]; rcases hlo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega_using [hj, hn])
  · exact (hE.reg.out_scr.sub_left (Offset.sub_base sig hl)).sub_right
      (Region.sub_prefix (by rw [oSigTmp_eq]; decide))
  · exact hE.dsig hl (by rw [oSigTmp_eq]; decide)
  · subst hs; exact (hE.reg.stk_out.sub_right (Offset.sub_base sig hl)).symm

/-! ## The head of a chain -/

/-- Before step `j` of chain `i`, from the memory `m₀` at the chain's start. -/
structure StepInv (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (m₀ : Mem) (i j : Nat) (t : State) : Prop where
  base : Base hE t
  mx : t.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  rbp : t.gpr .rbp = BitVec.ofNat 64 j
  lanes : ∀ k < 4, ∃ h, LaneA p t.mem S k WOTS_HASH (kp + k) i h (cv p skSeed pkSeed a16 kp k i j)
  fr : Frame (AZ p S sig (σ.gpr .rsp) stk i) m₀ t.mem
  sigc : sigC p t.mem sig i = if InR kp idx ∧ digitAt σ.mem S i < j then
    wotsChainAt p skSeed pkSeed a16 idx i (digitAt σ.mem S i) else sigC p m₀ sig i

/-- The private key values' addresses and messages, the type `WOTS_PRF`. -/
theorem prfs_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i : Nat} (hi : i < p.len)
    {t₀ : State} (hb : Base hE t₀) (hr13 : t₀.gpr .r13 = BitVec.ofNat 64 i)
    (h20 : ∀ k < 4, la p t₀.mem S k 20 4 = toByte (kp + k) 4) :
    WP isa (.block (Wots.prfLanes (L p))) t₀ (fun t => (Base hE t ∧ (∀ g, g ≠ .rax → t.gpr g = t₀.gpr g) ∧
      (∀ k < 4, la p t.mem S k 20 4 = toByte (kp + k) 4) ∧ (∀ k < 4, LaneA p t.mem S k WOTS_PRF (kp + k) i 0 skSeed) ∧
      Frame ((List.range 4).map (laneR p S)) t₀.mem t.mem) ∧ t.mxcsr = t₀.mxcsr) := by
  have hn := hz.n32
  have hi32 : i < 2 ^ 32 := by have := hz.len; omega_using [hi, this, hn]
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine wp_mx (nm_flatMap 4 fun k => by
    simp only [Wots.prfLane, List.all_append, nm_setField, nm_setFieldR, nm_copyWords, Bool.and_self]) ?_
  refine WP.mono (wp_range_flatMap 4 (P := fun j t => Base hE t ∧ (∀ g, g ≠ .rax → t.gpr g = t₀.gpr g) ∧
      (∀ k < 4, la p t.mem S k 20 4 = toByte (kp + k) 4) ∧ (∀ k < j, LaneA p t.mem S k WOTS_PRF (kp + k) i 0 skSeed) ∧
      Frame ((List.range 4).map (laneR p S)) t₀.mem t.mem)
    ⟨hb, fun _ _ => rfl, h20, fun _ h => absurd h (by omega_using []), Frame.refl _ _⟩ fun j hj t ht => ?_)
    fun t₁ ht₁ hmx₁ => ⟨ht₁, hmx₁⟩
  · refine WP.mono (prfLane_ok hE hz hj hi32 ht.1 (by rw [ht.2.1 _ (by decide), hr13])) fun t' h => ?_
    obtain ⟨b', g', y16, y24, y28, ym, y20, f'⟩ := h
    refine ⟨b', fun g hg => by rw [g' g hg, ht.2.1 g hg], fun k hk => ?_, fun k hk => ?_,
      ht.2.2.2.2.trans (f'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hlR hj)⟩
    · by_cases e : k = j
      · subst e; rw [y20, ht.2.2.1 k hk]
      · rw [la_keep hz (o₁ := 16) (f'.sub fun r hr => ⟨_, hr, fun _ h => h⟩) hj hk (by omega_using [])
          (by omega_using []) (by omega_using []) (by omega_using [hn]) (Or.inl (Ne.symm e)), ht.2.2.1 k hk]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact (ht.2.2.2.1 k hk').keep hz f' hj (by omega_using [hk', hj]) (by omega_using [hk'])
      · exact ⟨y16, by rw [y20, ht.2.2.1 _ hj], y24, y28, ym⟩

/-- The private key values, `PRF` of them, and the type `WOTS_HASH`. -/
theorem chainHead_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) {i : Nat} (hi : i < p.len) {t₀ : State} (hb : Base hE t₀)
    (hmx : t₀.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10) (hr13 : t₀.gpr .r13 = BitVec.ofNat 64 i)
    (h20 : ∀ k < 4, la p t₀.mem S k 20 4 = toByte (kp + k) 4) {X : Prog isa} {Q : State → Prop}
    (kk : ∀ t, StepInv hE t₀.mem i 0 t → WP isa X t Q) :
    WP isa (.seq (.block (Wots.prfLanes (L p))) (.seq (thashCall (L p) name T.code Layout.oA Layout.strideA
      (2 * (L p).n + 32)) (.seq (.block (Wots.hashType (L p))) X))) t₀ Q := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have h16 := a16_length (hE.env)
  have hi32 : i < 2 ^ 32 := by have := hz.len; omega_using [hi, this, hn]
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine WP.seq (WP.mono (prfs_ok hE hz hi hb hr13 h20) fun t₁ ⟨ht₁, hmx₁⟩ => ?_)
  -- The call: `PRF`.
  obtain ⟨hb₁, hg₁, _, hl₁, hf₁⟩ := ht₁
  refine WP.seq (tcall_ok hE hz T name hs (o := 3296) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb₁
    fun t₂ hb₂ hg₂ hout hf₂ hmx₂ => ?_)
  have hl₂ : ∀ k < 4, LaneA p t₂.mem S k WOTS_PRF (kp + k) i 0 (cv p skSeed pkSeed a16 kp k i 0) := fun k hk => by
    have l := hl₁ k hk
    refine ⟨by rw [t4_fields hE hz hs hf₂ hk (by decide) (by decide)]; exact l.f16,
      by rw [t4_fields hE hz hs hf₂ hk (by decide) (by decide)]; exact l.f20,
      by rw [t4_fields hE hz hs hf₂ hk (by decide) (by decide)]; exact l.f24,
      by rw [t4_fields hE hz hs hf₂ hk (by decide) (by decide)]; exact l.f28, ?_⟩
    have e := hout k hk
    rw [show 3296 + k * 128 = Layout.laneA k by rw [laneA_eq]; omega_using [], laneA_msg (hb₁.env hz) hk l] at e
    rw [cv, chainAt_zero hz h16 (by omega_using [hkp, hk])]
    exact e
  -- The type `WOTS_HASH`, and `j ← 0`.
  refine WP.seq (wp_mx (by
    simp only [Wots.hashType, List.all_append, nm_flatMap 4 fun k => nm_setField _ _ _, Bool.true_and]; rfl) ?_)
  simp only [Wots.hashType]
  refine WP.block_append (WP.mono (wp_range_flatMap 4 (P := fun j t => Base hE t ∧
      (∀ g, g ≠ .rax → t.gpr g = t₂.gpr g) ∧
      (∀ k < 4, (k < j → LaneA p t.mem S k WOTS_HASH (kp + k) i 0 (cv p skSeed pkSeed a16 kp k i 0)) ∧
        (j ≤ k → LaneA p t.mem S k WOTS_PRF (kp + k) i 0 (cv p skSeed pkSeed a16 kp k i 0))) ∧
      Frame ((List.range 4).map (laneR p S)) t₂.mem t.mem)
    ⟨hb₂, fun _ _ => rfl, fun k hk => ⟨fun h => absurd h (by omega_using []), fun _ => hl₂ k hk⟩, Frame.refl _ _⟩
    fun j hj t ht => ?_) fun t₃ ht₃ => ?_)
  · simp only [Layout.adrsOff]
    rw [← List.append_nil (setField .rbx (Layout.laneA j + p.n + 16) 0)]
    refine setField_base hE ht.1 (tailA_of hz hj (by decide) (by decide)) (by decide) fun t' b' g' y' f' => ?_
    refine WP.block_nil ⟨b', fun g hg => by rw [g' g hg, ht.2.1 g hg], fun k hk => ⟨fun hk' => ?_, fun hk' => ?_⟩,
      ht.2.2.2.trans (frame_cat f' (Frame.refl [] _) |>.sub fun r hr => by
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, hlR hj, la_sub (by omega_using []) (by omega_using [hn])⟩)⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
      · exact ((ht.2.2.1 k hk).1 h').keep' hz f' hj hk (by omega_using [h']) (by omega_using []) (by omega_using [hn])
      · exact ((ht.2.2.1 k hk).2 (Nat.le_refl _)).set16 hz hk f' y'
    · exact ((ht.2.2.1 k hk).2 (by omega_using [hk'])).keep' hz f' hj hk (by omega_using [hk']) (by omega_using [])
        (by omega_using [hn])
  refine wp_mov32i fun t₄ u₄ => WP.block_nil fun hmx₄ => kk t₄ ?_
  obtain ⟨hb₃, hg₃, hl₃, hf₃⟩ := ht₃
  have hf : Frame ((List.range 4).map (laneR p S)) t₃.mem t₄.mem := by rw [u₄.mem]; exact Frame.refl _ _
  refine ⟨hb₃.regs u₄.mem u₄.rd u₄.wr fun g hg => u₄.other g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hmx₄, hmx₂, hmx₁, hmx],
    by rw [u₄.other _ (by decide), hg₃ _ (by decide), hg₂ _ (by simp [calleeSaved]), hg₁ _ (by decide), hr13],
    by rw [u₄.gpr]; rfl, fun k hk => ⟨0, by rw [u₄.mem]; exact (hl₃ k hk).1 hk⟩,
    ((Frame.trans_sub hf₁ hf₂ (sub_AZ_t4 hz hs) rfl).trans (frame_AZ hf₃ sub_AZ_lanes)).trans
      (frame_AZ hf sub_AZ_lanes), ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => absurd h.2 (by omega_using []))),
    sig_lanes hE hz hi hf, sig_lanes hE hz hi hf₃, sig_t4 hE hz hs (Or.inl ⟨rfl, rfl⟩) hi hf₂, sig_lanes hE hz hi hf₁]

/-! ## A step of the chains -/

theorem zf_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => h ((ofNat_eq_iff ha hb).mp (by
      have := congrArg (· + BitVec.ofNat 64 b) e
      rw [BitVec.sub_add_cancel] at this; exact this.trans (by simp)))
    rw [decide_eq_false h]; simpa using this

theorem sig_step (P : Prop) [Decidable P] {d j : Nat} (f : Nat → List Byte) (Y : List Byte) :
    (if P ∧ j = d then f j else if P ∧ d < j then f d else Y) = if P ∧ d < j + 1 then f d else Y := by
  by_cases hP : P
  · by_cases h₁ : j = d
    · subst h₁; simp [hP]
    · by_cases h₂ : d < j
      · simp [hP, h₁, h₂, show d < j + 1 by omega_using [h₂]]
      · simp [hP, h₁, h₂, show ¬ d < j + 1 by omega_using [h₁, h₂]]
  · simp [hP]

/-- A step's capture and hash addresses `j`. -/
theorem stepPre_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {m₀ : Mem} {i j : Nat}
    (hi : i < p.len) (hj : j < 15) {t : State} (h : StepInv hE m₀ i j t) :
    WP isa (.block (Wots.capture (L p) ++ Wots.hashAdrs (L p))) t (fun t₂ => ∃ t₁ : State,
      (Base hE t₁ ∧ (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .rdi → t₁.gpr g = t.gpr g) ∧
        sigC p t₁.mem sig i = (if InR kp idx ∧ j = digitAt σ.mem S i then
          wotsChainAt p skSeed pkSeed a16 idx i j else sigC p t.mem sig i) ∧
        Frame [⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩] t.mem t₁.mem) ∧
      (Base hE t₂ ∧ (∀ g, g ≠ .rax → t₂.gpr g = t₁.gpr g) ∧
        (∀ k < 4, (k < 4 → LaneA p t₂.mem S k WOTS_HASH (kp + k) i j (cv p skSeed pkSeed a16 kp k i j)) ∧
          (4 ≤ k → ∃ h', LaneA p t₂.mem S k WOTS_HASH (kp + k) i h' (cv p skSeed pkSeed a16 kp k i j))) ∧
        Frame ((List.range 4).map (laneR p S)) t₁.mem t₂.mem) ∧ t₂.mxcsr = t.mxcsr) := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have h16 := a16_length (hE.env)
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine wp_mx (by
    simp only [Wots.capture, Wots.hashAdrs, List.all_append, nm_mulN, nm_flatMap 4 (nm_captureLane _),
      nm_flatMap 4 fun k => nm_setFieldR _ _ _]
    rfl) ?_
  refine WP.block_append (WP.mono (capture_ok hE hz hi (by omega_using [hj]) h.base h.r13 h.rbp fun k hk => by
      obtain ⟨_, l⟩ := h.lanes k hk; exact l.msg) fun t₁ ⟨hb₁, hg₁, hs₁, hf₁⟩ => ?_)
  have hl₁ : ∀ k < 4, ∃ h', LaneA p t₁.mem S k WOTS_HASH (kp + k) i h' (cv p skSeed pkSeed a16 kp k i j) := by
    intro k hk
    obtain ⟨h', l⟩ := h.lanes k hk
    have hlen : i * p.n + p.n ≤ p.len * p.n := by
      have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
    have e : ∀ o l, 16 ≤ o → o + l ≤ p.n + 32 → la p t₁.mem S k o l = la p t.mem S k o l := fun o l h₁ h₂ =>
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hE.dsig (o := i * p.n) (l := p.n) (by omega_using [hlen])
          (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn, h₂])).symm) (by omega_using [h₂, hn])
    exact ⟨h', by rw [e 16 4 (by decide) (by omega_using [hn])]; exact l.f16,
      by rw [e 20 4 (by decide) (by omega_using [hn])]; exact l.f20, by rw [e 24 4 (by decide) (by omega_using [hn])]; exact l.f24,
      by rw [e 28 4 (by decide) (by omega_using [hn])]; exact l.f28, by rw [e 32 p.n (by decide) (by omega_using [])]; exact l.msg⟩
  have hbp₁ : t₁.gpr .rbp = BitVec.ofNat 64 j := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]
  have hj32 : (t₁.gpr .rbp).toNat < 2 ^ 32 := by rw [hbp₁]; exact toNat_lt_of (by omega_using [hj])
  have hjv : (t₁.gpr .rbp).toNat = j := by rw [hbp₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])]
  simp only [Wots.hashAdrs]
  refine WP.mono (wp_range_flatMap 4 (P := fun j' u => Base hE u ∧ (∀ g, g ≠ .rax → u.gpr g = t₁.gpr g) ∧
      (∀ k < 4, (k < j' → LaneA p u.mem S k WOTS_HASH (kp + k) i j (cv p skSeed pkSeed a16 kp k i j)) ∧
        (j' ≤ k → ∃ h', LaneA p u.mem S k WOTS_HASH (kp + k) i h' (cv p skSeed pkSeed a16 kp k i j))) ∧
      Frame ((List.range 4).map (laneR p S)) t₁.mem u.mem)
    ⟨hb₁, fun _ _ => rfl, fun k hk => ⟨fun h' => absurd h' (by omega_using []), fun _ => hl₁ k hk⟩, Frame.refl _ _⟩
    fun j' hj' u hu => ?_) fun t₂ ht₂ hmx₂ => ⟨t₁, ⟨hb₁, hg₁, hs₁, hf₁⟩, ht₂, hmx₂⟩
  · simp only [Layout.adrsOff]
    rw [← List.append_nil (setFieldR .rbx (Layout.laneA j' + p.n + 28) .rbp)]
    refine setFieldR_base hE hu.1 (tailA_of hz hj' (by decide) (by decide)) (by rw [hu.2.1 _ (by decide)]; exact hj32)
      fun u' b' g' y' f' => ?_
    rw [hu.2.1 _ (by decide), hjv] at y'
    refine WP.block_nil ⟨b', fun g hg => by rw [g' g hg, hu.2.1 g hg], fun k hk => ⟨fun hk' => ?_, fun hk' => ?_⟩,
      hu.2.2.2.trans (frame_cat f' (Frame.refl [] _) |>.sub fun r hr => by
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, hlR hj', la_sub (by omega_using []) (by omega_using [hn])⟩)⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
      · exact ((hu.2.2.1 k hk).1 h').keep' hz f' hj' hk (by omega_using [h']) (by omega_using []) (by omega_using [hn])
      · obtain ⟨_, l⟩ := (hu.2.2.1 k hk).2 (Nat.le_refl _)
        exact l.set28 hz hk f' y'
    · obtain ⟨h', l⟩ := (hu.2.2.1 k hk).2 (by omega_using [hk'])
      exact ⟨h', l.keep' hz f' hj' hk (by omega_using [hk']) (by omega_using []) (by omega_using [hn])⟩

/-- A step: the capture, the hash addresses `j`, `F`, and `j + 1`. -/
theorem step_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) {m₀ : Mem} {i j : Nat} (hi : i < p.len) (hj : j < 15) {t : State}
    (h : StepInv hE m₀ i j t) :
    WP isa (Wots.stepBody (L p) name T.code) t (fun t' => StepInv hE m₀ i (j + 1) t' ∧
      t'.zf = some (decide (j + 1 = 15))) := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have h16 := a16_length (hE.env)
  have hlR : ∀ {k : Nat}, k < 4 → laneR p S k ∈ (List.range 4).map (laneR p S) := fun hk =>
    List.mem_map.mpr ⟨_, List.mem_range.mpr hk, rfl⟩
  refine WP.seq (WP.mono (stepPre_ok hE hz hi hj h) fun t₂ ⟨t₁, ⟨hb₁, hg₁, hs₁, hf₁⟩, ht₂, hmx₂⟩ => ?_)
  have hbp₁ : t₁.gpr .rbp = BitVec.ofNat 64 j := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]
  obtain ⟨hb₂, hg₂, hl₂, hf₂⟩ := ht₂
  refine WP.seq (tcall_ok hE hz T name hs (o := 3296) (st := 128) (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩)
    (by omega_using []) (by have := hz.n8; omega_using [this]) (by omega_using [hn]) hb₂
    fun t₃ hb₃ hg₃ hout hf₃ hmx₃ => ?_)
  have hl₃ : ∀ k < 4, LaneA p t₃.mem S k WOTS_HASH (kp + k) i j (cv p skSeed pkSeed a16 kp k i (j + 1)) := fun k hk => by
    have l := (hl₂ k hk).1 hk
    refine ⟨by rw [t4_fields hE hz hs hf₃ hk (by decide) (by decide)]; exact l.f16,
      by rw [t4_fields hE hz hs hf₃ hk (by decide) (by decide)]; exact l.f20,
      by rw [t4_fields hE hz hs hf₃ hk (by decide) (by decide)]; exact l.f24,
      by rw [t4_fields hE hz hs hf₃ hk (by decide) (by decide)]; exact l.f28, ?_⟩
    have e := hout k hk
    rw [show 3296 + k * 128 = Layout.laneA k by rw [laneA_eq]; omega_using [], laneA_msg (hb₂.env hz) hk l] at e
    rw [cv, chainAt_succ hz h16]
    exact e
  refine wp_mx rfl ?_
  refine wp_addi fun t₄ u₄ => wp_cmpi fun t₅ g₅ m₅ rd₅ wr₅ _ zf₅ => WP.block_nil fun hmx₅ => ?_
  have hbp₄ : t₄.gpr .rbp = BitVec.ofNat 64 (j + 1) := by
    rw [u₄.gpr, hg₃ _ (by simp [calleeSaved]), hg₂ _ (by decide), hbp₁,
      show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from by decide, ← BitVec.ofNat_add]
  have hm₅ : t₅.mem = t₃.mem := by rw [m₅, u₄.mem]
  refine ⟨⟨hb₃.regs hm₅ (by rw [rd₅, u₄.rd]) (by rw [wr₅, u₄.wr]) fun g hg => by
      rw [g₅, u₄.other g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [hmx₅, hmx₃, hmx₂, h.mx],
    by rw [g₅, u₄.other _ (by decide), hg₃ _ (by simp [calleeSaved]), hg₂ _ (by decide),
      hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r13],
    by rw [g₅, hbp₄], fun k hk => ⟨j, by rw [hm₅]; exact hl₃ k hk⟩, ?_, ?_⟩, ?_⟩
  · rw [hm₅]
    exact ((h.fr.trans (frame_AZ hf₁ sub_AZ_sig)).trans (frame_AZ hf₂ sub_AZ_lanes)).trans (frame_AZ hf₃ (sub_AZ_t4 hz hs))
  · rw [hm₅, sig_t4 hE hz hs (Or.inl ⟨rfl, rfl⟩) hi hf₃, sig_lanes hE hz hi hf₂, hs₁, h.sigc]
    exact sig_step _ (fun x => wotsChainAt p skSeed pkSeed a16 idx i x) _
  · rw [zf₅, hbp₄, show BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 15 from by decide,
      zf_eq (by omega_using [hj]) (by decide)]

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  show s.zf.map (!·) = _; rw [h]; rfl

/-- The 15 steps of chain `i`. -/
theorem steps_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) {m₀ : Mem} {i : Nat} (hi : i < p.len) {t : State}
    (h : StepInv hE m₀ i 0 t) :
    WP isa (.loop (Wots.stepBody (L p) name T.code) .ne) t (StepInv hE m₀ i 15) := by
  refine WP.loop (M := isa) (Inv := fun (n : Nat) (u : State) => 1 ≤ n ∧ n ≤ 15 ∧ StepInv hE m₀ i (15 - n) u) (fun n u hu => ?_) 15 t
    ⟨by decide, by decide, by rw [Nat.sub_self]; exact h⟩
  obtain ⟨h₁, h₂, hu⟩ := hu
  refine WP.mono (step_ok hE hz T name hs hi (by omega_using [h₁]) hu) fun u' ⟨hu', hzf⟩ => ?_
  by_cases e : 15 - n + 1 = 15
  · rw [e] at hu'
    exact Or.inl ⟨by rw [eval_ne hzf, decide_eq_true e]; rfl, hu'⟩
  · refine Or.inr ⟨by rw [eval_ne hzf, decide_eq_false e]; rfl, n - 1, by omega_using [h₁],
      ⟨by omega_using [e, h₁, h₂], by omega_using [h₂], ?_⟩⟩
    rw [show 15 - (n - 1) = 15 - n + 1 by omega_using [h₁, h₂, e]]; exact hu'

/-! ## The ends of the chains to `B` -/

/-- Chain `i` of lane `k`'s message in `B`. -/
abbrev bm (p : Params) (m : Mem) (S : Addr) (k i : Nat) : List Byte :=
  bytesAt m (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n

theorem bm_fit (hz : Sz p) {k i : Nat} (_hk : k < 4) (hi : i < p.len) :
    Layout.laneB k + p.n + 32 + i * p.n + p.n ≤ Layout.laneB k + Layout.strideB := by
  have hl : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  rw [hz.len] at hl
  rw [strideB_eq]
  rcases hz.nv with e | e | e <;> rw [e] at hl ⊢ <;> omega_using [hl]

end VG.Proof.SlhDsa.X86_64.Wots4

/-! ## `wotsLeaves4`, one chain of the four lanes

The ends of chain `i` of the four lanes to their messages in `B` (`toB_ok`),
what holds before each chain (`ChainInv`: the ends of the chains before it
in `B`, the signature's chains before it captured), and a whole chain
(`chainBody_ok`).
-/

namespace VG.Proof.SlhDsa.X86_64.Wots4

open VG VG.X86_64 VG.X86_64.Steps
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.SlhDsa (fld)

variable {p : Params} {stk : Nat} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-- Where chain `i` of lane `k` goes in `B`. -/
abbrev bR (p : Params) (S : Addr) (k i : Nat) : Region := ⟨at' S (Layout.laneB k + p.n + 32 + i * p.n), p.n⟩

theorem bR_wch (hz : Sz p) {k i : Nat} (hk : k < 4) (hi : i < p.len) (S sig : Addr) (kp : Nat) (sp : Addr) (stk : Nat) :
    ∃ R ∈ wch p S sig kp sp stk, Region.Sub (bR p S k i) R := by
  have hn := hz.n32
  refine ⟨_, tailB_mem k hk S sig kp sp stk, ?_⟩
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have e := sub_tailB (p := p) (S := S) (k := k) (a := p.n + 32 + i * p.n) (l := p.n) (by omega_using [])
    (by rw [strideB_eq]; omega_using [hf])
  rwa [show Layout.laneB k + (p.n + 32 + i * p.n) = Layout.laneB k + p.n + 32 + i * p.n by omega_using []] at e

theorem bR_save (hz : Sz p) {k i : Nat} (hk : k < 4) (hi : i < p.len) (S : Addr) :
    Region.Disjoint ⟨at' S 2400, 48⟩ (bR p S k i) := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  exact Entry.dscr (Or.inl (by rw [laneB_eq]; omega_using [])) (by decide)
    (by rw [laneB_eq]; omega_using [hf, hk])

/-- Two places of chain ends in `B`. -/
theorem bR_disj (hz : Sz p) {k i k' i' : Nat} (hk : k < 4) (hi : i < p.len) (hk' : k' < 4) (hi' : i' < p.len)
    (h : k ≠ k' ∨ i ≠ i') (S : Addr) : Region.Disjoint (bR p S k i) (bR p S k' i') := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have hf' := bm_fit hz hk' hi'
  rw [laneB_eq, strideB_eq] at hf'
  have hc : Layout.laneB k + p.n + 32 + i * p.n + p.n ≤ Layout.laneB k' + p.n + 32 + i' * p.n ∨
      Layout.laneB k' + p.n + 32 + i' * p.n + p.n ≤ Layout.laneB k + p.n + 32 + i * p.n := by
    rw [laneB_eq, laneB_eq]
    rcases h with h | h
    · rcases Nat.lt_or_gt_of_ne h with h | h <;> omega_using [h, hf, hf']
    · rcases Nat.lt_or_gt_of_ne h with h | h
      · by_cases e : k = k'
        · subst e; left
          have := Nat.mul_le_mul_right p.n (show i + 1 ≤ i' by omega_using [h]); rw [Nat.add_mul, Nat.one_mul] at this
          omega_using [this]
        · rcases Nat.lt_or_gt_of_ne e with e | e <;> omega_using [e, hf, hf']
      · by_cases e : k = k'
        · subst e; right
          have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ i by omega_using [h]); rw [Nat.add_mul, Nat.one_mul] at this
          omega_using [this]
        · rcases Nat.lt_or_gt_of_ne e with e | e <;> omega_using [e, hf, hf']
  exact Entry.dscr hc (by rw [laneB_eq]; omega_using [hf, hk])
    (by rw [laneB_eq]; omega_using [hf', hk'])

/-- A place of a chain end in `B` and a range of a lane of `A`. -/
theorem bR_la (hz : Sz p) {k i k' o l : Nat} (hk : k < 4) (hi : i < p.len) (hk' : k' < 4) (ho : o + l ≤ p.n + 32)
    (S : Addr) : Region.Disjoint (bR p S k i) ⟨at' S (Layout.laneA k' + p.n + o), l⟩ := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  exact Entry.dscr (Or.inr (by rw [laneA_eq, laneB_eq]; omega_using [hk', ho, hn]))
    (by rw [laneB_eq]; omega_using [hf, hk]) (by rw [laneA_eq]; omega_using [hk', ho, hn])

/-- A chain end in `B` and a fields' range of a lane of `B`. -/
theorem bR_fB (hz : Sz p) {k i k' o : Nat} (hk : k < 4) (hi : i < p.len) (hk' : k' < 4) (ho₁ : 16 ≤ o)
    (ho : o + 4 ≤ 32) (S : Addr) : Region.Disjoint (bR p S k i) ⟨at' S (Layout.laneB k' + p.n + o), 4⟩ := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have hc : Layout.laneB k' + p.n + o + 4 ≤ Layout.laneB k + p.n + 32 + i * p.n ∨
      Layout.laneB k + p.n + 32 + i * p.n + p.n ≤ Layout.laneB k' + p.n + o := by
    rw [laneB_eq, laneB_eq]
    by_cases e : k = k'
    · subst e; left; omega_using [ho]
    · rcases Nat.lt_or_gt_of_ne e with e | e <;> omega_using [e, hf, ho, ho₁]
  exact Entry.dscr hc.symm (by rw [laneB_eq]; omega_using [hf, hk])
    (by rw [laneB_eq]; omega_using [hk', ho, hn])

/-- A chain end in `B` and a chain of the signature. -/
theorem bR_sig (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i i' : Nat} (hk : k < 4) (hi : i < p.len)
    (hi' : i' < p.len) : Region.Disjoint (bR p S k i) ⟨sig + BitVec.ofNat 64 (i' * p.n), p.n⟩ := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have hl : i' * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ p.len by omega_using [hi']); rwa [Nat.add_mul, Nat.one_mul] at this
  exact (hE.dsig hl (by rw [oSigTmp_eq, laneB_eq]; omega_using [hf, hk])).symm

theorem at_add (S : Addr) (a b : Nat) : BitVec.ofNat 64 a + S + BitVec.ofNat 64 b = at' S (b + a) := by
  rw [BitVec.add_comm (BitVec.ofNat 64 a) S, ofNat_add', Nat.add_comm]

/-- `toB`: the end of chain `i` of each lane to its message in `B`. -/
theorem toB_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i : Nat} (hi : i < p.len) {t : State}
    (hb : Base hE t) (hr13 : t.gpr .r13 = BitVec.ofNat 64 i) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Base hE t' → (∀ g, g ≠ .rax → g ≠ .rdx → t'.gpr g = t.gpr g) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n = la p t.mem S k 32 p.n) →
      Frame ((List.range 4).map fun k => bR p S k i) t.mem t'.mem → WP isa (.block is) t' Q) :
    WP isa (.block (Wots.toB (L p) ++ is)) t Q := by
  have hn := hz.n32
  have h8 := hz.n8
  simp only [Wots.toB, List.append_assoc]
  refine wp_mov fun t₁ u₁ => mulN_ok hz.nv (r := .rdx) (tmp := .rax) (x := i) (by decide)
    (by rw [u₁.gpr, hr13]) fun t₂ h₂ g₂ m₂ rd₂ wr₂ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun t₃ u₃ => ?_
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, m₂, u₁.mem]
  have hg₃ : ∀ g, g ≠ .rax → g ≠ .rdx → t₃.gpr g = t.gpr g := fun g h₁ h₂ => by
    rw [u₃.other _ h₂, g₂ _ h₂ h₁, u₁.other _ h₂]
  have hb₃ : Base hE t₃ := hb.regs hm₃ (by rw [u₃.rd, rd₂, u₁.rd]) (by rw [u₃.wr, wr₂, u₁.wr]) fun g h' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)
  have hdx : t₃.gpr .rdx = BitVec.ofNat 64 (i * p.n) + S := by
    rw [u₃.gpr, h₂, u₃.other _ (by decide) |>.symm.trans (u₃.other _ (by decide)), g₂ _ (by decide) (by decide),
      u₁.other _ (by decide), hb.rbx]
  have hrbx : ∀ u : State, Base hE u → u.gpr .rbx = S := fun u h => h.rbx
  refine WP.block_append (WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧
      (∀ g, g ≠ .rax → u.gpr g = t₃.gpr g) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n = la p t.mem S k 32 p.n) ∧
      Frame ((List.range K).map fun k => bR p S k i) t₃.mem u.mem)
    ⟨hb₃, fun _ _ => rfl, fun _ h => absurd h (by omega_using []), by simpa using Frame.refl [] t₃.mem⟩
    fun K hK u hu => ?_) fun u hu => ?_)
  · have hdxu : u.gpr .rdx = BitVec.ofNat 64 (i * p.n) + S := by rw [hu.2.1 _ (by decide), hdx]
    have hfit := bm_fit hz hK hi
    have hdst : ∀ j < p.n / 8, InRegions u.wr (u.gpr .rdx + BitVec.ofNat 64 (Layout.laneB K + (L p).msgOff + 8 * j)) 8 :=
      fun j hj => by
        rw [hdxu, at_add]
        exact hE.inScr hu.1.wr (by simp only [Layout.msgOff]; rw [laneB_eq, strideB_eq] at hfit; rw [laneB_eq]; omega_using [hfit, hj, hK, h8])
    have hsrc : ∀ j < p.n / 8, InRegions (u.rd ++ u.wr) (u.gpr .rbx + BitVec.ofNat 64 (Layout.laneA K + (L p).msgOff + 8 * j)) 8 :=
      fun j hj => by
        rw [hrbx u hu.1]
        exact hE.inScr' hu.1.rd hu.1.wr (by simp only [Layout.msgOff]; rw [laneA_eq]; omega_using [hj, hK, h8, hn])
    have hw8 : 8 * (p.n / 8) = p.n := by omega_using [h8]
    have hdis : Region.Disjoint ⟨u.gpr .rdx + BitVec.ofNat 64 (Layout.laneB K + (L p).msgOff), 8 * (p.n / 8)⟩
        ⟨u.gpr .rbx + BitVec.ofNat 64 (Layout.laneA K + (L p).msgOff), 8 * (p.n / 8)⟩ := by
      rw [hdxu, at_add, hrbx u hu.1, hw8]
      have := bR_la hz hK hi hK (o := 32) (l := p.n) (by omega_using []) S
      simp only [bR, at', Layout.msgOff, Nat.add_assoc] at this ⊢
      exact this
    refine WP.mono (copyWords_ok (by decide) (by decide) hdst hsrc hdis (by omega_using [hn])
      (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hK, hn])) fun u' c => ?_
    rw [hdxu, at_add, hrbx u hu.1, hw8] at c
    have hbr : at' S (Layout.laneB K + (L p).msgOff + i * p.n) = at' S (Layout.laneB K + p.n + 32 + i * p.n) := by
      simp only [Layout.msgOff, Nat.add_assoc]
    rw [hbr] at c
    have hf' : Frame [bR p S K i] u.mem u'.mem := c.frame
    refine ⟨hu.1.ofFrame c.rd c.wr (fun g hg => c.gpr g (base_regs_ne hg)) hf'
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact bR_wch hz hK hi S sig kp _ stk)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact bR_save hz hK hi S),
      fun g hg => by rw [c.gpr g hg, hu.2.1 g hg], fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact bR_disj hz (by omega_using [hk', hK]) hi hK hi (Or.inl (by omega_using [hk'])) S) (by omega_using [hn]),
          hu.2.2.1 k hk']
      · have e₁ : bytesAt u'.mem (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n =
            bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n := by
          refine bytesAt_ext fun q hq => ?_
          have := c.bytes q (by omega_using [hq, hw8])
          simpa only [Layout.msgOff, Nat.add_assoc] using this
        rw [e₁, show at' S (Layout.laneA k + p.n + 32) = at' S (Layout.laneA k + p.n + 32) from rfl]
        have e₂ := bytesAt_frame (a := at' S (Layout.laneA k + p.n + 32)) (n := p.n) hu.2.2.2 (fun r hr => by
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
          exact (bR_la hz (by have := List.mem_range.mp hk'; omega_using [this, hK]) hi hK (o := 32) (l := p.n)
            (by omega_using []) S).symm)
          (by omega_using [hn])
        rw [e₂, hm₃]
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact frame_cat hu.2.2.2 hf'
  · exact kk u hu.1 (fun g h₁ h₂ => by rw [hu.2.1 g h₁, hg₃ g h₁ h₂]) hu.2.2.1 (by rw [← hm₃]; exact hu.2.2.2)

/-! ## A chain of the four lanes -/

/-- Before chain `i`: the ends of the chains before it in `B`, the
signature's chains before it captured. -/
structure ChainInv (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (i : Nat) (t : State) : Prop where
  base : Base hE t
  mx : t.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  lanes : ∀ k < 4, LaneSet p t.mem S kp k
  ends : ∀ k < 4, ∀ i' < i, bm p t.mem S k i' = cv p skSeed pkSeed a16 kp k i' 15
  sigs : ∀ i' < p.len, sigC p t.mem sig i' = if InR kp idx ∧ i' < i then
    wotsChainAt p skSeed pkSeed a16 idx i' (digitAt σ.mem S i') else sigC p σ.mem sig i'

theorem bR_AZ (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i' i : Nat} (hk : k < 4)
    (hi' : i' < p.len) (hi : i < p.len) : ∀ r ∈ AZ p S sig (σ.gpr .rsp) stk i, Region.Disjoint (bR p S k i') r := by
  have hf := bm_fit hz hk hi'
  rw [laneB_eq, strideB_eq] at hf
  exact B_AZ hE hz (a := Layout.laneB k + p.n + 32 + i' * p.n) (l := p.n) (by rw [laneB_eq]; omega_using [])
    (by rw [laneB_eq]; omega_using [hf, hk]) hi

theorem fB_AZ (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k o i : Nat} (hk : k < 4) (ho : o ≤ 28)
    (hi : i < p.len) : ∀ r ∈ AZ p S sig (σ.gpr .rsp) stk i, Region.Disjoint ⟨at' S (Layout.laneB k + p.n + o), 4⟩ r := by
  have hn := hz.n32
  exact B_AZ hE hz (a := Layout.laneB k + p.n + o) (l := 4) (by rw [laneB_eq]; omega_using [])
    (by rw [laneB_eq]; omega_using [hn, hk, ho]) hi

/-- A range of `scratch` before the signature's copy and a chain of the signature. -/
theorem scr_sig (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) {i a l : Nat} (hi : i < p.len)
    (ha : a + l ≤ Layout.oSigTmp) : Region.Disjoint ⟨at' S a, l⟩ ⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ := by
  have hl : i * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i + 1 ≤ p.len by omega_using [hi]); rwa [Nat.add_mul, Nat.one_mul] at this
  exact (hE.dsig hl ha).symm

theorem LaneSet.frame {m m' : Mem} {k : Nat} {rs : List Region} (hl : LaneSet p m S kp k) (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.laneA k + p.n + 20), 4⟩ r)
    (hB : ∀ o, 16 ≤ o → o ≤ 28 → ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.laneB k + p.n + o), 4⟩ r) :
    LaneSet p m' S kp k :=
  ⟨(bytesAt_frame hf hA (by decide)).trans hl.a20,
    (bytesAt_frame hf (hB 16 (by decide) (by decide)) (by decide)).trans hl.b16,
    (bytesAt_frame hf (hB 20 (by decide) (by decide)) (by decide)).trans hl.b20,
    (bytesAt_frame hf (hB 24 (by decide) (by decide)) (by decide)).trans hl.b24,
    (bytesAt_frame hf (hB 28 (by decide) (by decide)) (by decide)).trans hl.b28⟩

theorem nm_final : (Wots.capture (L p) ++ Wots.toB (L p) ++
    [Instr.alu .add .r13 (.imm 1), Instr.alu .cmp .r13 (.imm (BitVec.ofNat 32 (L p).len))]).all (fun i => !loadsMxcsr i) = true := by
  simp only [Wots.capture, Wots.toB, List.all_append, nm_mulN, nm_flatMap 4 (nm_captureLane _),
    nm_flatMap 4 fun k => nm_copyWords _ _ _ _ _]
  rfl

/-- Chain `i` of the four lanes. -/
theorem chainBody_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) {i : Nat} (hi : i < p.len) {t₀ : State} (h : ChainInv hE i t₀) :
    WP isa (Wots.chainBody (L p) name T.code) t₀ (fun t' => ChainInv hE (i + 1) t' ∧
      t'.zf = some (decide (i + 1 = p.len))) := by
  have hn := hz.n32
  have hlen31 : p.len < 2 ^ 31 := by have := hz.len; omega_using [this, hn]
  refine chainHead_ok hE hz T name hs hi h.base h.mx h.r13 (fun k hk => (h.lanes k hk).a20) fun t ht => ?_
  refine WP.seq (WP.mono (steps_ok hE hz T name hs hi ht) fun u hu => ?_)
  refine wp_mx nm_final ?_
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (capture_ok hE hz hi (by decide) hu.base hu.r13 hu.rbp fun k hk => by
      obtain ⟨_, l⟩ := hu.lanes k hk; exact l.msg) fun u₁ ⟨hb₁, hg₁, hs₁, hf₁⟩ => ?_)
  have hr₁ : u₁.gpr .r13 = BitVec.ofNat 64 i := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hu.r13]
  refine toB_ok hE hz hi hb₁ hr₁ fun u₂ hb₂ hg₂ he₂ hf₂ => ?_
  refine wp_addi fun u₃ v₃ => wp_cmpi fun u₄ g₄ m₄ rd₄ wr₄ _ zf₄ => WP.block_nil fun hmx₄ => ?_
  have hm : u₄.mem = u₂.mem := by rw [m₄, v₃.mem]
  have hr₄ : u₄.gpr .r13 = BitVec.ofNat 64 (i + 1) := by
    rw [g₄, v₃.gpr, hg₂ _ (by decide) (by decide), hr₁,
      show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from by decide, ← BitVec.ofNat_add]
  -- Frames of the capture and of `toB`.
  have hfB : ∀ {R : Region}, (∀ k < 4, Region.Disjoint R (bR p S k i)) → ∀ r ∈ (List.range 4).map fun k => bR p S k i,
      Region.Disjoint R r := fun hR r hr => by
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
    exact hR k' (List.mem_range.mp hk')
  have hfS : ∀ {R : Region}, Region.Disjoint R ⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ →
      ∀ r ∈ [(⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ : Region)], Region.Disjoint R r := fun hR r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR
  refine ⟨⟨hb₂.regs hm (by rw [rd₄, v₃.rd]) (by rw [wr₄, v₃.wr]) fun g hg => by
      rw [g₄, v₃.other g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [hmx₄]; exact hu.mx, hr₄, fun k hk => ?_, fun k hk i' hi' => ?_, fun i' hi' => ?_⟩, ?_⟩
  · -- The lanes' fields.
    obtain ⟨_, la₀⟩ := hu.lanes k hk
    have l₀ : LaneSet p u.mem S kp k :=
      ⟨la₀.f20, (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 16) (by decide) hi) (by decide)).trans (h.lanes k hk).b16,
        (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 20) (by decide) hi) (by decide)).trans (h.lanes k hk).b20,
        (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 24) (by decide) hi) (by decide)).trans (h.lanes k hk).b24,
        (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 28) (by decide) hi) (by decide)).trans (h.lanes k hk).b28⟩
    have l₁ := l₀.frame hf₁ (hfS (scr_sig hE hi (a := Layout.laneA k + p.n + 20) (l := 4) (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])))
      fun o _ ho => hfS (scr_sig hE hi (a := Layout.laneB k + p.n + o) (l := 4) (by rw [laneB_eq, oSigTmp_eq]; omega_using [hk, hn, ho]))
    rw [hm]
    exact l₁.frame hf₂ (hfB fun k' hk' => (bR_la hz hk' hi hk (o := 20) (l := 4) (by omega_using [hn]) S).symm)
      fun o ho₁ ho => hfB fun k' hk' => (bR_fB hz hk' hi hk ho₁ (by omega_using [ho]) S).symm
  · -- The ends of the chains.
    have hi'l : i' < p.len := by omega_using [hi', hi]
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
    · show bytesAt _ _ _ = _
      rw [bytesAt_frame hf₂ (hfB fun k' hk' => bR_disj hz hk hi'l hk' hi (Or.inr (by omega_using [hlt])) S)
          (by omega_using [hn]),
        bytesAt_frame hf₁ (hfS (bR_sig hE hz hk hi'l hi)) (by omega_using [hn]),
        bytesAt_frame hu.fr (bR_AZ hE hz hk hi'l hi) (by omega_using [hn])]
      exact h.ends k hk i' hlt
    · show bytesAt _ _ _ = _
      rw [he₂ k hk]
      obtain ⟨_, la₀⟩ := hu.lanes k hk
      show bytesAt _ _ _ = _
      rw [bytesAt_frame hf₁ (hfS (scr_sig hE hi (a := Layout.laneA k + p.n + 32) (l := p.n)
        (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn]))) (by omega_using [hn])]
      exact la₀.msg
  · -- The signature's chains.
    rw [hm]
    show bytesAt _ _ _ = _
    rw [bytesAt_frame hf₂ (hfB fun k' hk' => (bR_sig hE hz hk' hi hi').symm) (by omega_using [hn])]
    by_cases e : i' = i
    · subst e
      show sigC p u₁.mem sig i' = _
      rw [hs₁, hu.sigc]
      refine (sig_step (InR kp idx) (fun x => wotsChainAt p skSeed pkSeed a16 idx i' x) _).trans ?_
      have hd := hE.dig i' hi'
      by_cases hP : InR kp idx
      · rw [ite_eq_left (⟨hP, by omega_using [hd]⟩ : InR kp idx ∧ digitAt σ.mem S i' < 15 + 1),
          ite_eq_left (⟨hP, Nat.lt_succ_self i'⟩ : InR kp idx ∧ i' < i' + 1)]
      · rw [ite_eq_right (fun h' => hP h'.1), ite_eq_right (fun h' => hP h'.1), h.sigs i' hi', ite_eq_right (fun h' => hP h'.1)]
    · rw [bytesAt_frame hf₁ (hfS (sig_AZ hE hz hi hi' e _ (by simp [AZ]))) (by omega_using [hn]),
        bytesAt_frame hu.fr (sig_AZ hE hz hi hi' e) (by omega_using [hn])]
      show sigC p t₀.mem sig i' = _
      rw [h.sigs i' hi']
      by_cases hc : InR kp idx ∧ i' < i
      · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega_using [hc.2]⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ⟨h'.1, by omega_using [h'.2, e]⟩)]
  · have hl := hz.len
    rw [zf₄, ← g₄, hr₄, sext_ofNat hlen31, zf_eq (by omega_using [hi, hl, hn]) (by omega_using [hl, hn])]

end VG.Proof.SlhDsa.X86_64.Wots4

/-! ## `wotsLeaves4` meets its contract

The loop of the `len` chains (`chains_ok`), the public keys (`leaves_ok`:
`T_len` of the chain ends in the lanes of `B`, to the nodes), the restore of
the caller's registers, and the whole function (`wots4_spec`): from a state
satisfying `wots4Contract`'s precondition, it returns in a state satisfying
its postcondition, keeping what the calling convention keeps.
-/

namespace VG.Proof.SlhDsa.X86_64.Wots4

open VG VG.X86_64 VG.X86_64.Steps
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.SlhDsa (fld)

variable {p : Params} {stk : Nat} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-- The `len` chains. -/
theorem chains_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) {t : State} (h : ChainInv hE 0 t) :
    WP isa (.loop (Wots.chainBody (L p) name T.code) .ne) t (ChainInv hE p.len) := by
  have hl : 1 ≤ p.len := by have := hz.len; omega_using [this]
  refine WP.loop (M := isa) (Inv := fun (n : Nat) (u : State) => 1 ≤ n ∧ n ≤ p.len ∧ ChainInv hE (p.len - n) u)
    (fun n u hu => ?_) p.len t
    ⟨hl, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  obtain ⟨h₁, h₂, hu⟩ := hu
  refine WP.mono (chainBody_ok hE hz T name hs (by omega_using [h₁, h₂]) hu) fun u' ⟨hu', hzf⟩ => ?_
  by_cases e : p.len - n + 1 = p.len
  · rw [e] at hu'
    exact Or.inl ⟨by rw [eval_ne hzf, decide_eq_true e]; rfl, hu'⟩
  · refine Or.inr ⟨by rw [eval_ne hzf, decide_eq_false e]; rfl, n - 1, by omega_using [h₁],
      ⟨by omega_using [e, h₁, h₂], by omega_using [h₂], ?_⟩⟩
    rw [show p.len - (n - 1) = p.len - n + 1 by omega_using [h₁, h₂, e]]; exact hu'

/-! ## The public keys -/

theorem bytesAt_flat (m : Mem) (S : Addr) (b n : Nat) :
    ∀ L, bytesAt m (at' S b) (L * n) = (List.range L).flatMap fun i => bytesAt m (at' S (b + i * n)) n
  | 0 => by simp [bytesAt]
  | L + 1 => by
    rw [Nat.add_mul, Nat.one_mul, bytesAt_split, bytesAt_flat m S b n L, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

theorem w_eq (hz : Sz p) : p.w - 1 = 15 := by simp [Params.w, hz.lgw]

/-- `wots_pkGen`, as `T_len` of the chain ends. -/
theorem pkGen_eq (hz : Sz p) (h16 : a16.length = 16) {κ : Nat} (hκ : κ < 2 ^ 32) :
    wotsPkGen p skSeed pkSeed (wotsAdrs a16 κ) = shake256 (pkSeed ++ fld a16 WOTS_PK κ 0 0 ++
      (List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 κ i 15) p.n := by
  have e : wotsPkGen p skSeed pkSeed (wotsAdrs a16 κ) = T p pkSeed (wotsPkAdrs (wotsAdrs a16 κ))
      ((List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 κ i (p.w - 1)) := rfl
  rw [e, w_eq hz, VG.Proof.SlhDsa.wotsAdrs_fld h16, VG.Proof.SlhDsa.wotsPkAdrs_fld h16 _ _ _ _ hκ]
  simp only [T, hz.shake, shakeAdrs]

theorem flatMap_range_congr {f g : Nat → List Byte} : ∀ {K : Nat}, (∀ i < K, f i = g i) →
    (List.range K).flatMap f = (List.range K).flatMap g
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr fun i hi => h i (by omega_using [hi]),
      List.flatMap_singleton, List.flatMap_singleton, h K (by omega_using [])]

theorem at_off (S : Addr) (a b : Nat) : at' S a + BitVec.ofNat 64 b = at' S (a + b) := ofNat_add' S a b

/-- The node of key pair `kp + k`. -/
abbrev nR (p : Params) (S : Addr) (kp k : Nat) : Region := ⟨at' S (Layout.oN + kp * p.n + p.n * k), p.n⟩

theorem nR_fit (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) {k : Nat} (hk : k < 4) :
    Layout.oN + kp * p.n + p.n * k + p.n ≤ 29280 := by
  have hkp := hE.kpN
  rw [nodeSlots_eq, Nat.add_mul] at hkp
  have : p.n * k + p.n ≤ 4 * p.n := by
    have := Nat.mul_le_mul_left p.n (show k + 1 ≤ 4 by omega_using [hk]); rw [Nat.mul_add, Nat.mul_one] at this
    omega_using [this]
  rw [oN_eq]; omega_using [hkp, this]

/-- The public keys: `T_len` of the lanes of `B`, copied to the nodes. -/
theorem leaves_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) {t : State} (h : ChainInv hE p.len t) :
    WP isa (Wots.leaves (L p) name T.code) t (fun t' => Base hE t' ∧
      t'.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10 ∧
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (kp + k) * p.n)) p.n =
        wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))) ∧
      ∀ i' < p.len, sigC p t'.mem sig i' = sigC p t.mem sig i') := by
  have hn := hz.n32
  have h8 := hz.n8
  have hl := hz.len
  have h16 := a16_length hE.env
  have hkp := hE.kp_lt hz
  have hlm : (p.n + 32 + p.len * p.n) % 8 = 0 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e]
  have hll : p.n + 32 + p.len * p.n ≤ 2208 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  refine WP.seq (tcall_ok hE hz T name hs (o := 3808) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
    (by omega_using []) hlm hll h.base fun t₁ hb₁ hcs₁ hout₁ hf₁ hmx₁ => ?_)
  -- The messages of the lanes of `B`.
  have hmsg : ∀ k < 4, bytesAt t.mem (at' S (3808 + k * 2208)) (p.n + 32 + p.len * p.n) =
      pkSeed ++ fld a16 WOTS_PK (kp + k) 0 0 ++
        (List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 (kp + k) i 15 := by
    intro k hk
    have henv := h.base.env hz
    obtain ⟨_, b16, b20, b24, b28⟩ := h.lanes k hk
    simp only [fB] at b16 b20 b24 b28
    rw [show 3808 + k * 2208 = Layout.laneB k by rw [laneB_eq]; omega_using [], lane_msg, henv.seedB k hk,
      henv.adrsB k hk, b16, b20, b24, b28, bytesAt_flat]
    rw [flatMap_range_congr fun i hi => h.ends k hk i hi]
    simp only [fld, List.append_assoc, WOTS_PK]
  have hpk : ∀ k < 4, bytesAt t₁.mem (at' S (Layout.laneB k + p.n + 32)) p.n =
      wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k)) := fun k hk => by
    have e := hout₁ k hk
    rw [hmsg k hk, show 3808 + k * 2208 + p.n + 32 = Layout.laneB k + p.n + 32 by rw [laneB_eq]; omega_using []] at e
    rw [e, pkGen_eq hz h16 (by omega_using [hkp, hk])]
  have hsig₁ : ∀ i' < p.len, sigC p t₁.mem sig i' = sigC p t.mem sig i' := fun i' hi' =>
    sig_t4 hE hz hs (Or.inr ⟨rfl, rfl⟩) hi' hf₁
  -- `rdx ← scratch + oN + kp·n`.
  refine wp_mx (by
    simp only [Wots.leafPtr, List.all_append, nm_mulN, nm_flatMap 4 fun k => nm_copyWords _ _ _ _ _]; rfl) ?_
  simp only [Wots.leafPtr, List.append_assoc]
  refine wp_mov fun t₂ u₂ => mulN_ok hz.nv (r := .rdx) (tmp := .rax) (x := kp) (by decide)
    (by rw [u₂.gpr, hb₁.r12]) fun t₃ h₃ g₃ m₃ rd₃ wr₃ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun t₄ u₄ => wp_addi fun t₅ u₅ => ?_
  have hm₅ : t₅.mem = t₁.mem := by rw [u₅.mem, u₄.mem, m₃, u₂.mem]
  have hg₅ : ∀ g, g ≠ .rax → g ≠ .rdx → t₅.gpr g = t₁.gpr g := fun g h₁ h₂ => by
    rw [u₅.other _ h₂, u₄.other _ h₂, g₃ _ h₂ h₁, u₂.other _ h₂]
  have hb₅ : Base hE t₅ := hb₁.regs hm₅ (by rw [u₅.rd, u₄.rd, rd₃, u₂.rd]) (by rw [u₅.wr, u₄.wr, wr₃, u₂.wr])
    fun g h' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)
  have hdx : t₅.gpr .rdx = at' S (Layout.oN + kp * p.n) := by
    rw [u₅.gpr, u₄.gpr, h₃, u₄.other _ (by decide) |>.symm.trans (u₄.other _ (by decide)), g₃ _ (by decide) (by decide),
      u₂.other _ (by decide), hb₁.rbx, sext_ofNat (by rw [oN_eq]; decide), at_add]
  -- The copies.
  refine WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧ (∀ g, g ≠ .rax → u.gpr g = t₅.gpr g) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.oN + kp * p.n + p.n * k)) p.n =
        wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))) ∧
      Frame ((List.range K).map fun k => nR p S kp k) t₅.mem u.mem)
    ⟨hb₅, fun _ _ => rfl, fun _ h => absurd h (by omega_using []), by simpa using Frame.refl [] t₅.mem⟩
    fun K hK u hu => ?_) fun u hu => ?_
  · have hdxu : u.gpr .rdx = at' S (Layout.oN + kp * p.n) := by rw [hu.2.1 _ (by decide), hdx]
    have hrbx : u.gpr .rbx = S := hu.1.rbx
    have hfit := nR_fit hE hK
    have hw8 : 8 * (p.n / 8) = p.n := by omega_using [h8]
    have hdst : ∀ j < p.n / 8, InRegions u.wr (u.gpr .rdx + BitVec.ofNat 64 (p.n * K + 8 * j)) 8 := fun j hj => by
      rw [hdxu, at_off]
      exact hE.inScr hu.1.wr (by omega_using [hfit, hj, h8])
    have hsrc : ∀ j < p.n / 8, InRegions (u.rd ++ u.wr) (u.gpr .rbx + BitVec.ofNat 64 (Layout.laneB K + (L p).msgOff + 8 * j)) 8 :=
      fun j hj => by
        rw [hrbx]
        exact hE.inScr' hu.1.rd hu.1.wr (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hj, hK, h8, hn])
    have hdis : Region.Disjoint ⟨u.gpr .rdx + BitVec.ofNat 64 (p.n * K), 8 * (p.n / 8)⟩
        ⟨u.gpr .rbx + BitVec.ofNat 64 (Layout.laneB K + (L p).msgOff), 8 * (p.n / 8)⟩ := by
      rw [hdxu, at_off, hrbx, hw8]
      exact Entry.dscr (Or.inr (by simp only [Layout.msgOff]; rw [laneB_eq, oN_eq]; omega_using [hK, hn]))
        (by omega_using [hfit]) (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hK, hn])
    have hnK : p.n * K ≤ 32 * 4 := Nat.mul_le_mul hn (Nat.le_of_lt hK)
    refine WP.mono (copyWords_ok (by decide) (by decide) hdst hsrc hdis (by omega_using [hn])
      (by omega_using [hnK, hn, hw8])) fun u' c => ?_
    rw [hdxu, at_off, hrbx, hw8] at c
    have hf' : Frame [nR p S kp K] u.mem u'.mem := by
      simpa only [nR, Nat.add_assoc] using c.frame
    have hfar : ∀ {a l : Nat}, a + l ≤ Layout.oN → Region.Disjoint ⟨at' S a, l⟩ (nR p S kp K) := fun ha =>
      Entry.dscr (Or.inl (by omega_using [ha])) (by rw [oN_eq] at ha; omega_using [ha]) (by omega_using [hfit])
    refine ⟨hu.1.ofFrame c.rd c.wr (fun g hg => c.gpr g (base_regs_ne hg)) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨⟨at' S (Layout.oN + kp * p.n), 4 * p.n⟩, by simp [wch], Offset.sub S (by omega_using []) ?_⟩
        have := Nat.mul_le_mul_left p.n (show K + 1 ≤ 4 by omega_using [hK]); rw [Nat.mul_add, Nat.mul_one] at this
        omega_using [this])
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hfar (by rw [oN_eq]; decide)),
      fun g hg => by rw [c.gpr g hg, hu.2.1 g hg], fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            have hf₂ := nR_fit hE (show k < 4 by omega_using [hk', hK])
            refine Entry.dscr (Or.inl ?_) (by omega_using [hf₂]) (by omega_using [hfit])
            have := Nat.mul_le_mul_left p.n (show k + 1 ≤ K by omega_using [hk']); rw [Nat.mul_add, Nat.mul_one] at this
            omega_using [this]) (by omega_using [hn]),
          hu.2.2.1 k hk']
      · have e₁ : bytesAt u'.mem (at' S (Layout.oN + kp * p.n + p.n * k)) p.n =
            bytesAt u.mem (at' S (Layout.laneB k + p.n + 32)) p.n := by
          refine bytesAt_ext fun q hq => ?_
          have := c.bytes q (by omega_using [hq])
          simpa only [Layout.msgOff, Nat.add_assoc, at', ofNat_add'] using this
        rw [e₁, bytesAt_frame hu.2.2.2 (fun r hr => by
            obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
            have hf₂ := nR_fit hE (show k' < 4 by have := List.mem_range.mp hk'; omega_using [this, hK])
            exact Entry.dscr (Or.inl (by rw [laneB_eq, oN_eq]; omega_using [hK, hn]))
              (by rw [laneB_eq]; omega_using [hK, hn]) (by omega_using [hf₂])) (by omega_using [hn]),
          hm₅, hpk k hK]
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact frame_cat hu.2.2.2 hf'
  · obtain ⟨hb, _, hn', hf⟩ := hu
    refine fun hmx => ⟨hb, ?_, fun k hk => ?_, fun i' hi' => ?_⟩
    · rw [hmx, hmx₁]; exact h.mx
    · rw [show Layout.oN + (kp + k) * p.n = Layout.oN + kp * p.n + p.n * k by rw [Nat.add_mul, Nat.mul_comm k]; omega_using []]
      exact hn' k hk
    · rw [← hsig₁ i' hi', ← hm₅]
      have hlen : i' * p.n + p.n ≤ p.len * p.n := by
        have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ p.len by omega_using [hi']); rwa [Nat.add_mul, Nat.one_mul] at this
      exact bytesAt_frame hf (fun r hr => by
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
        have hf₂ := nR_fit hE (show k' < 4 from List.mem_range.mp hk')
        exact hE.dsig hlen (by rw [oSigTmp_eq]; omega_using [hf₂])) (by omega_using [hn])

/-! ## The epilogue, and the whole function -/

theorem restore_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) {t : State} (hb : Base hE t) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.mxcsr = t.mxcsr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (restoreRegs 0)) t Q := by
  have hin : ∀ i < 6, InRegions (t.rd ++ t.wr) (at' S (Layout.oSave 0 i)) 8 := fun i hi =>
    hE.inScr' hb.rd hb.wr (by rw [oSave_eq]; omega_using [hi])
  refine wp_mx rfl ?_
  rw [show restoreRegs 0 = [Instr.mov .r15 (.mem (at_ .rbx (Layout.oSave 0 5))),
    .mov .r14 (.mem (at_ .rbx (Layout.oSave 0 4))), .mov .r13 (.mem (at_ .rbx (Layout.oSave 0 3))),
    .mov .r12 (.mem (at_ .rbx (Layout.oSave 0 2))), .mov .rbp (.mem (at_ .rbx (Layout.oSave 0 1))),
    .mov .rbx (.mem (at_ .rbx (Layout.oSave 0 0)))] from rfl]
  refine wp_movm (by rw [ea_at, hb.rbx]) (hin 5 (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (by rw [ea_at, u₁.other _ (by decide), hb.rbx]) (by rw [u₁.rd, u₁.wr]; exact hin 4 (by decide))
    fun t₂ u₂ => ?_
  refine wp_movm (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hb.rbx])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_movm (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb.rbx])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 2 (by decide)) fun t₄ u₄ => ?_
  refine wp_movm (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb.rbx])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 1 (by decide)) fun t₅ u₅ => ?_
  refine wp_movm (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hb.rbx])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 0 (by decide))
    fun t₆ u₆ => WP.block_nil fun hmx => ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) hmx fun r hr => ?_
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hb.saved 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hb.saved 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hb.rsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hb.saved 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hb.saved 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hb.saved 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hb.saved 5 (by decide)

/-- What `wotsLeaves4` does, from the entry state `σ`. -/
structure Wots4Post (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (t : State) : Prop where
  cs : ∀ r ∈ calleeSaved, t.gpr r = σ.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10
  frame : Frame (wch p S sig kp (σ.gpr .rsp) stk) σ.mem t.mem
  env : Env p t.mem S pkSeed a16
  nodes : ∀ k < 4, bytesAt t.mem (at' S (Layout.oN + (kp + k) * p.n)) p.n =
    wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))
  sigs : ∀ i < p.len, sigC p t.mem sig i = if InR kp idx then
    wotsChainAt p skSeed pkSeed a16 idx i (digitAt σ.mem S i) else sigC p σ.mem sig i

theorem nm_setup : (Wots.pro ++ Wots.setup (L p)).all (fun i => !loadsMxcsr i) = true := rfl

/-- The prologue and the setup: the invariant of the chains, before the first. -/
theorem start_ok (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) :
    WP isa (.block (Wots.pro ++ Wots.setup (L p))) σ (ChainInv hE 0) := by
  have hn := hz.n32
  refine wp_mx nm_setup (WP.mono (setup_ok hE hz) fun t ht hmx => ?_)
  refine ⟨ht.base, by rw [hmx], by rw [ht.r13]; rfl, ht.lanes, fun _ _ _ h => absurd h (Nat.not_lt_zero _),
    fun i' hi' => ?_⟩
  rw [ite_eq_right (fun h => Nat.not_lt_zero _ h.2)]
  have hl : i' * p.n + p.n ≤ p.len * p.n := by
    have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ p.len by omega_using [hi']); rwa [Nat.add_mul, Nat.one_mul] at this
  exact bytesAt_frame ht.scr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hE.reg.out_scr.sub_left (Offset.sub_base sig hl)) (by omega_using [hn])

theorem wots4_wp (hE : Entry p stk σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) (hs : stk = 8 + T.stack) :
    WP isa (Wots.wotsLeaves4 (L p) name T.code) σ (Wots4Post hE) := by
  have hn := hz.n32
  refine WP.seq (WP.mono (start_ok hE hz) fun t h0 => ?_)
  refine WP.seq (WP.mono (chains_ok hE hz T name hs h0) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (leaves_ok hE hz T name hs h₁) fun t₂ h₂ => ?_)
  refine restore_ok hE h₂.1 fun t₃ m₃ mx₃ cs₃ => ⟨cs₃, by rw [mx₃]; exact h₂.2.1, by rw [m₃]; exact h₂.1.frame,
    by rw [m₃]; exact h₂.1.env hz, by rw [m₃]; exact h₂.2.2.1, fun i hi => ?_⟩
  show bytesAt _ _ _ = _
  rw [m₃]
  show sigC p t₂.mem sig i = _
  rw [h₂.2.2.2 i hi, h₁.sigs i hi]
  by_cases hP : InR kp idx
  · rw [ite_eq_left (⟨hP, hi⟩ : InR kp idx ∧ i < p.len), ite_eq_left hP]
  · rw [ite_eq_right (fun h => hP h.1), ite_eq_right hP]

/-! ## The contract -/

/-- What `wotsLeaves4` may change is in what the contract allows. -/
theorem wch_sub (hz : Sz p) {S sig : Addr} {kp : Nat} (hkp : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots) (sp : Addr) (stk : Nat) :
    ∀ r ∈ wch p S sig kp sp stk, ∃ R ∈ changes p S ++ [⟨sig, p.len * p.n⟩, below sp stk], Region.Sub r R := by
  have hn := hz.n32
  rw [nodeSlots_eq, Nat.add_mul] at hkp
  intro r hr
  simp only [wch, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl | rfl | rfl
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · exact ⟨⟨at' S Layout.oVars, 768⟩, by simp [changes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩))), fun _ h => h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩))), fun _ h => h⟩
  · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp [changes],
      Offset.sub S (by omega_using []) (by rw [nodeSlots_eq]; omega_using [hkp])⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The return address is outside what `wotsLeaves4` may change. -/
theorem wch_ret (hz : Sz p) {s : State} {S sig : Addr} {kp stk : Nat} (hreg : Regions stk s S [] ⟨sig, p.len * p.n⟩)
    (hkp : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots) (hstk : stk + 8 ≤ 2 ^ 64) :
    ∀ r ∈ wch p S sig kp (s.gpr .rsp) stk, Region.Disjoint (retR s) r := by
  have hn := hz.n32
  rw [nodeSlots_eq, Nat.add_mul] at hkp
  have hsc : ∀ {a l : Nat}, a + l ≤ 65536 → Region.Disjoint (retR s) ⟨at' S a, l⟩ := fun h =>
    hreg.ret_scr.sub_right (Offset.sub_base S h)
  intro r hr
  simp only [wch, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl | rfl | rfl
  · exact hreg.ret_scr.sub_right (Region.sub_prefix (by decide))
  · exact hsc (by decide)
  · exact hsc (by rw [oVars_eq]; decide)
  · exact hsc (by rw [laneA_eq, strideA_eq]; omega_using [hk, hn])
  · exact hsc (by rw [laneB_eq, strideB_eq]; omega_using [hk, hn])
  · exact hsc (by rw [oN_eq]; omega_using [hkp])
  · exact hreg.ret_out
  · exact Offset.base_disjoint_below _ (by omega_using [hstk])

theorem sig_flat (m : Mem) (sig : Addr) (n L : Nat) :
    bytesAt m sig (L * n) = (List.range L).flatMap fun i => bytesAt m (sig + BitVec.ofNat 64 (i * n)) n := by
  have := bytesAt_flat m sig 0 n L
  simp only [at', Nat.zero_add] at this
  rwa [show sig + BitVec.ofNat 64 0 = sig from BitVec.add_zero sig] at this

/-- The first part of `Verified`: from every state of the precondition,
`wotsLeaves4` returns, keeping what the calling convention keeps, in a state
of the postcondition. -/
theorem wots4_correct (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    ∀ s, (wots4Contract p (8 + T.stack)).pre s → ∃ t s', Exec isa (Wots.wotsLeaves4 (L p) name T.code) s t s' ∧
      abiPreserved s s' ∧ (wots4Contract p (8 + T.stack)).post s s' := by
  intro s ⟨hreg, ⟨pkSeed, a16, henv⟩, hkp4, hkpN, hidx, hdig⟩
  have hE : Entry p (8 + T.stack) s (s.gpr .rdi) (s.gpr .rcx) (s.gpr .rsi).toNat (s.gpr .rdx).toNat pkSeed a16
      (bytesAt s.mem (at' (s.gpr .rdi) Layout.oSkSeed) p.n) :=
    ⟨rfl, by simp, by simp, rfl, hreg, henv, rfl, hkp4, hkpN, hidx, hdig⟩
  obtain ⟨t, s', he, q⟩ := wots4_wp hE hz T name rfl
  have hstk : 8 + T.stack + 8 ≤ 2 ^ 64 := by have := T.stack_le; omega_using [this]
  refine ⟨t, s', he, ⟨q.cs, q.frame.readW (r := retR s) (by simp [Region.Contains]) (wch_ret hz hreg hkpN hstk)
    (by decide), q.mx⟩, ?_⟩
  intro pkSeed' a16' skSeed' henv' hsk'
  have e₁ : pkSeed' = pkSeed := by rw [← henv'.seedA 0 (by decide), henv.seedA 0 (by decide)]
  have e₂ : a16' = a16 := by rw [← henv'.adrsA 0 (by decide), henv.adrsA 0 (by decide)]
  have e₃ : skSeed' = bytesAt s.mem (at' (s.gpr .rdi) Layout.oSkSeed) p.n := hsk'.symm
  subst e₁ e₂ e₃
  refine ⟨q.env, q.nodes, fun hP i hi => by
      have := q.sigs i hi; rw [ite_eq_left hP] at this; exact this,
    fun hP => ?_, q.frame⟩
  rw [sig_flat, sig_flat]
  exact flatMap_range_congr fun i hi => by have := q.sigs i hi; rw [ite_eq_right hP] at this; exact this

end VG.Proof.SlhDsa.X86_64.Wots4
