module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Blocks
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Contracts
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Impl
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Wots
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA on AArch64: `wotsLeaves4`, its calls of `thash4`, prologue and setup

A call of an implementation `T` of `thash4` (`Thash4Impl`) on four lanes of
`stride` bytes at `scratch + o`, with `work` at `scratch` (`t4call_ok`):
each output, at `n + 32` in its lane, is `SHAKE256` of its message, and the
memory changes only in the outputs and `work[0..workUsed)`. Then, for
`wotsLeaves4`, as on x86-64 (`Proof/SlhDsa/X86_64/WotsMain.lean`): the
facts of the entry state the proof uses (`Entry`), what holds at every
point of the code (`Base`: the registers that hold the arguments, the
callee-saved registers the code does not use, the caller's registers in
frame 0, and the frame of what the function may change), the prologue and
the setup of the lanes' addresses, and the calls of `thash4` from a state
with `Base`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Wots4

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64

/-! ## Calling `thash4` on the lanes of the working space -/

/-- What a call of `thash4` on the lanes at `S + o` changes. -/
def t4ch (n : Nat) (S : Addr) (o st : Nat) : List Region :=
  (List.range 4).map (fun j => ⟨at' S (o + j * st + n + 32), n⟩) ++ [⟨S, workUsed⟩]

/-- The regions a call of `thash4` on the lanes at `S + o` is given: the lanes and `work`. -/
def t4wr (S : Addr) (o st : Nat) : List Region := [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]

theorem ce_gpr {s : State} (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr]; exact State.callEntry_gpr _ h

theorem toNat_at {S : Addr} {o : Nat} (hfit : S.toNat + 65536 ≤ 2 ^ 64) (ho : o < 65536) :
    (at' S o).toNat = S.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega_using [ho]),
    Nat.mod_eq_of_lt (by omega_using [hfit, ho])]

theorem sub_scr {S : Addr} {o len : Nat} (h : o + len ≤ 65536) : Region.Sub ⟨at' S o, len⟩ ⟨S, 65536⟩ :=
  Offset.sub_base S h

/-- The regions of the call are in the caller's writable regions. -/
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
theorem t4pre {n : Nat} {s : State} {S : Addr} {o st len : Nat} (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (ho : 1024 ≤ o) (hol : o + 4 * st ≤ 65536)
    (h0 : s.gpr .x0 = at' S o) (h1 : s.gpr .x1 = BitVec.ofNat 64 st) (h2 : s.gpr .x2 = BitVec.ofNat 64 len)
    (h3 : s.gpr .x3 = at' S (o + n + 32)) (h4 : s.gpr .x4 = S)
    (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st) (hno : n + 32 + n ≤ st) :
    (thash4Contract n).pre (s.callEntry.withRegions [] (t4wr S o st)) := by
  have hst' : (BitVec.ofNat 64 st).toNat = st := by rw [BitVec.toNat_ofNat]; omega_using [hol]
  have hlen' : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega_using [hol, hll]
  have g0 := ce_gpr (s := s) [] (t4wr S o st) (r := .x0) (by decide)
  have g1 := ce_gpr (s := s) [] (t4wr S o st) (r := .x1) (by decide)
  have g2 := ce_gpr (s := s) [] (t4wr S o st) (r := .x2) (by decide)
  have g3 := ce_gpr (s := s) [] (t4wr S o st) (r := .x3) (by decide)
  have g4 := ce_gpr (s := s) [] (t4wr S o st) (r := .x4) (by decide)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [g0, g1, g2, g3, g4, h0, h1, h2, h3, h4, hst', hlen']
  · rfl
  · exact Offset.disjoint_base S (by simp only [workLen]; omega_using [ho]) (by omega_using [hol])
  · rw [toNat_at hfit (by omega_using [hol, ho, hlp, hll])]; omega_using [hol, hfit]
  · simp only [workLen]; omega_using [hfit]
  · exact hlp
  · exact hlm
  · exact hll
  · rw [ofNat_add', Nat.add_assoc]
  · exact hno

/-- A call of `thash4` on the lanes at `S + o`. -/
theorem t4call_ok {n : Nat} (T : Thash4Impl n) (name : String) {s : State} {S : Addr} {o st len : Nat}
    (hscr : (⟨S, 65536⟩ : Region) ∈ s.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (ho : 1024 ≤ o) (hol : o + 4 * st ≤ 65536)
    (h0 : s.gpr .x0 = at' S o) (h1 : s.gpr .x1 = BitVec.ofNat 64 st) (h2 : s.gpr .x2 = BitVec.ofNat 64 len)
    (h3 : s.gpr .x3 = at' S (o + n + 32)) (h4 : s.gpr .x4 = S)
    (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st) (hno : n + 32 + n ≤ st) {Q : State → Prop}
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      (∀ j < 4, bytesAt s'.mem (at' S (o + j * st + n + 32)) n =
        shake256 (bytesAt s.mem (at' S (o + j * st)) len) n) →
      Frame (t4ch n S o st) s.mem s'.mem → Q s') :
    WP isa (.call name T.code) s Q := by
  have hst' : (BitVec.ofNat 64 st).toNat = st := by rw [BitVec.toNat_ofNat]; omega_using [hol]
  have hlen' : (BitVec.ofNat 64 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega_using [hol, hll]
  have hpre := t4pre (n := n) hfit ho hol h0 h1 h2 h3 h4 hlp hlm hll hno
  have hcov := t4cov (s := s) hscr hol
  refine WP.callV T.verified.1 hpre hcov.1 hcov.2 (fun s' hrd hwr hsp _ hcs _ hv hpost => k s' hrd hwr hsp hcs hv ?_ ?_)
    T.noFrames
  · intro j hj
    obtain ⟨hout, _⟩ := hpost
    have e1 := hout j hj
    simp only [outAt, msg, ce_gpr _ _ (show Reg.x0 ∉ linkRegs by decide), ce_gpr _ _ (show Reg.x1 ∉ linkRegs by decide),
      ce_gpr _ _ (show Reg.x2 ∉ linkRegs by decide), ce_gpr _ _ (show Reg.x3 ∉ linkRegs by decide), h0, h1, h2, h3,
      hst', hlen', ofNat_add', State.withRegions_mem, State.callEntry_mem] at e1
    rw [show o + j * st + n + 32 = o + n + 32 + j * st by omega_using [], e1]
  · obtain ⟨_, hfr⟩ := hpost
    simp only [State.withRegions_mem, State.callEntry_mem] at hfr
    refine hfr.sub fun r hr => ?_
    simp only [thash4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨j, hj, rfl⟩ | rfl
    · refine ⟨⟨at' S (o + j * st + n + 32), n⟩, List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩), ?_⟩
      simp only [outAt, ce_gpr _ _ (show Reg.x3 ∉ linkRegs by decide), ce_gpr _ _ (show Reg.x1 ∉ linkRegs by decide),
        h3, h1, hst', ofNat_add']
      rw [show o + n + 32 + j * st = o + j * st + n + 32 by omega_using []]
      exact fun _ h => h
    · refine ⟨⟨S, workUsed⟩, by simp [t4ch], ?_⟩
      simp only [ce_gpr _ _ (show Reg.x4 ∉ linkRegs by decide), h4]; exact fun _ h => h

/-! ## The layout, as numbers -/

theorem laneA_eq (k : Nat) : Layout.laneA k = 3136 + 128 * k := rfl
theorem laneB_eq (k : Nat) : Layout.laneB k = 3648 + 2208 * k := rfl
theorem oSave_eq (i : Nat) : Layout.oSave 0 i = 1024 + 8 * i := rfl
theorem oN_eq : Layout.oN = 12480 := rfl
theorem oVars_eq : Layout.oVars = 1024 := rfl
theorem oFrame0_eq : Layout.oFrame 0 = 1024 := rfl
theorem oDigits_eq : Layout.oDigits = 1856 := rfl
theorem oSkSeed_eq : Layout.oSkSeed = 1664 := rfl
theorem oSigTmp_eq : Layout.oSigTmp = 30144 := rfl
theorem nodeSlots_eq : Layout.nodeSlots = 520 := rfl
theorem strideA_eq : Layout.strideA = 128 := rfl
theorem strideB_eq : Layout.strideB = 2208 := rfl
theorem frameLen_eq : Layout.frameLen = 128 := rfl

/-! ## The entry state -/

variable (p : Params)

/-- The layout of `p`. -/
abbrev L : Layout := ⟨p.n, p.len⟩

/-- What the proof uses of the entry state `σ`: the arguments, and the
values of the working space. -/
structure Entry (σ : State) (S sig : Addr) (kp idx : Nat) (pkSeed a16 skSeed : List Byte) : Prop where
  x0 : σ.gpr .x0 = S
  x1 : σ.gpr .x1 = BitVec.ofNat 64 kp
  x2 : σ.gpr .x2 = BitVec.ofNat 64 idx
  x3 : σ.gpr .x3 = sig
  reg : Regions σ S [] ⟨sig, p.len * p.n⟩
  env : Env p σ.mem S pkSeed a16
  sk : SkAt p σ.mem S skSeed
  kp4 : kp % 4 = 0
  kpN : (kp + 4) * p.n ≤ 32 * Layout.nodeSlots
  idx32 : idx < 2 ^ 32
  dig : ∀ i < p.len, digitAt σ.mem S i < 16

/-- What `wotsLeaves4` may change: the contract's, and the signature. -/
abbrev wch (S sig : Addr) (kp : Nat) : List Region := wotsChanges p S kp ++ [⟨sig, p.len * p.n⟩]

/-- The callee-saved registers the code keeps fixed: `scratch`, `kp`,
`idx`, `sig`, and those it does not use. -/
abbrev BR : List Reg := [.x19, .x20, .x23, .x24, .x25, .x26, .x27, .x28]

theorem ne_of_mem {l : List Reg} {a b : Reg} (ha : a ∈ l) (hb : b ∉ l) : a ≠ b := fun e => hb (e ▸ ha)

variable {p} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-- What holds at every point of the code, from the entry state `σ`. -/
structure Base (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x19 : s.gpr .x19 = S
  x20 : s.gpr .x20 = BitVec.ofNat 64 kp
  x23 : s.gpr .x23 = BitVec.ofNat 64 idx
  x24 : s.gpr .x24 = sig
  keep : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], s.gpr r = σ.gpr r
  saved : ∀ i < 7, s.mem.readW (at' S (Layout.oSave 0 i)) 64 = σ.gpr (Wots.saved.getD i .x19)
  frame : Frame (wch p S sig kp) σ.mem s.mem

namespace Entry

variable (hE : Entry p σ S sig kp idx pkSeed a16 skSeed)
include hE

/-- A range of `scratch` is writable. -/
theorem inScr {s : State} (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ 65536) : InRegions s.wr (at' S o) n :=
  ⟨⟨S, 65536⟩, by rw [hw, hE.reg.wr_eq]; exact List.mem_cons_self .., Offset.contains_base S h (by
    have := hE.reg.scr_fit; simp only [scratchLen] at this; omega_using [this, h])⟩

theorem inScr' {s : State} (hw : s.wr = σ.wr) {o n : Nat} (h : o + n ≤ 65536) :
    InRegions (s.rd ++ s.wr) (at' S o) n := by
  obtain ⟨r, hr', hc⟩ := hE.inScr hw h
  exact ⟨r, List.mem_append_right _ hr', hc⟩

theorem scr_mem {s : State} (hw : s.wr = σ.wr) : (⟨S, 65536⟩ : Region) ∈ s.wr := by
  rw [hw, hE.reg.wr_eq]; exact List.mem_cons_self ..

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

end Entry

/-! ## The prologue -/

/-- After the saves: the registers as at entry, the first `j` saved. -/
structure SaveInv (σ : State) (S : Addr) (j : Nat) (t : State) : Prop where
  gpr : t.gpr = σ.gpr
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  saved : ∀ i < j, t.mem.readW (at' S (Layout.oSave 0 i)) 64 = σ.gpr (Wots.saved.getD i .x19)
  frame : Frame [⟨at' S (Layout.oFrame 0), Layout.frameLen⟩] σ.mem t.mem

theorem wp_range_map {f : Nat → Instr} {P : Nat → State → Prop} (K : Nat) {s : State} (h0 : P 0 s)
    (hs : ∀ j < K, ∀ t, P j t → WP isa (.block [f j]) t (P (j + 1))) :
    WP isa (.block ((List.range K).map f)) s (P K) := by
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap K h0 hs

theorem saveRegs_eq : saveRegs 0 .x0 Wots.saved =
    (List.range 7).map fun i => .str .x (Wots.saved.getD i .x19) .x0 (Layout.oSave 0 0 + 8 * i) := rfl

theorem saves_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) :
    WP isa (.block (saveRegs 0 .x0 Wots.saved)) σ (SaveInv σ S 7) := by
  rw [saveRegs_eq]
  refine wp_range_map 7 ⟨rfl, rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩
    fun j hj t ht => ?_
  refine wp_str (a := at' S (Layout.oSave 0 j)) ⟨by rw [oSave_eq]; omega_using [], by rw [oSave_eq]; omega_using [hj]⟩
    (by rw [ht.gpr, hE.x0, oSave_eq, oSave_eq])
    (hE.inScr ht.wr (by rw [oSave_eq]; omega_using [hj])) fun t' u => WP.block_nil ?_
  refine ⟨by rw [u.gpr, ht.gpr], by rw [u.sp, ht.sp], by rw [u.rd, ht.rd], by rw [u.wr, ht.wr], fun i hi => ?_, ?_⟩
  · rw [u.mem]
    by_cases e : i = j
    · subst e; rw [Mem.readW_writeW_self64, ht.gpr]
    · rw [Mem.readW_writeW_sep (Offset.sep S (by rw [oSave_eq, oSave_eq]; omega_using [e, hi, hj])
        (by rw [oSave_eq]; omega_using [hi, hj]) (by rw [oSave_eq]; omega_using [hj])) (by decide),
        ht.saved i (by omega_using [hi, e])]
  · rw [u.mem]
    refine ht.frame.writeW (List.mem_singleton_self _) _ ?_
    show (⟨S + BitVec.ofNat 64 1024, 128⟩ : Region).Contains (S + BitVec.ofNat 64 (1024 + 8 * j)) 8
    rw [← ofNat_add']
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-! ## Fields of the lanes -/

/-- The low halves of v8–v15 of `a` are `b`'s. -/
def VK (a b : State) : Prop := ∀ r ∈ preservedV, (a.v r).extractLsb' 0 64 = (b.v r).extractLsb' 0 64

theorem VK.trans {a b c : State} (h₁ : VK a b) (h₂ : VK b c) : VK a c := fun r hr => (h₁ r hr).trans (h₂ r hr)
theorem VK.refl (a : State) : VK a a := fun _ _ => rfl

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

/-- A frame of a range within `R` extends a frame of the regions that include `R`. -/
theorem frame_ext {rs : List Region} {m₀ m m' : Mem} (h₀ : Frame rs m₀ m) {R : Region} (hR : R ∈ rs)
    {r : Region} (hr : Region.Sub r R) (h : Frame [r] m m') : Frame rs m₀ m' :=
  h₀.trans (h.sub fun _ hx => by simp only [List.mem_singleton] at hx; subst hx; exact ⟨R, hR, hr⟩)

theorem frame_cat {rs rs' : List Region} {m₁ m₂ m₃ : Mem} (h₁ : Frame rs m₁ m₂) (h₂ : Frame rs' m₂ m₃) :
    Frame (rs ++ rs') m₁ m₃ :=
  (h₁.mono fun _ hr => List.mem_append_left _ hr).trans (h₂.mono fun _ hr => List.mem_append_right _ hr)

theorem tailA_mem (k : Nat) (hk : k < 4) (S sig : Addr) (kp : Nat) :
    (⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩ : Region) ∈ wch p S sig kp := by
  simp only [wch, wotsChanges, laneTails, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨k, hk, List.mem_cons_self ..⟩))

theorem tailB_mem (k : Nat) (hk : k < 4) (S sig : Addr) (kp : Nat) :
    (⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩ : Region) ∈ wch p S sig kp := by
  simp only [wch, wotsChanges, laneTails, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨k, hk, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))

theorem work_mem (S sig : Addr) (kp : Nat) : (⟨S, workUsed⟩ : Region) ∈ wch p S sig kp := by
  simp [wch, wotsChanges]

theorem frame0_mem (S sig : Addr) (kp : Nat) :
    (⟨at' S (Layout.oFrame 0), Layout.frameLen⟩ : Region) ∈ wch p S sig kp := by
  simp [wch, wotsChanges]

theorem sig_mem (S sig : Addr) (kp : Nat) : (⟨sig, p.len * p.n⟩ : Region) ∈ wch p S sig kp := by
  simp [wch]

theorem nodes_mem (S sig : Addr) (kp : Nat) :
    (⟨at' S (Layout.oN + kp * p.n), 4 * p.n⟩ : Region) ∈ wch p S sig kp := by
  simp [wch, wotsChanges]

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

/-- The saved registers, in frame 0. -/
abbrev saveR (S : Addr) : Region := ⟨at' S 1024, 56⟩

theorem keep_BR {r : Reg} (h : r ∈ [Reg.x25, .x26, .x27, .x28]) : r ∈ BR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem Base.step {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} {t t' : State} (hb : Base hE t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ BR, t'.gpr r = t.gpr r)
    {R : Region} (hR : R ∈ wch p S sig kp) {r : Region} (hr : Region.Sub r R)
    (hf : Frame [r] t.mem t'.mem) (hsv : ∀ i < 7, t'.mem.readW (at' S (Layout.oSave 0 i)) 64 =
      t.mem.readW (at' S (Layout.oSave 0 i)) 64) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hsp, hb.sp], by rw [hg _ (by simp), hb.x19],
    by rw [hg _ (by simp), hb.x20], by rw [hg _ (by simp), hb.x23], by rw [hg _ (by simp), hb.x24],
    fun r hr => by rw [hg r (keep_BR hr), hb.keep r hr],
    fun i hi => by rw [hsv i hi, hb.saved i hi], frame_ext hb.frame hR hr hf⟩

/-- `Base` through a change of registers only. -/
theorem Base.regs {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} {t t' : State} (hb : Base hE t)
    (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ BR, t'.gpr r = t.gpr r) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hsp, hb.sp], by rw [hg _ (by simp), hb.x19],
    by rw [hg _ (by simp), hb.x20], by rw [hg _ (by simp), hb.x23], by rw [hg _ (by simp), hb.x24],
    fun r hr => by rw [hg r (keep_BR hr), hb.keep r hr],
    fun i hi => by rw [hm, hb.saved i hi], by rw [hm]; exact hb.frame⟩

/-- A write of 4 bytes in a lane tail keeps the saved registers. -/
theorem saved_keep {m m' : Mem} {S : Addr} {a : Nat} (hf : Frame [⟨at' S a, 4⟩] m m') (ha : 3136 ≤ a) (ha' : a + 4 ≤ 65536)
    (i : Nat) (hi : i < 7) : m'.readW (at' S (Layout.oSave 0 i)) 64 = m.readW (at' S (Layout.oSave 0 i)) 64 :=
  hf.readW (r := ⟨at' S (Layout.oSave 0 i), 8⟩) (by simp [Region.Contains])
    (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact Entry.dscr (Or.inl (by rw [oSave_eq]; omega_using [hi, ha])) (by rw [oSave_eq]; omega_using [hi]) ha')
    (by decide)

/-- A 4-byte range of a lane tail of `A` or `B`. -/
def InTail (p : Params) (a : Nat) : Prop :=
  ∃ k < 4, (Layout.laneA k + p.n + 16 ≤ a ∧ a + 4 ≤ Layout.laneA k + Layout.strideA) ∨
    (Layout.laneB k + p.n + 16 ≤ a ∧ a + 4 ≤ Layout.laneB k + Layout.strideB)

theorem InTail.sub {a : Nat} (h : InTail p a) (S sig : Addr) (kp : Nat) :
    ∃ R ∈ wch p S sig kp, Region.Sub ⟨at' S a, 4⟩ R := by
  obtain ⟨k, hk, hA | hB⟩ := h
  · refine ⟨_, tailA_mem k hk S sig kp, ?_⟩
    have e := sub_tailA (p := p) (S := S) (k := k) (a := a - Layout.laneA k) (l := 4) (by omega_using [hA])
      (by omega_using [hA])
    rwa [Nat.add_sub_cancel' (by omega_using [hA])] at e
  · refine ⟨_, tailB_mem k hk S sig kp, ?_⟩
    have e := sub_tailB (p := p) (S := S) (k := k) (a := a - Layout.laneB k) (l := 4) (by omega_using [hB])
      (by omega_using [hB])
    rwa [Nat.add_sub_cancel' (by omega_using [hB])] at e

theorem InTail.lo {a : Nat} (h : InTail p a) : 3136 ≤ a := by
  obtain ⟨k, hk, hA | hB⟩ := h
  · rw [laneA_eq] at hA; omega_using [hA]
  · rw [laneB_eq] at hB; omega_using [hB]

theorem InTail.hi {a : Nat} (h : InTail p a) : a + 4 ≤ 12480 := by
  obtain ⟨k, hk, hA | hB⟩ := h
  · rw [laneA_eq, strideA_eq] at hA; omega_using [hA, hk]
  · rw [laneB_eq, strideB_eq] at hB; omega_using [hB, hk]

variable {is : List Instr} {Q : State → Prop}

/-- `setFieldR` in a lane tail, with `Base`. -/
theorem setFieldR_base (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) {t : State} (hb : Base hE t) {a : Nat}
    {r : Reg} (ha : InTail p a) (ha4 : a % 4 = 0) (hr : (t.gpr r).toNat < 2 ^ 32)
    (k : ∀ t', Base hE t' → (∀ g, g ≠ .x9 → t'.gpr g = t.gpr g) →
      bytesAt t'.mem (at' S a) 4 = toByte (t.gpr r).toNat 4 → Frame [⟨at' S a, 4⟩] t.mem t'.mem →
      WP isa (.block is) t' Q) :
    WP isa (.block (setFieldR .x19 a r ++ is)) t Q := by
  have hhi := ha.hi
  refine setFieldR_ok (by decide) ⟨ha4, by omega_using [hhi]⟩ hr
    (by rw [hb.x19]; exact hE.inScr hb.wr (by omega_using [hhi])) fun t' f => ?_
  rw [hb.x19] at f
  obtain ⟨R, hR, hs⟩ := ha.sub S sig kp
  exact k t' (hb.step f.rd f.wr f.sp (fun g hg => f.gpr g (ne_of_mem hg (by decide))) hR hs f.frame
    (saved_keep f.frame ha.lo (by omega_using [hhi]))) f.gpr f.bytes f.frame

/-- `setField` in a lane tail, with `Base`. -/
theorem setField_base (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) {t : State} (hb : Base hE t) {a v : Nat}
    (ha : InTail p a) (ha4 : a % 4 = 0) (hv : FieldV v)
    (k : ∀ t', Base hE t' → (∀ g, g ≠ .x9 → t'.gpr g = t.gpr g) →
      bytesAt t'.mem (at' S a) 4 = toByte v 4 → Frame [⟨at' S a, 4⟩] t.mem t'.mem →
      WP isa (.block is) t' Q) :
    WP isa (.block (setField .x19 a v ++ is)) t Q := by
  have hhi := ha.hi
  refine setField_ok (by decide) ⟨ha4, by omega_using [hhi]⟩ hv
    (by rw [hb.x19]; exact hE.inScr hb.wr (by omega_using [hhi])) fun t' f => ?_
  rw [hb.x19] at f
  obtain ⟨R, hR, hs⟩ := ha.sub S sig kp
  exact k t' (hb.step f.rd f.wr f.sp (fun g hg => f.gpr g (ne_of_mem hg (by decide))) hR hs f.frame
    (saved_keep f.frame ha.lo (by omega_using [hhi]))) f.gpr f.bytes f.frame

/-- Four bytes of `scratch` that writes of four bytes elsewhere leave. -/
theorem keep4 {m m' : Mem} {S : Addr} {as : List Nat} (hf : Frame (as.map fun a => ⟨at' S a, 4⟩) m m') {b : Nat}
    (h : ∀ a ∈ as, (a + 4 ≤ b ∨ b + 4 ≤ a) ∧ a + 4 ≤ 65536) (hb : b + 4 ≤ 65536) :
    bytesAt m' (at' S b) 4 = bytesAt m (at' S b) 4 :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact Entry.dscr (Or.symm (h a ha).1) hb (h a ha).2) (by decide)

theorem Entry.kp_lt (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) : kp + 4 ≤ 1040 := by
  have h2 : (kp + 4) * 16 ≤ (kp + 4) * p.n := Nat.mul_le_mul_left _ hz.n16
  have h3 := hE.kpN
  rw [nodeSlots_eq] at h3
  omega_using [h2, h3]

/-! ## The setup -/

/-- Lane `k`'s fields after the setup. -/
structure LaneSet (p : Params) (m : Mem) (S : Addr) (kp k : Nat) : Prop where
  a20 : fA p m S k 20 = toByte (kp + k) 4
  b16 : fB p m S k 16 = toByte 1 4
  b20 : fB p m S k 20 = toByte (kp + k) 4
  b24 : fB p m S k 24 = toByte 0 4
  b28 : fB p m S k 28 = toByte 0 4

/-- The fields of lane `k` that the setup writes. -/
def setupOffs (p : Params) (k : Nat) : List Nat :=
  [Layout.laneA k + p.n + 20, Layout.laneB k + p.n + 20, Layout.laneB k + p.n + 16, Layout.laneB k + p.n + 24,
    Layout.laneB k + p.n + 28]

theorem setupOffs_tail (hz : Sz p) {k : Nat} (hk : k < 4) : ∀ a ∈ setupOffs p k, InTail p a ∧ a % 4 = 0 := by
  have := hz.n32
  have h8 := hz.n8
  intro a ha
  simp only [setupOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨k, hk, Or.inl (by rw [strideA_eq]; omega_using [this])⟩, by rw [laneA_eq]; omega_using [h8]⟩
  all_goals exact ⟨⟨k, hk, Or.inr (by rw [strideB_eq]; omega_using [this])⟩, by rw [laneB_eq]; omega_using [h8]⟩

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

theorem setupLane_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k : Nat} (hk : k < 4)
    {t : State} (hb : Base hE t) (hl : ∀ k' < k, LaneSet p t.mem S kp k') :
    WP isa (.block (([.addImm .x .x10 .x20 k] : List Instr) ++
      setFieldR .x19 (Layout.laneA k + (L p).adrsOff + 20) .x10 ++
      setFieldR .x19 (Layout.laneB k + (L p).adrsOff + 20) .x10 ++
      setField .x19 (Layout.laneB k + (L p).adrsOff + 16) 1 ++ setField .x19 (Layout.laneB k + (L p).adrsOff + 24) 0 ++
      setField .x19 (Layout.laneB k + (L p).adrsOff + 28) 0)) t
      (fun t' => (Base hE t' ∧ ∀ k' < k + 1, LaneSet p t'.mem S kp k') ∧
        Frame ((setupOffs p k).map fun a => (⟨at' S a, 4⟩ : Region)) t.mem t'.mem) := by
  have hn := hz.n32
  have hkp := hE.kp_lt hz
  have ht := setupOffs_tail hz hk
  simp only [List.append_assoc, List.cons_append, List.nil_append, Layout.adrsOff]
  refine wp_addImm (by omega_using [hk]) fun t₂ u₂ => ?_
  have hr10 : t₂.gpr .x10 = BitVec.ofNat 64 (kp + k) := by
    rw [u₂.gpr, hb.x20, ← BitVec.ofNat_add]
  have hb₂ : Base hE t₂ := hb.regs u₂.mem u₂.rd u₂.wr u₂.sp (fun g hg => u₂.other _ (ne_of_mem hg (by decide)))
  have hv : (t₂.gpr .x10).toNat = kp + k := by
    rw [hr10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hkp, hk])]
  have hlt : (t₂.gpr .x10).toNat < 2 ^ 32 := by rw [hv]; omega_using [hkp, hk]
  rw [← List.append_nil (setField .x19 (Layout.laneB k + p.n + 28) 0)]
  refine setFieldR_base hE hb₂ (ht _ (by simp [setupOffs])).1 (ht _ (by simp [setupOffs])).2 hlt
    fun t₃ b₃ g₃ y₃ f₃ => ?_
  have hr3 : t₃.gpr .x10 = t₂.gpr .x10 := g₃ _ (by decide)
  refine setFieldR_base hE b₃ (ht _ (by simp [setupOffs])).1 (ht _ (by simp [setupOffs])).2 (by rw [hr3]; exact hlt)
    fun t₄ b₄ _ y₄ f₄ => ?_
  refine setField_base hE b₄ (ht _ (by simp [setupOffs])).1 (ht _ (by simp [setupOffs])).2 (by decide)
    fun t₅ b₅ _ y₅ f₅ => ?_
  refine setField_base hE b₅ (ht _ (by simp [setupOffs])).1 (ht _ (by simp [setupOffs])).2 (by decide)
    fun t₆ b₆ _ y₆ f₆ => ?_
  refine setField_base hE b₆ (ht _ (by simp [setupOffs])).1 (ht _ (by simp [setupOffs])).2 (by decide)
    fun t₇ b₇ _ y₇ f₇ => ?_
  rw [hr3, hv] at y₄
  rw [hv] at y₃
  have hf : Frame ((setupOffs p k).map fun a => (⟨at' S a, 4⟩ : Region)) t.mem t₇.mem := by
    have := frame_cat (frame_cat (frame_cat (frame_cat f₃ f₄) f₅) f₆) f₇
    rw [u₂.mem] at this; exact this
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
structure SetupPost (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (t : State) : Prop where
  base : Base hE t
  x21 : t.gpr .x21 = 0
  lanes : ∀ k < 4, LaneSet p t.mem S kp k
  scr : Frame [⟨S, Layout.oSigTmp⟩] σ.mem t.mem

theorem add0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := by simp

theorem setup_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) :
    WP isa (.block (Wots.pro ++ Wots.setup (L p))) σ (SetupPost hE) := by
  rw [Wots.pro, List.append_assoc]
  refine WP.block_append (WP.mono (saves_ok hE) fun t ht => ?_)
  simp only [Thash4.mov, List.cons_append, List.nil_append]
  refine wp_addImm (by decide) fun t₁ u₁ => wp_addImm (by decide) fun t₂ u₂ => wp_addImm (by decide) fun t₃ u₃ =>
    wp_addImm (by decide) fun t₄ u₄ => ?_
  have hb : Base hE t₄ := by
    refine ⟨by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, ht.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, ht.wr],
      by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, ht.sp],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ht.gpr, hE.x0, add0],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), ht.gpr, hE.x1, add0],
      by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), ht.gpr, hE.x2, add0],
      by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht.gpr, hE.x3, add0],
      fun r hr => ?_, fun i hi => by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, ht.saved i hi], ?_⟩
    · have h₁ : r ≠ .x19 := ne_of_mem hr (by decide)
      have h₂ : r ≠ .x20 := ne_of_mem hr (by decide)
      have h₃ : r ≠ .x23 := ne_of_mem hr (by decide)
      have h₄ : r ≠ .x24 := ne_of_mem hr (by decide)
      rw [u₄.other _ h₄, u₃.other _ h₃, u₂.other _ h₂, u₁.other _ h₁, ht.gpr]
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact ht.frame.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact frame0_mem S sig kp
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
        exact ⟨_, List.mem_singleton_self _, hsub (by rw [oFrame0_eq, frameLen_eq, oSigTmp_eq]; decide)⟩⟩
    fun j hj t ht => WP.mono (setupLane_ok hE hz hj ht.1.1 ht.1.2) fun t' h => ⟨h.1, ht.2.trans (h.2.sub fun r hr => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      refine ⟨_, List.mem_singleton_self _, hsub ?_⟩
      simp only [setupOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp only [laneA_eq, laneB_eq, oSigTmp_eq] <;>
        omega_using [hj, hn])⟩) fun t ht => ?_)
  refine wp_movz fun t' u => WP.block_nil ⟨ht.1.1.regs u.mem u.rd u.wr u.sp (fun g hg => u.other g (ne_of_mem hg (by decide))),
    by rw [u.gpr]; rfl, by rw [u.mem]; exact ht.1.2, by rw [u.mem]; exact ht.2⟩

/-! ## What `wotsLeaves4` never changes -/

/-- A range of `scratch` outside what `wch` allows to change: frames 1 to 3,
the keys, the digest, the digits, …, and the lanes' `PK.seed` and `a16`. -/
def Out (p : Params) (a l : Nat) : Prop :=
  (1152 ≤ a ∧ a + l ≤ 3136) ∨ (3136 ≤ a ∧ a + l ≤ 3648 ∧ (a - 3136) % 128 + l ≤ p.n + 16) ∨
    (3648 ≤ a ∧ a + l ≤ 12480 ∧ (a - 3648) % 2208 + l ≤ p.n + 16)

theorem Out.disj (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {a l : Nat} (h : Out p a l) :
    ∀ R ∈ wch p S sig kp, Region.Disjoint ⟨at' S a, l⟩ R := by
  have hn := hz.n32
  have ha : a + l ≤ 12480 := by unfold Out at h; omega_using [h]
  intro R hR
  simp only [wch, wotsChanges, laneTails, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hR
  rcases hR with (((rfl | rfl) | ⟨k, hk, rfl | rfl⟩) | rfl) | rfl
  · exact Offset.disjoint_base S (by simp only [workUsed]; unfold Out at h; omega_using [h]) (by omega_using [ha])
  · exact Entry.dscr (by rw [oFrame0_eq, frameLen_eq]; unfold Out at h; omega_using [h]) (by omega_using [ha]) (by decide)
  · exact Entry.dscr (by unfold Out at h; rw [laneA_eq, strideA_eq]; omega_using [h, hk, hn]) (by omega_using [ha])
      (by rw [laneA_eq, strideA_eq]; omega_using [hk, hn])
  · exact Entry.dscr (by unfold Out at h; rw [laneB_eq, strideB_eq]; omega_using [h, hk, hn]) (by omega_using [ha])
      (by rw [laneB_eq, strideB_eq]; omega_using [hk, hn])
  · have hkp : kp * p.n + 4 * p.n ≤ 16640 := by have := hE.kpN; rw [nodeSlots_eq, Nat.add_mul] at this; exact this
    exact Entry.dscr (by rw [oN_eq]; omega_using [ha, hkp]) (by omega_using [ha]) (by rw [oN_eq]; omega_using [hkp])
  · exact (hE.reg.out_scr.sub_right (Offset.sub_base S (by rw [oSigTmp_eq]; omega_using [ha]))).symm

theorem Base.bytes {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t)
    {a l : Nat} (h : Out p a l) : bytesAt t.mem (at' S a) l = bytesAt σ.mem (at' S a) l :=
  bytesAt_frame hb.frame (h.disj hE hz) (by unfold Out at h; omega_using [h])

theorem Base.env {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t) :
    Env p t.mem S pkSeed a16 := by
  have hn := hz.n32
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hb.bytes hz (by unfold Out; rw [laneA_eq]; right; left; omega_using [hk, hn])]; exact hE.env.seedA k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneB_eq]; right; right; omega_using [hk, hn])]; exact hE.env.seedB k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneA_eq]; right; left; omega_using [hk, hn])]; exact hE.env.adrsA k hk
  · rw [hb.bytes hz (by unfold Out; rw [laneB_eq]; right; right; omega_using [hk, hn])]; exact hE.env.adrsB k hk

theorem Base.sk {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t) :
    SkAt p t.mem S skSeed := by
  have hn := hz.n32
  unfold SkAt; rw [hb.bytes hz (by unfold Out; rw [oSkSeed_eq]; left; omega_using [hn])]; exact hE.sk

theorem Base.digit {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} (hz : Sz p) {t : State} (hb : Base hE t)
    {i : Nat} (hi : i < p.len) : t.mem (at' S (Layout.oDigits + i)) = σ.mem (at' S (Layout.oDigits + i)) := by
  have hn := hz.n32; have hl := hz.len
  have := hb.frame.bytes (R := ⟨at' S (Layout.oDigits + i), 1⟩)
    (Out.disj hE hz (by unfold Out; rw [oDigits_eq]; left; omega_using [hi, hn, hl])) (by show 1 ≤ 2 ^ 64; decide)
    (i := 0) (by show 0 < 1; decide)
  simpa using this

/-! ## The calls of `thash4` -/

/-- `Base` through a change of memory in ranges of `wch` away from the saved registers. -/
theorem Base.ofFrame {hE : Entry p σ S sig kp idx pkSeed a16 skSeed} {t t' : State} (hb : Base hE t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hg : ∀ r ∈ BR, t'.gpr r = t.gpr r)
    {rs : List Region} (hf : Frame rs t.mem t'.mem) (hs : ∀ r ∈ rs, ∃ R ∈ wch p S sig kp, Region.Sub r R)
    (hsv : ∀ r ∈ rs, Region.Disjoint (saveR S) r) : Base hE t' :=
  ⟨by rw [hrd, hb.rd], by rw [hwr, hb.wr], by rw [hsp, hb.sp], by rw [hg _ (by simp), hb.x19],
    by rw [hg _ (by simp), hb.x20], by rw [hg _ (by simp), hb.x23], by rw [hg _ (by simp), hb.x24],
    fun r hr => by rw [hg r (keep_BR hr), hb.keep r hr],
    fun i hi => by
      rw [hf.readW (r := ⟨at' S (Layout.oSave 0 i), 8⟩) (by simp [Region.Contains])
        (fun r hr => (hsv r hr).sub_left (by
          rw [oSave_eq]
          show Region.Sub ⟨S + BitVec.ofNat 64 (1024 + 8 * i), 8⟩ ⟨S + BitVec.ofNat 64 1024, 56⟩
          rw [← ofNat_add']; exact Offset.sub_base _ (by omega_using [hi]))) (by decide), hb.saved i hi],
    hb.frame.trans (hf.sub hs)⟩

/-- The lanes of `A` or of `B`. -/
def Lanes (o st : Nat) : Prop := (o = 3136 ∧ st = 128) ∨ (o = 3648 ∧ st = 2208)

theorem Lanes.out_sub {o st : Nat} (h : Lanes o st) (hz : Sz p) {j : Nat} (hj : j < 4) (S sig : Addr) (kp : Nat) :
    ∃ R ∈ wch p S sig kp, Region.Sub ⟨at' S (o + j * st + p.n + 32), p.n⟩ R := by
  have hn := hz.n32
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨_, tailA_mem j hj S sig kp, ?_⟩
    have e := sub_tailA (p := p) (S := S) (k := j) (a := p.n + 32) (l := p.n) (by omega_using [])
      (by rw [strideA_eq]; omega_using [hn])
    rwa [laneA_eq, show 3136 + 128 * j + (p.n + 32) = 3136 + j * 128 + p.n + 32 by omega_using []] at e
  · refine ⟨_, tailB_mem j hj S sig kp, ?_⟩
    have e := sub_tailB (p := p) (S := S) (k := j) (a := p.n + 32) (l := p.n) (by omega_using [])
      (by rw [strideB_eq]; omega_using [hn])
    rwa [laneB_eq, show 3648 + 2208 * j + (p.n + 32) = 3648 + j * 2208 + p.n + 32 by omega_using []] at e

/-- What a call of `thash4` changes is in `wch`, away from the saved registers. -/
theorem t4Changes_ok (hz : Sz p) {o st : Nat} (hl : Lanes o st) (S sig : Addr) (kp : Nat) :
    ∀ r ∈ t4ch p.n S o st, (∃ R ∈ wch p S sig kp, Region.Sub r R) ∧ Region.Disjoint (saveR S) r := by
  have hn := hz.n32
  intro r hr
  simp only [t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl
  · refine ⟨hl.out_sub hz hj S sig kp, Entry.dscr ?_ (by decide) ?_⟩ <;>
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega_using [hj, hn]
  · exact ⟨⟨_, work_mem S sig kp, fun _ h => h⟩, Offset.disjoint_base S (by decide) (by decide)⟩

/-- What the arguments of a call of `thash4` on the lanes at `o` leave, from `t`. -/
structure ArgsPost (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (t u : State) (o st len : Nat) : Prop where
  base : Base hE u
  mem : u.mem = t.mem
  vk : VK u t
  gpr : ∀ g ∉ [Reg.x0, .x1, .x2, .x3, .x4], u.gpr g = t.gpr g
  x0 : u.gpr .x0 = at' S o
  x1 : u.gpr .x1 = BitVec.ofNat 64 st
  x2 : u.gpr .x2 = BitVec.ofNat 64 len
  x3 : u.gpr .x3 = at' S (o + p.n + 32)
  x4 : u.gpr .x4 = S

theorem thashArgs_eq (L : Layout) {o : Nat} (ho : o < 4096) (st len : Nat) :
    thashArgs L o st len = [.addImm .x .x0 .x19 o, .movz .x .x1 (BitVec.ofNat 16 st) 0,
      .movz .x .x2 (BitVec.ofNat 16 len) 0, .addImm .x .x3 .x0 L.msgOff, .addImm .x .x4 .x19 0] := by
  simp [thashArgs, lea, ho, Thash4.mov]

theorem movz_ofNat {v : Nat} (hv : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega_using [hv])]

/-- The arguments of a call of `thash4` on the lanes at `o`, from a state with `Base`. -/
theorem targs_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {o st len : Nat} (hl : Lanes o st)
    (hll : len ≤ st) {t : State} (hb : Base hE t) :
    WP isa (.block (thashArgs (L p) o st len)) t (fun u => ArgsPost hE t u o st len) := by
  have hn := hz.n32
  have hst : st < 65536 := by rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have ho : o < 4096 := by rcases hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  rw [thashArgs_eq _ ho]
  refine wp_vk rfl ?_
  refine wp_addImm ho fun t₁ u₁ => wp_movz fun t₂ u₂ => wp_movz fun t₃ u₃ =>
    wp_addImm (by simp only [Layout.msgOff]; omega_using [hn]) fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ =>
      WP.block_nil fun hvk => ?_
  have hm : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg : ∀ g ∉ [Reg.x0, .x1, .x2, .x3, .x4], t₅.gpr g = t.gpr g := fun g h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    rw [u₅.other _ h.2.2.2.2, u₄.other _ h.2.2.2.1, u₃.other _ h.2.2.1, u₂.other _ h.2.1, u₁.other _ h.1]
  have h0 : t₁.gpr .x0 = at' S o := by rw [u₁.gpr, hb.x19]
  refine ⟨hb.regs hm (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun g h' => hg g (by revert h'; revert g; decide)), hm, hvk, hg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h0]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, movz_ofNat hst]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, movz_ofNat (by omega_using [hst, hll])]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h0]
    simp only [Layout.msgOff]
    rw [ofNat_add', Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb.x19, add0]

theorem pres_not_args : ∀ r ∈ preserved, r ∉ [Reg.x0, .x1, .x2, .x3, .x4] := by decide

/-- A call of `thash4` on the lanes at `o`, from a state with `Base`. -/
theorem tcall_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {o st len : Nat} (hl : Lanes o st) (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    {t : State} (hb : Base hE t) {Q : State → Prop}
    (k : ∀ t', Base hE t' → (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) → VK t' t →
      (∀ j < 4, bytesAt t'.mem (at' S (o + j * st + p.n + 32)) p.n =
        shake256 (bytesAt t.mem (at' S (o + j * st)) len) p.n) →
      Frame (t4ch p.n S o st) t.mem t'.mem → Q t') :
    WP isa (thashCall (L p) name T.code o st len) t Q := by
  have hn := hz.n32
  refine WP.seq (WP.mono (targs_ok hE hz hl hll hb) fun t₅ a => ?_)
  have hb₅ := a.base
  have hm := a.mem
  refine t4call_ok T name (s := t₅) (S := S) (o := o) (st := st) (len := len)
    (hE.scr_mem hb₅.wr) hE.scr_fit
    (by rcases hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide)
    (by rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) a.x0 a.x1 a.x2 a.x3 a.x4
    hlp hlm hll (by rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega_using [hn]) fun t' h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_
  rw [hm] at h₆ h₇
  have hc := t4Changes_ok hz hl S sig kp
  have hpr : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r := fun r hr h30 => by
    rw [h₄ r hr h30]
    exact a.gpr _ (pres_not_args r hr)
  exact k t' (hb₅.ofFrame h₁ h₂ h₃ (fun g hg' => h₄ g (by revert hg'; revert g; decide) (by revert hg'; revert g; decide))
      (by rw [hm]; exact h₇) (fun r hr => (hc r hr).1) fun r hr => (hc r hr).2)
    hpr (VK.trans h₅ a.vk) h₆ h₇

end VG.Proof.SlhDsa.AArch64.Wots4
