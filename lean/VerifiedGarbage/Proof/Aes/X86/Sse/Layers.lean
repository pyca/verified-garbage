module

public import VerifiedGarbage.Impl.Aes.X86.Sse
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.X86.StraightSse
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The layers of bitsliced AES in SSE2 registers on x86 (32-bit), by evaluation

Each piece of straight-line code is evaluated by the kernel: the S-boxes on
truth tables of 256 rows (`sub_ok`), and what only moves and adds bits on
words of atoms (`lin_ok`), compared with the pairs (slice, position) whose
bits each bit of the result adds (`Proof/Aes/Bitsliced.lean`, with `B = 8`).
Slices are where a function to `Loc` says: in registers and in slots.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.X86.StraightSse VG.Bitslice VG.Impl.Aes.X86.Sse VG.Proof.Aes

/-! ## The evaluator, without a table of constants -/

/-- `k` slots at `b`, and `n` words at `e`. -/
def cfgAt (b : Reg) (k : Nat) (e : Reg) (n : Nat) : Cfg :=
  { base := b, slots := k, ext := e, exts := n, tbl := .ebp, name := "", words := [] }

/-- The slots, and `n` words at `eax`. -/
abbrev cfg (n : Nat) : Cfg := cfgAt .edi 18 .eax n

def sseOnly (is : List Instr) : Bool :=
  is.all fun | .xop _ | .movdquLoad .. | .movdquStore .. => true | _ => false

/-- SSE2 instructions do not depend on the addresses of symbols, nor change them. -/
theorem exec_syms {i : Instr} (h : sseOnly [i] = true) (σ : String → BitVec 32) (s : State) :
    exec i { s with syms := σ } = (exec i s).map fun t => { t with syms := σ } := by
  cases i with
  | xop o => cases o <;> rfl
  | movdquLoad d m =>
    show Option.map _ (s.load128 (s.ea m)) = Option.map _ (Option.map _ (s.load128 (s.ea m)))
    rw [Option.map_map]; rfl
  | movdquStore m r =>
    simp only [exec, State.store128]
    show (if InRegions s.wr (s.ea m) 16 then _ else none) = Option.map _ (if InRegions s.wr (s.ea m) 16 then _ else none)
    split <;> rfl
  | _ => cases h

theorem runBlock_syms {is : List Instr} (h : sseOnly is = true) (σ : String → BitVec 32) (s : State) :
    runBlock isa is { s with syms := σ } = (runBlock isa is s).map fun t => { t with syms := σ } := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [sseOnly, List.all_cons, Bool.and_eq_true] at h ih
    show (exec i { s with syms := σ }).bind (runBlock isa is) = ((exec i s).bind (runBlock isa is)).map _
    rw [exec_syms (by simp only [sseOnly, List.all_cons, List.all_nil, Bool.and_true]; exact h.1)]
    cases exec i s with
    | none => rfl
    | some t => exact ih h.2 t

/-- What the machine needs. -/
structure OkAt (b : Reg) (k : Nat) (e : Reg) (n : Nat) (s : State) : Prop where
  slotIn : ∀ j < k, InRegions s.wr (xAddr (s.gpr b) j) 16
  extIn : ∀ j < n, InRegions (s.rd ++ s.wr) (xAddr (s.gpr e) j) 16
  fit : (s.gpr b).toNat + 16 * k ≤ 2 ^ 32
  sep : ∀ i < k, ∀ j < n, Mem.Sep (xAddr (s.gpr b) i) 16 (xAddr (s.gpr e) j) 16

abbrev Ok (n : Nat) (s : State) : Prop := OkAt .edi 18 .eax n s

theorem run' {α : Type} {D : XDom α} {R : α → BitVec 128 → Prop} (hD : D.Sound R) {b e : Reg} {k n : Nat}
    {ext : Nat → Option α} {is : List Instr} {v v' : StraightSse.Env α} {s : State} (hs : sseOnly is = true)
    (hok : OkAt b k e n s) (hrel : Rel R (cfgAt b k e n) ext v s) (h : eval D (cfgAt b k e n) ext is v = some v') :
    ∃ s', runBlock isa is s = some s' ∧ Post R (cfgAt b k e n) ext v' s s' is := by
  obtain ⟨t, ht, p⟩ := run hD (s := { s with syms := fun _ => s.gpr .ebp })
    ⟨hok.slotIn, hok.extIn, hok.fit, hok.sep, rfl⟩ ⟨hrel.reg, hrel.slot, hrel.ext⟩ h
  rw [runBlock_syms hs] at ht
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp ht
  have hsy : s'.syms = s.syms := by
    have := runBlock_syms hs s.syms s
    rw [show ({ s with syms := s.syms } : State) = s from rfl, hs'] at this
    have h2 : s' = { s' with syms := s.syms } := Option.some.inj this
    have h3 := congrArg State.syms h2
    exact h3
  refine ⟨s', hs', ⟨p.rel.reg, p.rel.slot, p.rel.ext⟩, ?_, p.other, p.kept, p.frame⟩
  have ho := congrArg (fun x : State => { x with syms := s.syms }) p.only
  exact (show s' = { s' with syms := s.syms } by rw [← hsy]).trans ho

/-! ## Where slices are -/

/-- What is at `l`. -/
def locVal (s : State) : Loc → BitVec 128
  | .x r => s.xmm r
  | .m k => s.mem.readW (xAddr (s.gpr .edi) k) 128

def locAt {α : Type} (e : StraightSse.Env α) : Loc → Option α
  | .x r => e.reg r
  | .m k => e.slot k

def locOk : Loc → Bool
  | .x _ => true
  | .m k => decide (k < 18)

def envOf {α : Type} (l : List (Loc × α)) : StraightSse.Env α :=
  { reg := fun r => (l.find? (·.1 == .x r)).map (·.2)
    slot := fun k => (l.find? (·.1 == .m k)).map (·.2) }

theorem rel_envOf {α : Type} {R : α → BitVec 128 → Prop} {n : Nat} {ext : Nat → Option α} {l : List (Loc × α)}
    {s : State} (hin : ∀ p ∈ l, R p.2 (locVal s p.1))
    (hext : ∀ k a, k < n → ext k = some a → R a (s.mem.readW (xAddr (s.gpr .eax) k) 128)) :
    Rel R (cfg n) ext (envOf l) s where
  reg r a h := by
    simp only [envOf, Option.map_eq_some_iff] at h
    obtain ⟨⟨l', b⟩, hf, rfl⟩ := h
    have hl : l' = .x r := by simpa using List.find?_some hf
    subst hl
    exact hin _ (List.mem_of_find?_eq_some hf)
  slot k a _ h := by
    simp only [envOf, Option.map_eq_some_iff] at h
    obtain ⟨⟨l', b⟩, hf, rfl⟩ := h
    have hl : l' = .m k := by simpa using List.find?_some hf
    subst hl
    exact hin _ (List.mem_of_find?_eq_some hf)
  ext := hext

/-- What a layer keeps: it changes only XMM registers and slots. -/
structure Keep (s s' : State) : Prop where
  only : s' = { s with xmm := s'.xmm, mem := s'.mem }
  frame : Frame [⟨(s.gpr .edi).setWidth 64, 288⟩] s.mem s'.mem

theorem Keep.gpr {s s' : State} (h : Keep s s') : s'.gpr = s.gpr := by rw [h.only]
theorem Keep.rd {s s' : State} (h : Keep s s') : s'.rd = s.rd := by rw [h.only]
theorem Keep.wr {s s' : State} (h : Keep s s') : s'.wr = s.wr := by rw [h.only]
theorem Keep.zf {s s' : State} (h : Keep s s') : s'.zf = s.zf := by rw [h.only]

theorem post_at {α : Type} {R : α → BitVec 128 → Prop} {n : Nat} {ext : Nat → Option α} {e : StraightSse.Env α} {s s' : State}
    {is : List Instr} (p : Post R (cfg n) ext e s s' is) {l : Loc} (hl : locOk l = true) {a : α}
    (h : locAt e l = some a) : R a (locVal s' l) := by
  cases l with
  | x r => exact p.rel.reg r a h
  | m k => exact p.rel.slot k a (of_decide_eq_true hl) h

/-! ## Linear layers -/

/-- The slices at `li`, and masks. -/
def linIns (li : Nat → Loc) (ms : List (XReg × BitVec 128)) : List (Loc × (Nat × Nat)) :=
  ((List.range 8).map fun j => (li j, inWordW 128 j)) ++ ms.map fun m => (.x m.1, (m.2.toNat, 0))

/-- Word `j` at `eax`. -/
def linExt (j : Nat) : Option (Nat × Nat) := some (inWordW 128 (8 + j))

/-- Pairs as the numbers of atoms. -/
def atoms (T : Nat → Nat → List (Nat × Nat)) (j p : Nat) : List Nat := (T j p).map fun t => 128 * t.1 + t.2

def linPost (lo : Nat → Loc) (T : Nat → Nat → List (Nat × Nat)) (e : StraightSse.Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => locOk (lo j) && outOkW 128 11 (locAt e (lo j)) (atoms T j)

def linCheck (n : Nat) (is : List Instr) (li : Nat → Loc) (ms : List (XReg × BitVec 128)) (lo : Nat → Loc)
    (T : Nat → Nat → List (Nat × Nat)) : Bool :=
  sseOnly is && check (ofDom (lanes 128 11)) (cfg n) linExt is (envOf (linIns li ms)) (linPost lo T)

/-- The words a layer reads: the slices, and those at `eax`. -/
def words (li : Nat → Loc) (s : State) (j : Nat) : BitVec 128 :=
  if j < 8 then locVal s (li j) else s.mem.readW (xAddr (s.gpr .eax) (j - 8)) 128

/-- A linear layer that the evaluator accepts. -/
theorem lin_ok {n : Nat} {is : List Instr} {li lo : Nat → Loc} {ms : List (XReg × BitVec 128)}
    {T : Nat → Nat → List (Nat × Nat)} (hchk : linCheck n is li ms lo T = true) (hn : n ≤ 8)
    (hT : ∀ j < 8, ∀ p < 128, ∀ t ∈ T j p, t.2 < 128) {s : State} (hok : Ok n s)
    (hm : ∀ m ∈ ms, s.xmm m.1 = m.2) :
    ∃ s', runBlock isa is s = some s' ∧ Keep s s' ∧
      ∀ j < 8, ∀ p < 128, (locVal s' (lo j)).getLsbD p = termsXor (words li s) (T j p) := by
  rw [linCheck, Bool.and_eq_true] at hchk
  obtain ⟨hsse, hchk⟩ := hchk
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel 11 (assign (words li s) (2 ^ 11))) (cfg n) linExt (envOf (linIns li ms)) s := by
    refine rel_envOf (fun p hp => ?_) fun k a hk h => ?_
    · simp only [linIns, List.mem_append, List.mem_map, List.mem_range] at hp
      rcases hp with ⟨j, hj, rfl⟩ | ⟨m, hmm, rfl⟩
      · have := inWordW_rel (k := 11) (words li s) (i := j) (by omega)
        rwa [words, ite_eq_left hj] at this
      · show LaneRel _ _ _ (s.xmm m.1)
        rw [hm m hmm]
        exact lanes_sound.const rfl
    · simp only [linExt, Option.some.injEq] at h
      subst h
      have := inWordW_rel (k := 11) (words li s) (i := 8 + k) (by omega)
      rwa [words, ite_eq_right (by omega), Nat.add_sub_cancel_left] at this
  obtain ⟨s', hs', p⟩ := run' (ofDom_sound _ lanes_sound) hsse hok hrel he
  refine ⟨s', hs', ⟨p.only, p.frame⟩, fun j hj q hq => ?_⟩
  have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := outOkW_spec h.2
  have := outWordW_rel_of_lt h2 (post_at p h.1 h1) q hq
  rw [this]
  exact xorBits_map (words li s) (T j q) (hT j hj q hq)

/-! ## S-boxes -/

def subIns : List (Loc × Nat) := (List.range 8).map fun j => (mid j, sbIn j)
def subPost (lo : Nat → Loc) (T : List Nat) (e : StraightSse.Env Nat) : Bool :=
  (List.range 8).all fun j => locOk (lo j) && locAt e (lo j) == some (T.getD j 0)

def subCheck (is : List Instr) (lo : Nat → Loc) (T : List Nat) : Bool :=
  sseOnly is && check (ofDom (table 128 256)) (cfg 0) (fun _ => none) is (envOf subIns) (subPost lo T)

/-- An S-box that the evaluator accepts, `g` its table's function. -/
theorem sub_ok {is : List Instr} {lo : Nat → Loc} {T : List Nat} {g : Byte → Byte}
    (hchk : subCheck is lo T = true)
    (hT : ∀ c j, c < 256 → j < 8 → (T.getD j 0).testBit c = (g (BitVec.ofNat 8 c)).getLsbD j)
    {s : State} (hok : Ok 0 s) :
    ∃ s', runBlock isa is s = some s' ∧ Keep s s' ∧
      ∀ j < 8, ∀ p < 128, (locVal s' (lo j)).getLsbD p =
        (g (bsByte (fun j => locVal s (mid j)) p)).getLsbD j := by
  rw [subCheck, Bool.and_eq_true] at hchk
  obtain ⟨hsse, hchk⟩ := hchk
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have key : ∀ p < 128, ∃ s', runBlock isa is s = some s' ∧
      Post (TableRel p (bsByte (fun j => locVal s (mid j)) p).toNat) (cfg 0) (fun _ => none) e' s s' is := by
    intro p hp
    refine run' (ofDom_sound _ (table_sound hp (bsByte _ p).isLt)) hsse hok
      (rel_envOf (fun q hq => ?_) fun k a hk => absurd hk (Nat.not_lt_zero k)) he
    simp only [subIns, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only [TableRel, sbIn, testBit_tableOf, (bsByte _ p).isLt, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hj]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', ⟨p₀.only, p₀.frame⟩, fun j hj q hq => ?_⟩
  obtain ⟨s'', hs'', p⟩ := key q hq
  obtain rfl : s'' = s' := Option.some.inj (hs''.symm.trans hs')
  have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have h2 := post_at p h.1 h.2
  simp only [TableRel] at h2
  rw [← h2, hT _ j (bsByte _ q).isLt hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem sbox_check : subCheck subBytes subOut sbox0T = true := by decide +kernel
theorem invSbox_check : subCheck invSubBytes invSubOut invSbox0T = true := by decide +kernel

/-! ## The layers' bits -/

/-- `mulTerms`, as the kernel need not compute it. -/
def mulT (c j : Nat) : List Nat :=
  ((match c with
  | 0x01 => [[0], [1], [2], [3], [4], [5], [6], [7]]
  | 0x02 => [[7], [0, 7], [1], [2, 7], [3, 7], [4], [5], [6]]
  | 0x03 => [[0, 7], [0, 1, 7], [1, 2], [2, 3, 7], [3, 4, 7], [4, 5], [5, 6], [6, 7]]
  | 0x09 => [[0, 5], [1, 5, 6], [2, 6, 7], [0, 3, 5, 7], [1, 4, 5, 6], [2, 5, 6, 7], [3, 6, 7], [4, 7]]
  | 0x0b => [[0, 5, 7], [0, 1, 5, 6, 7], [1, 2, 6, 7], [0, 2, 3, 5], [1, 3, 4, 5, 6, 7], [2, 4, 5, 6, 7],
      [3, 5, 6, 7], [4, 6, 7]]
  | 0x0d => [[0, 5, 6], [1, 5, 7], [0, 2, 6], [0, 1, 3, 5, 6, 7], [1, 2, 4, 5, 7], [2, 3, 5, 6], [3, 4, 6, 7],
      [4, 5, 7]]
  | _ => [[5, 6, 7], [0, 5], [0, 1, 6], [0, 1, 2, 5, 6], [1, 2, 3, 5], [2, 3, 4, 6], [3, 4, 5, 7],
      [4, 5, 6]] : List (List Nat))).getD j []

theorem mulT_eq : ∀ c ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09], ∀ j < 8, mulTerms c j = mulT c j := by
  decide +kernel

/-- `mixT`, with `mulT`. -/
def mixL (cs : List Nat) (f : Bool) (j p : Nat) : List (Nat × Nat) :=
  (List.range 4).flatMap fun i =>
    (mulT (cs.getD i 0) j).map fun b => (b, posAt 8 f (down (byteAt 8 f p) i) (p % 8))

theorem mixL_eq (cs : List Nat) (hc : ∀ i < 4, cs.getD i 0 ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09]) (f : Bool)
    {j : Nat} (hj : j < 8) (p : Nat) : mixL cs f j p = mixT cs 8 f j p := by
  simp only [mixL, mixT, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil,
    mulT_eq _ (hc 0 (by decide)) j hj, mulT_eq _ (hc 1 (by decide)) j hj, mulT_eq _ (hc 2 (by decide)) j hj,
    mulT_eq _ (hc 3 (by decide)) j hj]

/-- MixColumns in form 1, and the round key. -/
def linAT (j p : Nat) : List (Nat × Nat) := mixL mcCoeffs true j p ++ [(8 + j, p)]
/-- ShiftRows twice, MixColumns in form 0, and the round key. -/
def linBT (j p : Nat) : List (Nat × Nat) :=
  ((mixL mcCoeffs false j p).map fun t => (t.1, sr2Src 8 t.2)) ++ [(8 + j, p)]
/-- The bits of the slices and the round key. -/
def withKey (l : List (Nat × Nat)) : List (Nat × Nat) := l.flatMap fun t => [t, (8 + t.1, t.2)]
/-- The round key, and InvMixColumns in form 1. -/
def invAT (j p : Nat) : List (Nat × Nat) := withKey (mixL invMcCoeffs true j p)
/-- The round key, InvMixColumns in form 0, and ShiftRows twice. -/
def invBT (j p : Nat) : List (Nat × Nat) := withKey (mixL invMcCoeffs false j (sr2Src 8 p))

theorem sr2Src_lt {p : Nat} (hp : p < 128) : sr2Src 8 p < 128 := by
  unfold sr2Src
  omega

theorem mixL_lt (cs : List Nat) (f : Bool) {j p : Nat} (hp : p < 128) : ∀ t ∈ mixL cs f j p, t.2 < 128 := by
  intro t ht
  simp only [mixL, List.mem_flatMap, List.mem_map, List.mem_range] at ht
  obtain ⟨i, _, b, _, rfl⟩ := ht
  have hb : byteAt 8 f p < 16 := by unfold byteAt; split <;> omega
  exact posAt_lt f (down_lt hb) (Nat.mod_lt _ (by decide))

theorem linAT_lt (j : Nat) {p : Nat} (hp : p < 128) : ∀ t ∈ linAT j p, t.2 < 128 := by
  intro t ht
  simp only [linAT, List.mem_append, List.mem_singleton] at ht
  rcases ht with h | rfl
  · exact mixL_lt _ _ hp t h
  · exact hp

theorem linBT_lt (j : Nat) {p : Nat} (hp : p < 128) : ∀ t ∈ linBT j p, t.2 < 128 := by
  intro t ht
  simp only [linBT, List.mem_append, List.mem_singleton, List.mem_map] at ht
  rcases ht with ⟨u, h, rfl⟩ | rfl
  · exact sr2Src_lt (mixL_lt _ _ hp u h)
  · exact hp

theorem withKey_lt {l : List (Nat × Nat)} (h : ∀ t ∈ l, t.2 < 128) : ∀ t ∈ withKey l, t.2 < 128 := by
  intro t ht
  simp only [withKey, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ht
  obtain ⟨u, hu, rfl | rfl⟩ := ht
  · exact h _ hu
  · exact h u hu

theorem invAT_lt (j : Nat) {p : Nat} (hp : p < 128) : ∀ t ∈ invAT j p, t.2 < 128 := withKey_lt (mixL_lt _ _ hp)
theorem invBT_lt (j : Nat) {p : Nat} (hp : p < 128) : ∀ t ∈ invBT j p, t.2 < 128 :=
  withKey_lt (mixL_lt _ _ (sr2Src_lt hp))

theorem linA_check : linCheck 8 linA subOut [] mid linAT = true := by decide +kernel
theorem linB_check : linCheck 8 linB subOut [] mid linBT = true := by decide +kernel
theorem invLinA_check : linCheck 8 invLinA invSubOut [] mid invAT = true := by decide +kernel
theorem invLinB_check : linCheck 8 invLinB invSubOut [] mid invBT = true := by decide +kernel

/-! ## Between bytes and slices -/

/-- The masks of the exchanges of bytes, bits and pairs of bits. -/
def bytesM : BitVec 128 := 0x00FF00FF00FF00FF00FF00FF00FF00FF
def bitsM : BitVec 128 := 0x55555555555555555555555555555555
def pairsM : BitVec 128 := 0x33333333333333333333333333333333
def nibblesM : BitVec 128 := 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F

def groupMs : List (XReg × BitVec 128) := [(.xmm5, bytesM), (.xmm6, bitsM), (.xmm7, pairsM)]
def pairMs : List (XReg × BitVec 128) := [(.xmm6, nibblesM)]

/-- The state between `toGroups` and `toPairs` has the third bit of the
numbers of blocks and slices not exchanged yet. -/
def toGroupT (w p : Nat) : List (Nat × Nat) :=
  [(p % 4 + 4 * (w / 4), 8 * byteAt 8 false p + (w % 4 + 4 * (p / 4 % 2))), (8, 8 * byteAt 8 false p + (w % 4 + 4 * (p / 4 % 2)))]
def toPairT (j p : Nat) : List (Nat × Nat) := [(j % 4 + 4 * (p / 4 % 2), p - 4 * (p / 4 % 2) + 4 * (j / 4))]
def toPairT' (inv : Bool) (j p : Nat) : List (Nat × Nat) := toPairT j (if inv then sr2Src 8 p else p)
def fromPairT' (enc : Bool) (w p : Nat) : List (Nat × Nat) :=
  [(w % 4 + 4 * (p / 4 % 2), (if enc then sr2Src 8 else id) (p - 4 * (p / 4 % 2) + 4 * (w / 4)))]
def fromGroupT (b t : Nat) : List (Nat × Nat) :=
  [(t % 4 + 4 * (b / 4), b % 4 + 4 * (t / 4 % 2) + 8 * (t / 8 / 4 + 4 * (t / 8 % 4))), (8, t)]

theorem toGroups_check : linCheck 1 toGroups .m groupMs .m toGroupT = true := by decide +kernel
theorem toPairs_check : ∀ inv, linCheck 0 (toPairs inv) .m pairMs mid (toPairT' inv) = true := by decide +kernel
theorem toSlots_check : linCheck 0 (toSlots subOut) subOut [] .m (fun j p => [(j, p)]) = true := by decide +kernel
theorem invToSlots_check : linCheck 0 (toSlots invSubOut) invSubOut [] .m (fun j p => [(j, p)]) = true := by
  decide +kernel
theorem fromPairs_check : ∀ enc, linCheck 0 (fromPairs enc) .m pairMs .m (fromPairT' enc) = true := by decide +kernel
theorem fromGroups_check : linCheck 1 fromGroups .m groupMs .m fromGroupT = true := by decide +kernel

/-! ## The round keys -/

/-- The constants of the key setup, as words. -/
def keyWords : List (BitVec 128) :=
  [nibblesM, pairsM, bitsM, 0x00000000FF00FF0000000000FF00FF00, 0xFFFFFFFF00000000FFFFFFFF00000000,
   0x63636363636363636363636363636363]

def keyExt (j : Nat) : Option (Nat × Nat) := (keyWords[j]?).map fun v => (v.toNat, 0)

/-- Slice `j` of a round key in form `f`: a bit of a byte of it, eight times. -/
def keyT (f : Bool) (j p : Nat) : List Nat := [8 * byteAt 8 f p + j]

def keyPost (f : Bool) (e : StraightSse.Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => outOkW 128 7 (e.slot j) (keyT f j)

/-- The round key, whose word is `W ⊕ {63…}` with `W` atoms, to slices. -/
def keyCheck (f : Bool) : Bool :=
  sseOnly (keyBytes f ++ keySlices) &&
    check (ofDom (lanes 128 7)) (cfgAt .edx 8 .edi 6) keyExt (keyBytes f ++ keySlices)
      { reg := fun r => if r = .xmm0 then some (inX 0 0x63636363636363636363636363636363) else none
        slot := fun _ => none } (keyPost f)

theorem key_check : ∀ f, keyCheck f = true := by decide +kernel

end VG.Proof.Aes.X86.Sse
