module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Generate
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The controller from its entry to the blocks after a prime's search

Its frame and public data, its entry and the clearing of the key's buffer,
the prime search's call and run, and the blocks after it.
-/

@[expose] public section

/-! ## The controller's public data, its frame and its loop states

`GenPublic` is everything two constant-time runs share: the arguments, the
primes' octets and the exponent. The controller keeps its working state in a
frame of 20 words at `sp - 160` (`GenPublic.F`); a loop state (`GenLive`) is
at an offset into the tape with the search's progress in the state and the
key's buffer.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

structure GenPublic where
  kp : Addr
  up : Addr
  rp : Addr
  B : Addr
  stp : Addr
  sp : Addr
  L : Nat
  randLen : Nat
  Z : Nat
  eB : List Byte

/-- The frame's base. -/
abbrev GenPublic.F (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 160

/-- The frame's region. -/
abbrev GenPublic.frame (p : GenPublic) : Region := ⟨p.F, 160⟩

/-- The frame's words while the search goes on (but the status, and the
region to zero). -/
def GenPublic.headers (p : GenPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, p.kp), (1, BitVec.ofNat 64 p.L), (2, p.up), (3, p.rp), (4, BitVec.ofNat 64 p.randLen), (5, p.B),
    (6, BitVec.ofNat 64 (p.Z / 8)), (7, p.stp), (8, BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (limitOf p.L p.eB))]

theorem GenPublic.headers_bound (p : GenPublic) (used : Nat) : ∀ e ∈ p.headers used, e.1 < 20 := by
  simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

def genOfState (s : State) : GenPublic where
  kp := s.gpr .rdi
  up := s.gpr .rdx
  rp := s.gpr .rcx
  B := s.gpr .r9
  stp := stackArg s 1
  sp := s.gpr .rsp
  L := genLen s
  randLen := (s.gpr .r8).toNat
  Z := (stackArg s 0).toNat * 8
  eB := genE s

def GenInput (p : GenPublic) (s : State) : Prop := genPre s ∧ genOfState s = p

/-- The phase's word in the state. -/
def phaseWord : KeyPhase → Nat
  | .p => 0
  | .q _ => 1

/-- The key's buffer's slot `j` (`p_len` octets each). -/
abbrev GenPublic.slot (p : GenPublic) (j : Nat) : Addr := p.kp + BitVec.ofNat 64 (j * p.L)

/-- The state's words for the progress `st`, and the exponent. -/
structure StateOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  remaining : word m p.stp 0 = BitVec.ofNat 64 st.remaining
  len : word m p.stp 8 = BitVec.ofNat 64 p.L
  cap : word m p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L)
  phase : word m p.stp 32 = BitVec.ofNat 64 (phaseWord st.phase)
  left : word m p.stp 40 = BitVec.ofNat 64 st.left
  e : Spec.Rsa.bytesAt m (p.stp + 48) 8 = p.eB
  remaining_le : st.remaining ≤ limitOf p.L p.eB
  left_lt : st.left < 2 ^ 64

/-- The key's buffer for the progress `st`: zeros but `p`'s slot, which holds
`p` for `q`'s search. -/
structure KeyOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  low : Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0
  high : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0
  other : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB

/-- A state of the controller in its frame: `used` octets consumed, the
progress `st` in the state. The entry state is functional-proof data only: its
callee-saved registers may hold secrets, and its tape and key buffer are
secret. -/
structure GenFrame (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop where
  input : GenInput p original
  used_le : used ≤ p.randLen
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  rsp : s.gpr .rsp = p.F
  r12 : s.gpr .r12 = p.F
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .rsp → s.gpr r = original.gpr r
  savedR12 : word s.mem p.F 72 = original.gpr .r12
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = genRand original
  headers : Slots s.mem p.F (p.headers used)
  state : StateOk p st s.mem

/-- A state of the loop: the frame's, and the key's buffer for the progress. -/
structure GenLive (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop
    extends GenFrame p original used st s where
  key : KeyOk p st s.mem

/-- The key search from octet `used` of the tape, from the progress `st`. -/
abbrev tailOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : KeySearchResult :=
  keySearch p.L p.eB st ((genRand original).drop used)

/-- A loop state, whose key search from there finishes as `final`. -/
def GenIter (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (s : State) : Prop :=
  GenLive p original used st s ∧ ∃ tr, final = (tailOf p original used st).consume used tr

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The controller's entry: its frame's words from the arguments and the state -/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-! ## Whether the exponent is 3 -/

/-- The exponent's eight octets, most significant first, read as a word, are
`3 · 2^56` exactly when the exponent is 3. -/
theorem word_eq_three (m : Mem) (a : Addr) :
    m.readW a 64 = 0x0300000000000000 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a 8) = 3 := by
  have hb : ∀ j < 8, (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
    intro j hj
    rw [← Mem.extractLsb'_read m a (n := 8) hj]
    rfl
  have hc : ∀ j < 8, (0x0300000000000000 : BitVec 64).extractLsb' (8 * j) 8 = if j = 7 then 3 else 0 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      h | h | h | h | h | h | h | h <;> subst h <;> decide
  rw [show Spec.Rsa.bytesAt m a 8 = Spec.Rsa.bytesAt m a 7 ++ [m (a + BitVec.ofNat 64 7)] from
    SearchInit.bytesAt_succ m a 7, SearchInit.os2ip_eq_three, SearchInit.or_eq_zero,
    SearchInit.orOf_eq_zero]
  have hx : (m (a + BitVec.ofNat 64 7)).setWidth 64 ^^^ 3 = 0 ↔ m (a + BitVec.ofNat 64 7) = 3 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
      rw [BitVec.toNat_setWidth, show (3 : BitVec 64).toNat = 3 from rfl] at this
      apply BitVec.eq_of_toNat_eq
      have hl := (m (a + BitVec.ofNat 64 7)).isLt
      rw [show (3 : BitVec 8).toNat = 3 from rfl]
      omega
    · intro h; rw [h]; decide
  rw [hx]
  constructor
  · intro h
    refine ⟨fun b hm => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      have hj := List.mem_range.mp hj
      have := (hb j (by omega)).symm.trans ((congrArg (fun x : BitVec 64 => x.extractLsb' (8 * j) 8) h).trans
        (hc j (by omega)))
      rw [ite_eq_right (by omega)] at this
      exact this
    · have := (hb 7 (by decide)).symm.trans ((congrArg (fun x : BitVec 64 => x.extractLsb' (8 * 7) 8) h).trans
        (hc 7 (by decide)))
      exact this
  · rintro ⟨h0, h7⟩
    apply Proof.Bignum.X86_64.WordIO.eq_of_bytes
    intro j hj
    rw [hb j hj, hc j hj]
    by_cases h : j = 7
    · subst h; rw [ite_eq_left rfl]; exact h7
    · rw [ite_eq_right h]
      exact h0 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)

/-! ## Where the buffers are -/

namespace GenInput

variable {p : GenPublic} {s : State}

theorem nowrap (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.1 r hr

theorem write_disjoint (h : GenInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧ (below (s.gpr .rsp) stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : GenInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.1

theorem sp_eq (h : GenInput p s) : p.sp = s.gpr .rsp := by rw [← h.2]; rfl

theorem room (h : GenInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem top (h : GenInput p s) : p.sp.toNat + 24 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.1.1

theorem F_toNat (h : GenInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 552 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [GenPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : GenInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  refine Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) ?_
  have := h.F_toNat
  have : 552 ≤ p.sp.toNat := h.room
  have := h.top
  omega

/-- The regions the controller (and its callees) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below (s.gpr .rsp) stackUse]

theorem read_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).2.symm

theorem bytes_frame (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega) (List.mem_range.mp hi)

theorem random_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

/-- The frame is in the stack the controller may use. -/
theorem frame_sub (h : GenInput p s) : Region.Sub p.frame (below (s.gpr .rsp) stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

theorem frame_disjoint_writes (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s) : p.frame.Disjoint r :=
  fun x hx hy => (h.stack_disjoint (List.mem_append_left _ hr)).2 x (h.frame_sub x hx) hy

end GenInput

/-! ## The entry's stores -/

def regValues (s : State) : List (Nat × BitVec 64) :=
  [(9, s.gpr .r12), (0, s.gpr .rdi), (2, s.gpr .rdx), (3, s.gpr .rcx), (4, s.gpr .r8), (5, s.gpr .r9)]

def argValues (s : State) : List (Nat × BitVec 64) := [(6, stackArg s 0), (7, stackArg s 1)]

def headValues (s : State) : List (Nat × BitVec 64) := regValues s ++ argValues s

/-- The counted candidates of a prime's search, from the primes' octets `w`
and the exponent's word `ew`. -/
def limitBV (w ew : BitVec 64) : BitVec 64 :=
  if ew = 0x0300000000000000 then w <<< 6 else (w <<< 3) <<< 2 + w <<< 3

def wordValues (s : State) : List (Nat × BitVec 64) :=
  [(1, s.mem.readW (stackArg s 1 + 8) 64), (8, 0),
    (11, limitBV (s.mem.readW (stackArg s 1 + 8) 64) (s.mem.readW (stackArg s 1 + 48) 64))]

def entryValues (s : State) : List (Nat × BitVec 64) := headValues s ++ wordValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, headValues, regValues, argValues, wordValues, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem arg_contains (s : State) {j : Nat} (hj : j < 2) :
    (inArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem input_args {p : GenPublic} {s : State} (h : GenInput p s) :
    ∀ j < 2, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inArgs s, ?_, arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (by simp [inReads])

/-- The frame's stores keep what is outside it. -/
theorem entry_frame {p : GenPublic} {s : State} (h : GenInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {r : Region} (hr : r ∈ inWrites s ++ inReads s) {a : Addr} {n : Nat}
    (ha : r.Contains a (n / 8)) (hn : n / 8 < 2 ^ 64) :
    (writeFrame s.mem p.F values).readW a n = s.mem.readW a n := by
  refine (writeFrame_frame s.mem p.F values hb).readW ha (fun q hq => ?_) hn
  obtain rfl := List.mem_singleton.mp hq
  exact fun x hx hy => (h.stack_disjoint hr).2 x (h.frame_sub x hy) hx

theorem alloc_rsp {p : GenPublic} {s : State} (h : GenInput p s) :
    (allocated 160 s).gpr .rsp = p.F := by
  rw [allocated_rsp, ← h.sp_eq]

theorem alloc_wr {p : GenPublic} {s : State} (h : GenInput p s) :
    (allocated 160 s).wr = p.frame :: s.wr := by
  show (⟨s.gpr .rsp - BitVec.ofNat 64 160, 160⟩ : Region) :: s.wr = _
  rw [← h.sp_eq]

theorem arg_addr {p : GenPublic} {s : State} (h : GenInput p s) (k : Nat) :
    p.F + BitVec.ofNat 64 (168 + 8 * k) = stackArgAddr s k := by
  rw [show 168 + 8 * k = 160 + 8 * (k + 1) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel, h.sp_eq]
  rfl

theorem arg_read {p : GenPublic} {s : State} (h : GenInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {k : Nat} (hk : k < 2) :
    (writeFrame s.mem p.F values).readW (p.F + BitVec.ofNat 64 (168 + 8 * k)) 64 = stackArg s k := by
  rw [arg_addr h]
  exact entry_frame h values hb (r := inArgs s) (by simp [inReads]) (arg_contains s hk) (by decide)

theorem arg_in {p : GenPublic} {s : State} (h : GenInput p s) {t : State} (hr : t.rd = s.rd)
    (hw : t.wr = p.frame :: s.wr) {k : Nat} (hk : k < 2) :
    InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 (168 + 8 * k)) 8 := by
  rw [arg_addr h, hr, hw]
  obtain ⟨r, hr', hc⟩ := input_args h k hk
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr' with hm | hm
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)

theorem entryHead_split : entryHead =
    ([.store { base := .rsp, disp := 72 } .r12, .mov .r12 (.reg .rsp),
      .store (field 0) .rdi, .store (field 2) .rdx, .store (field 3) .rcx, .store (field 4) .r8,
      .store (field 5) .r9] : List Instr) ++
    ([.mov .rax (.mem (callerArg 0)), .store (field 6) .rax,
      .mov .rax (.mem (callerArg 1)), .store (field 7) .rax] : List Instr) := rfl

theorem entry_regs_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block [.store { base := .rsp, disp := 72 } .r12, .mov .r12 (.reg .rsp),
      .store (field 0) .rdi, .store (field 2) .rdx, .store (field 3) .rcx, .store (field 4) .r8,
      .store (field 5) .r9]) (allocated 160 s) fun t =>
      (t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (regValues s)) ∧ Keep [.r12] (allocated 160 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 160 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 160 s).wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hsp := alloc_rsp h
  refine WP.keep [.r12] ?_ rfl
  unfold writeFrame regValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero, hsp,
    allocated_reg _ _ _ (show Reg.r12 ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.rdx ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.rcx ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.r8 ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.r9 ≠ .rsp by decide),
    allocated_mem, hs0, hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide),
    hs 72 (by decide)]

theorem entry_args_ok {p : GenPublic} {s t : State} (h : GenInput p s)
    (hm : t.mem = writeFrame s.mem p.F (regValues s)) (k : Keep [.r12] (allocated 160 s) t)
    (hr : t.gpr .r12 = p.F) :
    WP isa (.block [.mov .rax (.mem (callerArg 0)), .store (field 6) .rax,
      .mov .rax (.mem (callerArg 1)), .store (field 7) .rax]) t fun u =>
      (u.gpr .rax = stackArg s 1 ∧ u.mem = writeFrame t.mem p.F (argValues s)) ∧ Keep [.rax] t u := by
  have hb : ∀ e ∈ regValues s, e.1 < 20 := fun e he =>
    entryValues_bound s e (List.mem_append_left _ (List.mem_append_left _ he))
  have htr : t.rd = s.rd := k.2.1
  have htw : t.wr = p.frame :: s.wr := k.2.2.trans (alloc_wr h)
  have hsp : t.gpr .rsp = p.F := (k.gpr (by decide)).trans (alloc_rsp h)
  have scr := h.frame_scr htw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions t.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hv0 : t.mem.readW (p.F + BitVec.ofNat 64 168) 64 = stackArg s 0 := by
    rw [hm]; exact arg_read h _ hb (k := 0) (by decide)
  have hv1 : t.mem.readW (p.F + BitVec.ofNat 64 176) 64 = stackArg s 1 := by
    rw [hm]; exact arg_read h _ hb (k := 1) (by decide)
  have ha0 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 168) 8 := arg_in h htr htw (k := 0) (by decide)
  have ha1 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 176) 8 := arg_in h htr htw (k := 1) (by decide)
  refine WP.keep [.rax] ?_ rfl
  unfold writeFrame argValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, callerArg, frameBytes, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, Nat.reduceAdd, hsp, hr, read_above_store, hv0, hv1, ha0, ha1,
    hs 48 (by decide), hs 56 (by decide)]

theorem entry_head_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block entryHead) (allocated 160 s) fun t =>
      t.gpr .r12 = p.F ∧ t.gpr .rax = stackArg s 1 ∧ t.mem = writeFrame s.mem p.F (headValues s) ∧
      Keep [.r12, .rax] (allocated 160 s) t := by
  rw [entryHead_split, WP.block_append_iff]
  refine WP.mono (entry_regs_ok h) fun t ⟨⟨hr, hm⟩, k⟩ => ?_
  refine WP.mono (entry_args_ok h hm k hr) fun u ⟨⟨ha, hu⟩, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr, ha, by rw [hu, hm, headValues, writeFrame_append],
    (k.trans ku).mono (by decide)⟩

theorem bv_sub_beq (x y : BitVec 64) : (x - y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg (· + y) h
    simp only [BitVec.sub_add_cancel] at this
    rw [this]; exact BitVec.zero_add _
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem limitBV_eq {L : Nat} {ew : BitVec 64} {eB : List Byte} (hL : L ≤ 512)
    (he : ew = 0x0300000000000000 ↔ Spec.Rsa.os2ip eB = 3) :
    limitBV (BitVec.ofNat 64 L) ew = BitVec.ofNat 64 (limitOf L eB) := by
  unfold limitBV limitOf primeLimit
  rw [SearchInit.shl_ofNat _ 6 (by omega), SearchInit.shl_ofNat _ 3 (by omega),
    SearchInit.shl_ofNat _ 2 (by omega), SearchInit.add_ofNat]
  by_cases h : ew = 0x0300000000000000
  · rw [ite_eq_left h, ite_eq_left (he.mp h)]; congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (he.mpr h'))]; congr 1; omega

theorem entry_words_ok {p : GenPublic} {s u : State} (h : GenInput p s)
    (hm : u.mem = writeFrame s.mem p.F (headValues s))
    (hra : u.gpr .rax = stackArg s 1) (hr : u.gpr .r12 = p.F)
    (huw : u.wr = p.frame :: s.wr) :
    WP isa (.block entryWords) u fun t =>
      t.mem = writeFrame u.mem p.F (wordValues s) ∧ Keep [.rcx, .rdx, .r8, .r9, .r11] u t := by
  have hb : ∀ e ∈ headValues s, e.1 < 20 := fun e he =>
    entryValues_bound s e (List.mem_append_left _ he)
  have scr := h.frame_scr huw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions u.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hst (d : Nat) (hd : d + 8 ≤ 56) : (inState s).Contains (stackArg s 1 + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ hd (by omega)
  have hv (d : Nat) (hd : d + 8 ≤ 56) :
      u.mem.readW (stackArg s 1 + BitVec.ofNat 64 d) 64 = s.mem.readW (stackArg s 1 + BitVec.ofNat 64 d) 64 := by
    rw [hm]
    exact entry_frame h _ hb (r := inState s) (by simp [inWrites]) (hst d hd) (by decide)
  have ha (d : Nat) (hd : d + 8 ≤ 56) : InRegions (u.rd ++ u.wr) (stackArg s 1 + BitVec.ofNat 64 d) 8 := by
    refine ⟨inState s, ?_, hst d hd⟩
    rw [huw, h.1.2.2.2.1]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
  have hv8 := hv 8 (by decide)
  have hv48 := hv 48 (by decide)
  have ha8 := ha 8 (by decide)
  have ha48 := ha 48 (by decide)
  refine WP.keep [.rcx, .rdx, .r8, .r9, .r11] ?_ rfl
  unfold entryWords writeFrame wordValues limitBV
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases he : s.mem.readW (stackArg s 1 + BitVec.ofNat 64 48) 64 = 0x0300000000000000 <;>
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    hra, hr, hv8, hv48, ha8, ha48, eval, execCmov, bv_sub_beq, he,
    hs 8 (by decide), hs 64 (by decide), hs 88 (by decide)] <;>
  split <;> rename_i hc <;> first | rfl | exact absurd hc he | exact absurd he hc

theorem entry_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block (entryHead ++ entryWords)) (allocated 160 s) fun t =>
      t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s) ∧
      Keep [.r12, .rax, .rcx, .rdx, .r8, .r9, .r11] (allocated 160 s) t := by
  rw [WP.block_append_iff]
  refine WP.mono (entry_head_ok h) fun u ⟨hr, ha, hm, k⟩ => ?_
  have huw : u.wr = p.frame :: s.wr := k.2.2.trans (alloc_wr h)
  refine WP.mono (entry_words_ok h hm ha hr huw) fun t ⟨ht, kt⟩ =>
    ⟨(kt.gpr (by decide)).trans hr, ?_, (k.trans kt).mono (by decide)⟩
  rw [ht, hm, entryValues, writeFrame_append]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

namespace GenInput

variable {p : GenPublic} {s : State}

theorem state_words (h : GenInput p s) {m : Mem} (hf : Frame [p.frame] s.mem m) (d : Nat) (hd : d + 8 ≤ 56) :
    m.readW (p.stp + BitVec.ofNat 64 d) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 d) 64 := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  refine hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd (by omega)) (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  rw [← hst]
  exact (h.frame_disjoint_writes (by simp [inWrites])).symm

theorem state_bytes (h : GenInput p s) {m : Mem} (hf : Frame [p.frame] s.mem m) :
    Spec.Rsa.bytesAt m (p.stp + 48) 8 = Spec.Rsa.bytesAt s.mem (p.stp + 48) 8 := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  rw [hst] at hn
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
  obtain rfl := List.mem_singleton.mp hq
  have hd := h.frame_disjoint_writes (r := inState s) (by simp [inWrites])
  rw [hst] at hd
  exact (hd.symm.sub_left (Offset.sub_base _ (by omega) (n := 8) (d := 48) (k := 56))) |>.symm.symm

end GenInput

/-- The state's words for the progress on entry. -/
theorem stateOk_entry {p : GenPublic} {s : State} (h : GenInput p s) {m : Mem} (hf : Frame [p.frame] s.mem m) :
    StateOk p (genProgress s) m := by
  have hw (d : Nat) (hd : d + 8 ≤ 56) := h.state_words hf d hd
  have hpre := h.1
  obtain ⟨-, -, -, -, -, -, -, -, hL, -, -, hrem, hcap, hph, -⟩ := hpre
  have hstp : p.stp = stackArg s 1 := by rw [← h.2]; rfl
  have hLp : p.L = genLen s := by rw [← h.2]; rfl
  have heB : p.eB = genE s := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, BitVec.isLt _⟩
  · change m.readW (p.stp + BitVec.ofNat 64 0) 64 = _
    rw [hw 0 (by decide), BitVec.add_zero, hstp]; exact (ofNat_toNat64 _).symm
  · change m.readW (p.stp + BitVec.ofNat 64 8) 64 = _
    rw [hw 8 (by decide), hLp, hstp, ofNat_toNat64]; rfl
  · change m.readW (p.stp + BitVec.ofNat 64 16) 64 = _
    rw [hw 16 (by decide), hLp, hstp]; exact hcap
  · change m.readW (p.stp + BitVec.ofNat 64 32) 64 = _
    rw [hw 32 (by decide), hstp]
    simp only [genProgress, keyProgressAt]
    have hph' : (s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat ≤ 1 := hph
    split
    · rename_i h0
      have h0' : (s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      rw [h0']; rfl
    · rename_i h0
      have h0' : ¬(s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      have : (s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat = 1 := by omega
      rw [this]; rfl
  · change m.readW (p.stp + BitVec.ofNat 64 40) 64 = _
    rw [hw 40 (by decide), hstp]; exact (ofNat_toNat64 _).symm
  · rw [h.state_bytes hf, heB, hstp]
  · rw [hLp, heB]
    exact hrem

/-- The controller's state on leaving its entry, before it clears the key's
buffer. -/
theorem gen_start {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block (entryHead ++ entryWords)) (allocated 160 s) fun t =>
      GenFrame p s 0 (genProgress s) t ∧ Frame [p.frame] s.mem t.mem := by
  refine WP.mono (entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hb := entryValues_bound s
  have hw (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hm]; exact writeFrame_word _ _ _ hb j hj
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame s.mem p.F _ hb
  have hf : Frame (GenInput.changes s) s.mem t.mem := by
    apply hfr.sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [GenInput.changes], h.frame_sub⟩
  have hL : p.L ≤ 512 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.1.2.1
  have hstp : p.stp = stackArg s 1 := by rw [← h.2]; rfl
  refine ⟨⟨h, Nat.zero_le _, k.2.1, k.2.2.trans (alloc_wr h), (k.gpr (by decide)).trans (alloc_rsp h), hr,
    fun r hr hn hs => ?_, ?_, ?_, ?_, stateOk_entry h hfr⟩, hfr⟩
  · rw [k.gpr (by revert r; decide), allocated_reg _ _ _ hs]
  · change word t.mem p.F (8 * 9) = _
    rw [hw 9 (by decide)]
    rfl
  · rw [h.random_frame hf]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (GenPublic.headers_bound _ _ e he)]
    have hLs : genLen s = p.L := by rw [← h.2]; rfl
    have hlim : limitBV (s.mem.readW (stackArg s 1 + 8) 64) (s.mem.readW (stackArg s 1 + 48) 64) =
        BitVec.ofNat 64 (limitOf p.L p.eB) := by
      rw [show s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 p.L by rw [← hLs]; exact (ofNat_toNat64 _).symm]
      exact limitBV_eq hL (by rw [word_eq_three]; rw [← h.2]; rfl)
    rw [← h.2] at he hlim
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [frameValue, entryValues, headValues, regValues, argValues, wordValues, List.cons_append,
        List.nil_append, List.foldl_cons, List.foldl_nil, genOfState, genLen, ofNat_toNat64, hlim,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## What the controller's steps keep

The callees and the controller's own stores change only the key's buffer,
`used`, the working space, the state's first four words and the stack below
the frame (`callChanges`); through such changes a loop state keeps its frame,
its tape and the state's last three words.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

namespace GenInput

variable {p : GenPublic} {s : State}

/-- What a step may write: the key's buffer, `used`, the working space, the
state's first four words, and the stack below the frame. -/
def callChanges (s : State) : List Region :=
  [inKey s, inUsed s, inScr s, ⟨stackArg s 1, 32⟩, ⟨s.gpr .rsp - BitVec.ofNat 64 stackUse, 392⟩]

theorem state32_sub (s : State) : Region.Sub ⟨stackArg s 1, 32⟩ (inState s) := by
  unfold inState
  exact Region.sub_prefix (by decide)

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], state32_sub s⟩
  · exact ⟨below (s.gpr .rsp) stackUse, by simp [changes], Region.sub_prefix (by decide)⟩

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (callChanges s) m m') :
    Frame (changes s) m m' := hf.sub (callChanges_sub s)

/-- The frame is disjoint from what a step writes. -/
theorem frame_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, p.frame.Disjoint r := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact (h.frame_disjoint_writes (r := inState s) (by simp [inWrites])).sub_right (state32_sub s)
  · rw [← h.sp_eq]
    have hs := Offset.sep_below p.sp 552 (a := 160) (n := 160) (b := 552) (k := 392) (by decide) (by decide)
      (Or.inr (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (by simp only [Region.Contains, GenPublic.F] at hx; omega)
      (by simp only [Region.Contains] at hy; exact hy)

theorem frame_words (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 20) : word m' p.F (8 * j) = word m p.F (8 * j) :=
  hf.readW (r := p.frame) (Offset.contains_base _ (by omega) (by omega)) h.frame_disjoint (by decide)

/-- The state's last three words. -/
abbrev stateTail (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 32, 24⟩

theorem tail_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, (stateTail p).Disjoint r := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hstp : stackArg s 1 = p.stp := by rw [← h.2]; rfl
  have hsub : Region.Sub (stateTail p) (inState s) := by rw [hst]; exact Offset.sub_base _ (by decide)
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hpw.1.2.2.symm).sub_left hsub
  · exact (hpw.2.1.2.symm).sub_left hsub
  · exact (hpw.2.2.1.symm).sub_left hsub
  · rw [hstp]
    exact fun x hx hy => by
      simp only [Region.Contains] at hx hy
      have := Offset.sep p.stp (d := 32) (n := 24) (e := 0) (k := 32) (Or.inr (by decide)) (by decide) (by decide)
      rw [BitVec.add_zero] at this
      exact this x (by omega) (by omega)
  · exact fun x hx hy => (h.stack_disjoint (r := inState s) (by simp [inWrites])).2 x
      (Region.sub_prefix (base := s.gpr .rsp - BitVec.ofNat 64 stackUse) (by decide) x hy) (hsub x hx)

theorem tail_word (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m') {d : Nat}
    (hd₁ : 32 ≤ d) (hd₂ : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d := by
  have hc : (stateTail p).Contains (off p.stp d) 8 := by
    rw [show off p.stp d = p.stp + BitVec.ofNat 64 32 + BitVec.ofNat 64 (d - 32) by
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  exact hf.readW hc h.tail_disjoint (by decide)

theorem tail_bytes (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m') :
    Spec.Rsa.bytesAt m' (p.stp + 48) 8 = Spec.Rsa.bytesAt m (p.stp + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hsub : Region.Sub ⟨p.stp + 48, 8⟩ (stateTail p) := by
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 32 + BitVec.ofNat 64 16 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl]
    exact Offset.sub_base _ (by decide)
  exact hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => (h.tail_disjoint r hr).sub_left hsub)
    (by show 8 ≤ 2 ^ 64; decide) hi

end GenInput

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through a step that keeps r12, the stack pointer, the regions and the
callee-saved registers, and writes only what a step may, with the state's
first three words for the progress `st'`, whose phase and generations are
`st`'s. -/
theorem restore (h : GenFrame p original used st s) {st' : KeyProgress}
    (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (hf : Frame (GenInput.callChanges original) s.mem t.mem)
    (h0 : word t.mem p.stp 0 = BitVec.ofNat 64 st'.remaining)
    (h1 : word t.mem p.stp 8 = BitVec.ofNat 64 p.L)
    (h2 : word t.mem p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L))
    (hph : st'.phase = st.phase ∨ phaseWord st'.phase = phaseWord st.phase) (hl : st'.left = st.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) :
    GenFrame p original used st' t := by
  have hc := h.input.frame_words hf
  have hf' := GenInput.frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, (hg .rsp (by decide)).trans h.rsp,
    (hg .r12 (by decide)).trans h.r12, fun r hr hn hs => (hg r hr).trans (h.saved r hr hn hs), ?_, ?_, ?_,
    ⟨h0, h1, h2, ?_, ?_, ?_, hrem, by rw [hl]; exact h.state.left_lt⟩⟩
  · exact (hc 9 (by decide)).trans h.savedR12
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (GenPublic.headers_bound _ _ e he)).trans (h.headers e he)
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.phase]
    rcases hph with hph | hph <;> rw [hph]
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.left, hl]
  · rw [h.input.tail_bytes hf, h.state.e]

end GenFrame

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## Zeros in the key's buffer

`clear` writes zeros to the region in frame words 12 and 13, which is in the
key's buffer: the frame, the state and everything else is kept.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.Rsa.X86_64 (OutOk)

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

theorem key_region (h : GenFrame p original used st s) : inKey original = ⟨p.kp, 9 * p.L⟩ := by
  have := h.input.1.2.2.2.2.2.2.2.2.2.1
  rw [← h.input.2]
  simp only [inKey, genOfState, this]

theorem key_state (h : GenFrame p original used st s) : (inKey original).Disjoint (inState original) := by
  have hpw := h.input.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.1.2.2

/-- Through a step that changes only the key's buffer. -/
theorem restoreKey (h : GenFrame p original used st s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (hf : Frame [inKey original] s.mem t.mem) : GenFrame p original used st t := by
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  have hd := h.key_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d :=
    hf.readW (r := inState original) (by rw [hst]; exact Offset.contains_base _ hd' (by omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine h.restore hr hw hg (hf.sub fun r hr => ?_) ?_ ?_ ?_ (.inl rfl) rfl h.state.remaining_le
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩
  · rw [hword 0 (by decide)]; exact h.state.remaining
  · rw [hword 8 (by decide)]; exact h.state.len
  · rw [hword 16 (by decide)]; exact h.state.cap

theorem outOk (h : GenFrame p original used st s) {op : Addr} {len : Nat}
    (hsub : Region.Sub ⟨op, len⟩ (inKey original)) (hn : op.toNat + len ≤ 2 ^ 64) :
    OutOk s p.F 160 op len := by
  have hin : inKey original ∈ s.wr := by
    rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
  have hd := h.input.frame_disjoint_writes (r := inKey original) (by simp [inWrites])
  refine ⟨fun i hi => ⟨_, hin, hsub _ (contains_byte _ hi (by omega))⟩, fun i hi => Nat.le_of_not_lt fun hlt =>
    hd _ (by simp only [ofs] at hlt; simp only [Region.Contains]; omega)
      (hsub _ (contains_byte _ hi (by omega)))⟩

end GenFrame

/-- `clear`: zeros at the region in frame words 12 and 13. -/
theorem clear_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {op : Addr} {len : Nat}
    (h12 : word s.mem p.F (8 * 12) = op) (h13 : word s.mem p.F (8 * 13) = BitVec.ofNat 64 len)
    (hsub : Region.Sub ⟨op, len⟩ (inKey original)) (hn : op.toNat + len ≤ 2 ^ 64) (h1 : 1 ≤ len)
    (hlt : len < 2 ^ 31) :
    WP isa clear s fun t => GenFrame p original used st t ∧ (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      Frame [⟨op, len⟩] s.mem t.mem ∧ (∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) ∧
      Keep [.rdi, .rsi, .rcx, .rax] s t := by
  unfold clear
  refine WP.seq (WP.mono (WP.keep [.rdi] (Q := fun u => u.gpr .rdi = p.F ∧ u.mem = s.mem) (by xrun [h.r12]) rfl)
    fun u ⟨⟨hdi, hm⟩, ku⟩ => ?_)
  have hu : GenFrame p original used st u :=
    h.restoreKey ku.2.1 ku.2.2 (fun r hr => ku.gpr (by revert r; decide)) (by rw [hm]; exact Frame.refl _ _)
  have scr := h.input.frame_scr (ku.2.2.trans h.wr)
  refine WP.mono (VG.Proof.Ffdh.X86_64.Generation.controller_zero_out (sPtr := 12) (sLen := 13) (op := op)
    (len := len) scr hdi (by decide) (by decide) (by decide) (by rw [hm]; exact h12) (by rw [hm]; exact h13)
    h1 hlt (hu.outOk hsub hn)) fun t ⟨hv, hfr, k⟩ => ?_
  have hframe : Frame [⟨op, len⟩] s.mem t.mem := by
    intro a ha
    rw [hfr a ?_, hm]
    intro i hi he
    apply ha _ (List.mem_singleton_self _)
    rw [he]
    exact contains_byte _ hi (by omega)
  have hkey : Frame [inKey original] u.mem t.mem := by
    intro a ha
    rw [← hm] at hframe
    refine hframe a fun r hr => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact fun hc => ha _ (List.mem_singleton_self _) (hsub _ hc)
  have hfw : ∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    intro j hj
    rw [← hm]
    exact hu.input.frame_words (hkey.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩) j hj
  exact ⟨hu.restoreKey k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide)) hkey, hv, hframe, hfw,
    (ku.trans k).mono (by decide)⟩

/-! ## Stores to the frame -/

namespace GenInput

variable {p : GenPublic} {s : State}

theorem frame_state (h : GenInput p s) : p.frame.Disjoint ⟨p.stp, 56⟩ := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  rw [← hst]; exact h.frame_disjoint_writes (by simp [inWrites])

/-- The state through stores to the frame. -/
theorem stateOk_frame (h : GenInput p s) {m m' : Mem} (hf : Frame [p.frame] m m') {st : KeyProgress}
    (hs : StateOk p st m) : StateOk p st m' := by
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  rw [hst] at hn
  have hd := h.frame_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d :=
    hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd' (by omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs.remaining_le, hs.left_lt⟩
  · rw [hword 0 (by decide)]; exact hs.remaining
  · rw [hword 8 (by decide)]; exact hs.len
  · rw [hword 16 (by decide)]; exact hs.cap
  · rw [hword 32 (by decide)]; exact hs.phase
  · rw [hword 40 (by decide)]; exact hs.left
  · rw [← hs.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    refine hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
    obtain rfl := List.mem_singleton.mp hq
    refine (hd.sub_right ?_).symm
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]
    exact Offset.sub_base _ (by decide)

end GenInput

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through stores to the frame but its saved r12, with the words for the
octets consumed `u`. -/
theorem store (h : GenFrame p original used st s) {u : Nat} (hu : u ≤ p.randLen)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20) (h9 : ∀ e ∈ values, 9 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hh : Slots t.mem p.F (p.headers u)) : GenFrame p original u st t := by
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame s.mem p.F values hb
  have hf : Frame (GenInput.changes original) s.mem t.mem := by
    apply hfr.sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩
  refine ⟨h.input, hu, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hreg hne hs => (hg reg hreg).trans (h.saved reg hreg hne hs), ?_, ?_, hh,
    h.input.stateOk_frame hfr h.state⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 9) = _
    rw [writeFrame_word _ _ _ hb 9 (by decide), frameValue_unchanged _ _ _ h9]
    exact h.savedR12
  · exact (h.input.random_frame hf).trans h.random

/-- The words of the frame's headers but `used`, kept through stores of others. -/
theorem slots_kept (h : GenFrame p original used st s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F values) p.F (p.headers used) := by
  intro e he
  have hj := GenPublic.headers_bound _ _ e he
  rw [writeFrame_word _ _ _ hb e.1 hj, frameValue_unchanged _ _ _ ?_]
  · exact h.headers e he
  · intro x hx heq
    have := hnot x hx
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end GenFrame

/-! ## The key's buffer but `p` -/

theorem bytes_zero {m : Mem} {op : Addr} {len : Nat} (h : ∀ i < len, m (op + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m op len = List.replicate len 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)

theorem bytes_kept {m m' : Mem} {R : Region} {a : Addr} {n : Nat} (hf : Frame [R] m m')
    (hd : R.Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨a, n⟩) (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) hn
    (List.mem_range.mp hi)

theorem slot_disjoint (kp : Addr) {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2 ^ 64)
    (he : e + k ≤ 2 ^ 64) : Region.Disjoint ⟨kp + BitVec.ofNat 64 d, n⟩ ⟨kp + BitVec.ofNat 64 e, k⟩ :=
  fun x hx hy => Offset.sep kp h hd he x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

theorem slot_sub (kp : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Region.Sub ⟨kp + BitVec.ofNat 64 d, n⟩ ⟨kp, k⟩ := Offset.sub_base kp h

theorem kp_zero (kp : Addr) : kp = kp + BitVec.ofNat 64 0 := (BitVec.add_zero kp).symm

/-- A read below a store of the frame sees what was there. -/
theorem read_below_store (m : Mem) (B : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep B (d := d) (n := 8) (e := e) (k := 8) (Or.inl h) (by omega) he)
    (by decide)

theorem read_below_store0 (m : Mem) (B : Addr) (v : BitVec 64) {e : Nat} (h : 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW B 64 = m.readW B 64 := by
  have := read_below_store m B v (d := 0) h he
  rwa [BitVec.add_zero] at this

theorem setLow_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
      .shift .shl .rcx 2, .store (field 13) .rcx]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 2)] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hs : ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

theorem setHigh_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 1)), .mov .rcx (.reg .rax), .shift .shl .rcx 2,
      .alu .add .rax (.reg .rcx), .mov .rcx (.mem (field 0)), .alu .add .rax (.reg .rcx), .store (field 12) .rax,
      .mov .rcx (.mem (field 1)), .shift .shl .rcx 2, .store (field 13) .rcx]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2 + p.kp),
        (13, BitVec.ofNat 64 p.L <<< 2)] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hs : ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

theorem twelve_thirteen : ∀ e ∈ [(12, (0 : BitVec 64)), (13, (0 : BitVec 64))], e.1 < 20 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> decide

theorem store_region {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {a b : BitVec 64}
    (hm : t.mem = writeFrame s.mem p.F [(12, a), (13, b)]) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ calleeSaved, r ∉ rs) :
    GenFrame p original used st t ∧ word t.mem p.F (8 * 12) = a ∧ word t.mem p.F (8 * 13) = b ∧
      Frame [p.frame] s.mem t.mem := by
  have hb : ∀ e ∈ [(12, a), (13, b)], e.1 < 20 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.store h.used_le _ hb (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide)
    hm k.2.1 k.2.2
    (fun r hr => k.gpr (hrs r hr)) (by
      rw [hm]; exact h.slots_kept _ hb (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide)), ?_, ?_, ?_⟩
  · rw [hm, writeFrame_word _ _ _ hb 12 (by decide)]; rfl
  · rw [hm, writeFrame_word _ _ _ hb 13 (by decide)]; rfl
  · rw [hm]; exact writeFrame_frame s.mem p.F _ hb

theorem GenFrame.key_nowrap {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : p.kp.toNat + 9 * p.L ≤ 2 ^ 64 := by
  have := h.input.nowrap (r := inKey original) (by simp [inWrites])
  rw [h.key_region] at this
  exact this

theorem GenFrame.len_valid {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : primeLenValid p.L := by
  rw [← h.input.2]; exact h.input.1.2.2.2.2.2.2.2.2.1

theorem GenFrame.frame_key {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.kp, 9 * p.L⟩ := by
  rw [← h.key_region]; exact h.input.frame_disjoint_writes (by simp [inWrites])

/-- `clearAround`: zeros at the key's buffer but `p`'s slot. -/
theorem clearAround_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s)
    (hp : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    WP isa clearAround s fun t => GenLive p original used st t ∧
      Frame [⟨p.kp, 9 * p.L⟩, p.frame] s.mem t.mem := by
  have hn := h.key_nowrap
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have hkr := h.key_region
  have hfk := h.frame_key
  have h4 : BitVec.ofNat 64 p.L <<< 2 = BitVec.ofNat 64 (4 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h5 : BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2 + p.kp = p.slot 5 := by
    rw [h4, SearchInit.add_ofNat, BitVec.add_comm]; congr 2; omega
  unfold clearAround
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (setLow_ok h) fun t1 ⟨hm1, k1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 (by decide)
  rw [h4] at w13
  refine WP.seq (WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega))
    (by omega) (by omega) (by omega)) fun t2 ⟨g2, z2, f2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (setHigh_ok g2) fun t3 ⟨hm3, k3⟩ => ?_)
  obtain ⟨g3, w12', w13', f3⟩ := store_region g2 hm3 k3 (by decide)
  rw [h4] at w13'
  rw [h5] at w12'
  refine WP.mono (clear_ok g3 w12' w13' (by rw [hkr]; exact slot_sub _ (by omega)) (by
      have : (p.slot 5).toNat = p.kp.toNat + 5 * p.L := by
        rw [GenPublic.slot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      omega) (by omega) (by omega)) fun t4 ⟨g4, z4, f4, _, _⟩ => ?_
  have hd0 : Region.Disjoint ⟨p.slot 5, 4 * p.L⟩ ⟨p.kp, 4 * p.L⟩ := by
    have := slot_disjoint p.kp (d := 5 * p.L) (n := 4 * p.L) (e := 0) (k := 4 * p.L) (.inr (by omega))
      (by omega) (by omega)
    rwa [← kp_zero] at this
  have hfs : p.frame.Disjoint ⟨p.slot 4, p.L⟩ := hfk.sub_right (slot_sub _ (by omega))
  have hf0 : p.frame.Disjoint ⟨p.kp, 4 * p.L⟩ := hfk.sub_right (Region.sub_prefix (by omega))
  have hfr : Frame [⟨p.kp, 9 * p.L⟩, p.frame] s.mem t4.mem := by
    have e1 : ∀ r ∈ [p.frame], ∃ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), p.frame], Region.Sub r q := fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩
    have e2 : ∀ {op : Addr} {n : Nat}, Region.Sub ⟨op, n⟩ ⟨p.kp, 9 * p.L⟩ →
        ∀ r ∈ [(⟨op, n⟩ : Region)], ∃ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), p.frame], Region.Sub r q := fun hs r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_cons_self .., hs⟩
    exact ((f1.sub e1).trans (f2.sub (e2 (Region.sub_prefix (by omega))))).trans
      ((f3.sub e1).trans (f4.sub (e2 (slot_sub _ (by omega)))))
  refine ⟨⟨g4, ⟨?_, ?_, ?_⟩⟩, hfr⟩
  · rw [bytes_kept f4 hd0 (by omega), bytes_kept f3 hf0 (by omega)]
    exact bytes_zero z2
  · exact bytes_zero z4
  · intro pB hpB
    rw [bytes_kept f4 (slot_disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega),
      bytes_kept f3 hfs (by omega), bytes_kept f2 ?_ (by omega), bytes_kept f1 hfs (by omega)]
    · exact hp pB hpB
    · have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := 4 * p.L) (k := p.L) (.inl (by omega))
        (by omega) (by omega)
      rwa [← kp_zero] at this

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The prime search's arguments

For the search of the progress' prime: `out` is `p`'s slot for `p`, `q`'s for
`q`; `p` is `p`'s slot, of `p_len` octets for `q` and none for `p`; `e` the
state's last word; the tape after the octets consumed. Its six stack
arguments in the call's frame of 48 octets below the controller's.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The search's output: `p`'s slot for `p`, `q`'s for `q`. -/
def outOf (p : GenPublic) (st : KeyProgress) : Addr := if phaseWord st.phase = 0 then p.slot 4 else p.slot 5

/-- The other prime's length: none for `p`. -/
def plenOf (p : GenPublic) (st : KeyProgress) : Nat := if phaseWord st.phase = 0 then 0 else p.L

/-- The search's stack arguments. -/
def callValues (p : GenPublic) (used : Nat) (st : KeyProgress) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (plenOf p st)), (1, p.rp + BitVec.ofNat 64 used),
    (2, BitVec.ofNat 64 (p.randLen - used)), (3, p.B), (4, BitVec.ofNat 64 (p.Z / 8)), (5, p.stp)]

theorem callValues_bound (p : GenPublic) (used : Nat) (st : KeyProgress) :
    ∀ e ∈ callValues p used st, e.1 < 20 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The search's arguments in registers. -/
def SearchRegs (p : GenPublic) (st : KeyProgress) (s : State) : Prop :=
  s.gpr .rdi = outOf p st ∧ s.gpr .rsi = BitVec.ofNat 64 p.L ∧ s.gpr .rdx = p.up ∧
    s.gpr .rcx = p.stp + BitVec.ofNat 64 48 ∧ s.gpr .r8 = BitVec.ofNat 64 8 ∧ s.gpr .r9 = p.slot 4

theorem phaseWord_le (ph : KeyPhase) : phaseWord ph ≤ 1 := by cases ph <;> simp only [phaseWord] <;> omega

theorem GenLive.frame_ld {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) {t : State} {k : Nat} (hw : t.wr = (allocated k s).wr) :
    ∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

theorem GenLive.state_ld {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) {t : State} {k : Nat}
    (hw : t.wr = (allocated k s).wr) :
    ∀ d, d + 8 ≤ 56 → InRegions (t.rd ++ t.wr) (p.stp + BitVec.ofNat 64 d) 8 := by
  intro d hd
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  refine ⟨inState original, List.mem_append_right _ ?_, by rw [hst]; exact Offset.contains_base _ hd (by omega)⟩
  rw [hw]
  exact List.mem_cons_of_mem _ (by rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites]))

/-- A read of the frame sees past a store to the call's frame below it. -/
theorem read_past_call (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 48)
    (he : e + 56 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have hF : F + BitVec.ofNat 64 e = F - BitVec.ofNat 64 48 + BitVec.ofNat 64 (48 + e) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [hF]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := 48 + e) (n := 8) (e := d) (k := 8) (Or.inr (by omega))
    (by omega) (by omega)) (by decide)

theorem read_past_call0 (m : Mem) (F : Addr) (v : BitVec 64) {e : Nat} (he : e + 56 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 48) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have := read_past_call m F v (d := 0) (by decide) he
  rwa [BitVec.add_zero] at this

theorem read_past_call00 (m : Mem) (F : Addr) (v : BitVec 64) {d : Nat} (hd : d + 8 ≤ 48) :
    (m.writeW (F - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) v).readW F 64 = m.readW F 64 := by
  have := read_past_call m F v (e := 0) hd (by decide)
  rwa [BitVec.add_zero] at this

theorem search_args_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    WP isa (.block searchArgs) (allocated 48 s) fun t =>
      SearchRegs p st t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 48 s) t := by
  have hl := h.frame_ld (t := allocated 48 s) rfl
  have hsl := h.state_ld (t := allocated 48 s) rfl
  have hl0 : InRegions ((allocated 48 s).rd ++ (allocated 48 s).wr) p.F 8 := by
    simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hsp : (allocated 48 s).gpr .rsp = p.F - BitVec.ofNat 64 48 := by rw [allocated_rsp, h.rsp]
  have hr12 : (allocated 48 s).gpr .r12 = p.F := by rw [allocated_reg _ _ _ (by decide), h.r12]
  have hF := h.input.F_toNat
  have hroom : 552 ≤ p.sp.toNat := h.input.room
  have haw : (allocated 48 s).wr = ⟨p.F - BitVec.ofNat 64 48, 48⟩ :: s.wr := by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 48, 48⟩ : Region) :: s.wr = _
    rw [h.rsp]
  have scr : Scr (allocated 48 s) (p.F - BitVec.ofNat 64 48) 48 :=
    Scr.of_mem (by rw [haw]; exact List.mem_cons_self ..) (by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 48).toNat = 48 from rfl]; omega)]
      have := h.input.top
      simp only [show (BitVec.ofNat 64 48).toNat = 48 from rfl]
      omega)
  have hs : ∀ d, d + 8 ≤ 48 → InRegions (allocated 48 s).wr (p.F - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 48 s).wr (p.F - BitVec.ofNat 64 48) 8 := by
    simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used) :
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv0 := hv 0 p.kp (by simp [GenPublic.headers])
  have hv1 := hv 1 (BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv2 := hv 2 p.up (by simp [GenPublic.headers])
  have hv3 := hv 3 p.rp (by simp [GenPublic.headers])
  have hv4 := hv 4 (BitVec.ofNat 64 p.randLen) (by simp [GenPublic.headers])
  have hv5 := hv 5 p.B (by simp [GenPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := hv 7 p.stp (by simp [GenPublic.headers])
  have hv8 := hv 8 (BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8
  have hph : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) :=
    h.state.phase
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have hul := h.used_le
  have hrl : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hsub : BitVec.ofNat 64 p.randLen - BitVec.ofNat 64 used = BitVec.ofNat 64 (p.randLen - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl,
      Nat.mod_eq_of_lt (by omega : used < 2 ^ 64)]
    omega
  have h4 : BitVec.ofNat 64 p.L <<< 2 + p.kp = p.slot 4 := by
    rw [SearchInit.shl_ofNat _ _ (by omega), BitVec.add_comm]; congr 2; omega
  have h5 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (Q := fun t =>
    SearchRegs p st t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold searchArgs SearchRegs writeFrame callValues outOf plenOf
  simp only [List.foldl_cons, List.foldl_nil]
  have hph1 := phaseWord_le st.phase
  rcases (by omega : phaseWord st.phase = 0 ∨ phaseWord st.phase = 1) with hp | hp <;>
  rw [hp] at hph <;>
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, allocated_mem,
    hsp, hr12, eval, execCmov, hl0, hl 8 (by decide), hl 16 (by decide), hl 24 (by decide),
    hl 32 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hsl 32 (by decide), read_past_call, read_past_call0, read_past_call00, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hph, hsub, h4, h5, hp,
    hs0, hs 8 (by decide), hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide)] <;>
  first | exact ⟨rfl, rfl⟩ | rfl

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The controller's call of the prime search

The search's regions, from the controller's: its output and the other prime in
the key's buffer, `used`, the working space, the state's first four words,
its exponent in the state's last, the rest of the tape, and its stack
arguments, return address and stack below the controller's frame.
-/

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

/-! ## The prime search, run

`searchRun`: in a frame of its stack arguments, the search's arguments and its
call. It leaves the search's status, its prime or zeros at its output, the
octets it consumed at `used`, and its counted candidates left and request in
the state; it writes nothing else but the working space and the stack.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem freed freed_rsp
  freed_reg frame_alloc)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf)

/-- The prime search, as the controller calls it. -/
def searchCall (v : RoundImpl) : Prog isa :=
  .call ("vg_rsa_prime_search" ++ v.suffix) (Search.searchCode v)

/-- What the search may write, as the controller sees it. -/
def searchChanges (p : GenPublic) (st : KeyProgress) : List Region :=
  [rO p st, rU p, rS p, rT p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩]

/-- What the search of the progress' prime at `used` leaves. -/
structure AfterSearch (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress)
    (s t : State) : Prop where
  frame : GenFrame p original used ⟨st.left, st.phase, (primeOf p.L p.eB st ((genRand original).drop used)).remaining⟩ t
  status : ((t.gpr .rax).setWidth 32).toNat = (primeOf p.L p.eB st ((genRand original).drop used)).status
  usedw : word t.mem p.up 0 = BitVec.ofNat 64 (primeOf p.L p.eB st ((genRand original).drop used)).used
  out : Spec.Rsa.bytesAt t.mem (outOf p st) p.L =
    (match (primeOf p.L p.eB st ((genRand original).drop used)).outcome with
      | .accepted c => Spec.Rsa.i2osp c p.L
      | _ => List.replicate p.L 0)
  req : ∃ requested, word t.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (primeOf p.L p.eB st ((genRand original).drop used)).Requests (primeEntropy p.L) requested
  mem : Frame (searchChanges p st) s.mem t.mem

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem GenLive.regions (h : GenLive p original used st s) :
    inKey original = ⟨p.kp, 9 * p.L⟩ ∧ inUsed original = rU p ∧ inScr original = rS p ∧
      inState original = cS p ∧ inRand original = cR p := by
  refine ⟨h.key_region, ?_, ?_, ?_, ?_⟩ <;> rw [← h.input.2] <;> rfl

theorem search_covers_writes (h : GenLive p original used st s) {u : State}
    (hw : u.wr = (allocated 48 s).wr) : Covers (sWrites p st) u.wr := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, ht, -⟩ := h.regions
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  rw [hk, hu, hs, ht] at hwo
  rw [hw]
  refine Covers.of_sub fun r hr => ?_
  have hin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), rU p, rS p, cS p], q ∈ (allocated 48 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hL := hf.len.1
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), if phaseWord st.phase = 0 then 4 * p.L else 5 * p.L, ?_, ?_⟩
    · simp only [outOf]; split <;> rfl
    · show _ + p.L ≤ 9 * p.L
      split <;> omega
  · exact ⟨rU p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨cS p, hin _ (by simp), 0, by simp, by simp⟩

theorem search_covers_reads (h : GenLive p original used st s) {u : State}
    (hrd : u.rd = (allocated 48 s).rd) (hw : u.wr = (allocated 48 s).wr) :
    Covers (sReads p used st ++ sWrites p st) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (search_covers_writes h hw).right
  have hf := h.input.cfacts
  obtain ⟨hk, -, -, ht, hr⟩ := h.regions
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  have hro : original.rd = [inRand original, inArgs original] := h.input.1.2.2.1
  rw [hk, ht] at hwo
  rw [hr] at hro
  have hul := h.used_le
  have hL := hf.len.1
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [sReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  have hwin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), cS p], q ∈ (allocated 48 s).rd ++ (allocated 48 s).wr := by
    intro q hq
    refine List.mem_append_right _ ?_
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  rcases hr' with rfl | rfl | rfl | rfl
  · exact ⟨cS p, hwin _ (by simp), 48, rfl, by simp⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hwin _ (by simp), 4 * p.L, rfl, by
      show _ + plenOf p st ≤ 9 * p.L; have := plen_le (p := p) (st := st); omega⟩
  · refine ⟨cR p, List.mem_append_left _ ?_, used, rfl, by simp; omega⟩
    show cR p ∈ s.rd
    rw [h.rd, hro]; simp
  · refine ⟨⟨s.gpr .rsp - BitVec.ofNat 64 48, 48⟩, List.mem_append_right _ (List.mem_cons_self ..), 0, ?_, by simp⟩
    rw [h.rsp, F_48, BitVec.add_zero]

end

/-- The search's result, from the controller's loop state. -/
theorem callS_result {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s)
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (ha : SearchRegs p st u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    Search.searchResult (callS p used st u) = primeOf p.L p.eB st ((genRand original).drop used) := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callS_args (used := used) (st := st) hu hm
  have hfr := callS_frame hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, sR⟩ := hst
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hL := hf.len
  obtain ⟨hL1, hL2, -⟩ := hL
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p) ∨ Region.Sub R (cR p))
      (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callS p used st u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfr.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR, sR.sub_left hR]
  have hlim : st.remaining < 2 ^ 64 := by
    have := h.state.remaining_le
    unfold KeySearch.limitOf primeLimit at this
    split at this <;> omega
  unfold Search.searchResult
  congr 1
  · simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), hsi, tl]
  · simp only [Search.searchE, callS_gpr (show Reg.rcx ≠ .rsp by decide), callS_gpr (show Reg.r8 ≠ .rsp by decide),
      hcx, h8, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    exact hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr (.inl rE_sub)) (by show 8 ≤ 2 ^ 64; decide)
  · simp only [Search.searchP, callS_gpr (show Reg.r9 ≠ .rsp by decide), h9, a0,
      toNat_ofNat_lt (show plenOf p st < 2 ^ 64 by have := plen_le (p := p) (st := st); omega)]
    have hk := h.key.other
    unfold plenOf
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => simp [phaseWord, KeyPhase.other, Spec.Rsa.bytesAt]
    | q pB =>
      simp only [phaseWord, Nat.one_ne_zero, ↓reduceIte, KeyPhase.other]
      rw [← hk pB rfl]
      exact hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (slot_sub _ (by omega))) (by show p.L ≤ 2 ^ 64; omega)
  · simp only [Search.searchRemaining, a5]
    have h0 := h.state.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0
    have := hfr.readW (r := cS p) (a := p.stp) (w := 64)
      (by simpa only [BitVec.add_zero] using Offset.contains_base p.stp (d := 0) (n := 8) (k := 56) (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sT) (by decide)
    rw [this, h0, toNat_ofNat_lt hlim]
  · simp only [Search.searchRand, a1, a2, toNat_ofNat_lt (show p.randLen - used < 2 ^ 64 by have := hf.rand64; omega)]
    have := hbytes (R := rR p used) (.inr (.inr (rR_sub h.used_le))) (by have := hf.rand64; simp; omega)
    simp only at this
    rw [this, Search.bytesAt_drop, h.random]

theorem stack_mem (p : GenPublic) (st : KeyProgress) :
    (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region) ∈ searchChanges p st := by
  simp [searchChanges]

theorem below_sub (sp : Addr) {n : Nat} (hn : n ≤ 344) :
    Region.Sub (below (sp - BitVec.ofNat 64 208) n) ⟨sp - BitVec.ofNat 64 552, 392⟩ := by
  simp only [below, BitVec.sub_sub]
  rw [← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem searchChanges_sub {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    ∀ r ∈ searchChanges p st, ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, -, -⟩ := h.regions
  have hT : (⟨stackArg original 1, 32⟩ : Region) = rT p := by rw [← h.input.2]; rfl
  have hS : (⟨original.gpr .rsp - BitVec.ofNat 64 stackUse, 392⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 552, 392⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hu, hs, hT, hS]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., rO_sub hf⟩
  all_goals exact ⟨_, by simp, fun _ h => h⟩

theorem search_run (v : RoundImpl) {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    WP isa (searchRun (searchCall v)) s (AfterSearch p original used st s) := by
  have hf := h.input.cfacts
  have hF := h.input.F_toNat
  have hroom := h.input.room
  unfold searchRun searchCall
  apply frame_alloc (by decide) (by decide) (by decide) (by rw [h.rsp, hF]; have : 552 ≤ p.sp.toNat := hroom; omega)
  refine WP.seq (WP.mono (search_args_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp, F_48]
  have hd : (Search.searchCode v).x86_64Depth ≤ 336 := Search.searchCode_depth v
  refine WP.callF (k := Search.searchContract) (Search.search_correct v) (SpSafe.of_all (Search.searchCode_sp v))
    (by omega) (callS_pre h hu ha hm) (search_covers_reads h k.2.1 k.2.2) (search_covers_writes h k.2.2)
    fun t htr htw hg hfr ⟨s₂, hm₂, hg₂, hpost⟩ _ => ?_
  have hres := callS_result h hu ha hm
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hlen : Search.searchLen (callS p used st u) = p.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), hsi]
    exact toNat_ofNat_lt (by have := hf.len.2.1; omega)
  obtain ⟨hst, hout, hused, req, hwords, hreq⟩ := hpost
  have hdi' : (callS p used st u).gpr .rdi = outOf p st := by rw [callS_gpr (by decide)]; exact hdi
  have hdx' : (callS p used st u).gpr .rdx = p.up := by rw [callS_gpr (by decide)]; exact hdx
  simp only [hres, hlen, hm₂, a5, hdi', hdx'] at hst hout hused hwords hreq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 1 = [0] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hwords hused
  simp only [Nat.reduceMul] at hwords hused
  obtain ⟨w0, w1, w2, w3⟩ := hwords
  -- The memory: the stack arguments, then the search.
  have f₀ : Frame (searchChanges p st) s.mem u.mem := by
    rw [hm, F_48]
    apply (Search.writeFrame_frame_size _ _ (callValues p used st) (size := 48) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, stack_mem p st, Offset.sub_below _ (by decide) (by decide)⟩
  have f₁ : Frame (searchChanges p st) u.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨r, ?_, fun _ h => h⟩
      simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, stack_mem p st, by rw [hu]; exact below_sub _ (by omega)⟩
  have hframe := f₀.trans f₁
  have hrem := KeySearch.primeSearch_remaining_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
  have hle := h.state.remaining_le
  have htsp : t.gpr .rsp = (allocated 48 s).gpr .rsp := by rw [hg _ (by decide), k.gpr (by decide)]
  refine ⟨htsp, htw.trans k.2.2, h.toGenFrame.restore (htr.trans k.2.1) (show t.wr.tail = s.wr by rw [htw, k.2.2]; rfl)
      (fun r hr => ?_) (hframe.sub (searchChanges_sub h)) ?_ w1 w2 (.inl rfl) rfl (Nat.le_trans hrem hle), ?_, ?_, ?_,
      ⟨req, ?_, hreq⟩, hframe⟩
  · have hnot : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] := by revert r; decide
    by_cases he : r = .rsp
    · subst he
      rw [freed_rsp, htsp, allocated_rsp]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ he, hg r hr, k.gpr hnot, allocated_reg _ _ _ he]
  · exact w0
  · rw [freed_reg _ _ _ (by decide), ← hg₂ _ (by decide)]; exact hst
  · exact hused
  · exact hout
  · exact w3

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The controller's blocks after a search

The octets the search consumed added to the frame's count, and the stores
that start the next prime's search (`nextPrime`) or end the key search
(`finishWith`), each with the frame and the state they leave.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

namespace GenFrame

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem scr (h : GenFrame p original used st s) : Scr s p.F 160 := h.input.frame_scr h.wr

theorem state_region (h : GenFrame p original used st s) : inState original = ⟨p.stp, 56⟩ := by
  rw [← h.input.2]; rfl

theorem used_region (h : GenFrame p original used st s) : inUsed original = ⟨p.up, 8⟩ := by
  rw [← h.input.2]; rfl

theorem stateScr (h : GenFrame p original used st s) : Scr s p.stp 56 := by
  have hn := h.input.nowrap (r := inState original) (by simp [inWrites])
  rw [h.state_region] at hn
  refine Scr.of_mem ?_ hn
  rw [h.wr, h.input.1.2.2.2.1, ← h.state_region]
  simp [inWrites]

theorem usedScr (h : GenFrame p original used st s) : Scr s p.up 8 := by
  have hn := h.input.nowrap (r := inUsed original) (by simp [inWrites])
  rw [h.used_region] at hn
  refine Scr.of_mem ?_ hn
  rw [h.wr, h.input.1.2.2.2.1, ← h.used_region]
  simp [inWrites]

/-- A header word of the frame. -/
theorem header (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64} (hj : (j, v) ∈ p.headers used) :
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj

end GenFrame

/-- The frame's headers after the octets consumed are `u`. -/
theorem slots_used {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (u : Nat) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20)
    (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (p.headers u) := by
  have hb' : ∀ e ∈ (8, BitVec.ofNat 64 u) :: values, e.1 < 20 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · show 8 < 20; decide
    · exact hb e he
  have hw (j : Nat) (hj : j < 20) (hj8 : j ≠ 8) (hv : ∀ e ∈ values, j ≠ e.1) :
      word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [writeFrame_word _ _ _ hb' j hj]
    show frameValue values j (if j = 8 then _ else _) = _
    rw [ite_eq_right hj8]
    exact frameValue_unchanged _ _ _ hv
  have hw8 : word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * 8) = BitVec.ofNat 64 u := by
    rw [writeFrame_word _ _ _ hb' 8 (by decide)]
    show frameValue values 8 (if 8 = 8 then _ else _) = _
    rw [ite_eq_left rfl]
    exact frameValue_unchanged _ _ _ fun e he heq => (hnot e he).2.2.2.2.2.2.2.2.1 heq.symm
  have hk (j : Nat) (v : BitVec 64) (hj : j < 20) (hj8 : j ≠ 8) (hjv : (j, v) ∈ p.headers used)
      (hv : ∀ e ∈ values, j ≠ e.1) :
      word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * j) = v := by
    have hh := h.headers (j, v) hjv
    dsimp only at hh
    rw [hw j hj hj8 hv]; exact hh
  simp only [Slots, GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨hk 0 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).1 q.symm,
    hk 1 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.1 q.symm,
    hk 2 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.1 q.symm,
    hk 3 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.1 q.symm,
    hk 4 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.2.1 q.symm,
    hk 5 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.2.2.1 q.symm,
    hk 6 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.1 q.symm,
    hk 7 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.2.1 q.symm,
    hw8,
    hk 11 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.2.2.2 q.symm⟩

/-- The status, the octets the search consumed and the count of those
consumed so far. -/
theorem head_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {n status : Nat}
    (hs : ((s.gpr .rax).setWidth 32).toNat = status) (hn : word s.mem p.up 0 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)), .mov .rcx (.mem { base := .rcx }),
      .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx), .store (field 8) .rdx,
      .alu .test .rax (.reg .rax)]) s fun t =>
      (eval .e t = some (decide (status = 0)) ∧ t.gpr .rax = BitVec.ofNat 64 status ∧
        t.gpr .rcx = BitVec.ofNat 64 n ∧
        t.mem = writeFrame s.mem p.F [(8, BitVec.ofNat 64 used + BitVec.ofNat 64 n)]) ∧
      Keep [.rax, .rcx, .rdx] s t := by
  have scr := h.scr
  have hu := h.usedScr
  have h2 := h.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := h.header (j := 8) (v := BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  have hl2 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 16) 8 := scr.ld (d := 16) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 64) 8 := scr.ld (d := 64) (by decide)
  have hs8 : InRegions s.wr (p.F + BitVec.ofNat 64 64) 8 := scr.st (d := 64) (by decide)
  have hlu : InRegions (s.rd ++ s.wr) p.up 8 := by simpa only [off, BitVec.add_zero] using hu.ld (d := 0) (by decide)
  have hn' : s.mem.readW p.up 64 = BitVec.ofNat 64 n := by simpa only [Bignum.word, off, BitVec.add_zero] using hn
  simp only [Nat.reduceMul] at h2 h8
  have hax : ((s.gpr .rax).setWidth 32).setWidth 64 = BitVec.ofNat 64 status := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]
  have he : (BitVec.ofNat 64 status &&& BitVec.ofNat 64 status == (0 : BitVec 64)) = decide (status = 0) := by
    apply Bool.eq_iff_iff.mpr
    have := ((s.gpr .rax).setWidth 32).isLt
    simp only [BitVec.and_self, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  refine WP.keep [.rax, .rcx, .rdx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl2, hl8, hs8, hlu, h2, h8, hn', hax, eval, he]

/-! ## Stores to the state and the frame -/

/-- The state's words `0`, `4` and `5` and the frame's status or region to
zero stored. -/
def StateStores (sv fv : List (Nat × BitVec 64)) : Prop :=
  (∀ e ∈ sv, e.1 = 0 ∨ e.1 = 4 ∨ e.1 = 5) ∧ (∀ e ∈ fv, e.1 = 10 ∨ e.1 = 12 ∨ e.1 = 13)

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

theorem state_frame (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.stp, 56⟩ := h.input.frame_state

/-- What stores to the state's first six words and to the frame keep: the
memory outside them. -/
theorem _root_.VG.Proof.RsaKeyGen.X86_64.Generate.stores_frame (p : GenPublic) (m : Mem)
    {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame (writeFrame m p.stp sv) p.F fv) := by
  have h1 : Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame m p.stp sv) :=
    (Search.writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  have h2 : Frame [⟨p.stp, 48⟩, p.frame] (writeFrame m p.stp sv) (writeFrame (writeFrame m p.stp sv) p.F fv) :=
    (writeFrame_frame _ _ fv fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide).sub
      fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp, fun _ h => h⟩
  exact h1.trans h2

theorem stores_changes (h : GenFrame p original used st s) :
    ∀ r ∈ [(⟨p.stp, 48⟩ : Region), p.frame], ∃ q ∈ GenInput.changes original, Region.Sub r q := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨inState original, by simp [GenInput.changes, inWrites], by
      rw [h.state_region]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩

/-- A region apart from the state's first six words and the frame is kept. -/
theorem _root_.VG.Proof.RsaKeyGen.X86_64.Generate.stores_bytes (p : GenPublic) (m : Mem)
    {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) {R : Region} (hs : (⟨p.stp, 48⟩ : Region).Disjoint R) (hf : p.frame.Disjoint R)
    (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame m p.stp sv) p.F fv) R.base R.len =
      Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine (stores_frame p m hv).bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  exacts [hs.symm, hf.symm]

/-- Through stores to the state's words `0`, `4` and `5` and to the frame's
status or region to zero, for the progress `st'` those words hold. -/
theorem setState (h : GenFrame p original used st s) {st' : KeyProgress} {sv fv : List (Nat × BitVec 64)}
    (hv : StateStores sv fv) (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F fv)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64) :
    GenFrame p original used st' t := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hsd := h.state_frame
  have hnst : p.stp.toNat + 56 ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inState original) (by simp [inWrites])
    rwa [h.state_region] at this
  -- The frame's words through the state's stores.
  have hF (j : Nat) (hj : j < 20) (hnot : ∀ e ∈ fv, j ≠ e.1) :
      word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [hm, writeFrame_word _ _ _ hfb j hj, frameValue_unchanged _ _ _ hnot]
    refine (Search.writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).readW (r := p.frame)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => ?_) (by decide)
    obtain rfl := List.mem_singleton.mp hq
    exact hsd.sub_right (Region.sub_prefix (by decide))
  -- The state's words through the frame's stores.
  have hS (j : Nat) (hj : j < 7) :
      word t.mem p.stp (8 * j) = frameValue sv j (word s.mem p.stp (8 * j)) := by
    rw [hm, ← writeFrame_word _ _ _ hsb j (by omega)]
    exact (writeFrame_frame _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact hsd.symm) (by decide)
  have hnf : ∀ j, j ≠ 10 → j ≠ 12 → j ≠ 13 → ∀ e ∈ fv, j ≠ e.1 := fun j h10 h12 h13 e he heq => by
    rcases hv.2 e he with h | h | h <;> omega
  have hns : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 5 → ∀ e ∈ sv, j ≠ e.1 := fun j h0 h4 h5 e he heq => by
    rcases hv.1 e he with h | h | h <;> omega
  have hfr : Frame (GenInput.changes original) s.mem t.mem := by
    rw [hm]; exact (stores_frame p s.mem hv).sub h.stores_changes
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, (hg .rsp (by decide)).trans h.rsp,
    (hg .r12 (by decide)).trans h.r12, fun reg hreg hne hsp => (hg reg hreg).trans (h.saved reg hreg hne hsp),
    ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hrem, hlt⟩⟩
  · exact (hF 9 (by decide) (hnf 9 (by decide) (by decide) (by decide))).trans h.savedR12
  · exact (h.input.random_frame hfr).trans h.random
  · intro e he
    have hj := GenPublic.headers_bound _ _ e he
    rw [hF e.1 hj (hnf _ ?_ ?_ ?_)]
    · exact h.headers e he
    all_goals
      simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · have := hS 0 (by decide); rw [h0] at this; exact this
  · have := hS 1 (by decide)
    rw [frameValue_unchanged _ _ _ (hns 1 (by decide) (by decide) (by decide))] at this
    exact this.trans h.state.len
  · have := hS 2 (by decide)
    rw [frameValue_unchanged _ _ _ (hns 2 (by decide) (by decide) (by decide))] at this
    exact this.trans h.state.cap
  · have := hS 4 (by decide); rw [h4] at this; exact this
  · have := hS 5 (by decide); rw [h5] at this; exact this
  · rw [← h.state.e, hm]
    refine stores_bytes p s.mem (R := ⟨p.stp + 48, 8⟩) hv ?_ ?_ (by show 8 ≤ 2 ^ 64; decide)
    · intro x hx hy
      exact Offset.sep p.stp (d := 0) (n := 48) (e := 48) (k := 8) (.inl (by omega)) (by omega) (by omega) x
        (by rw [BitVec.add_zero]; simp only [Region.Contains] at hx; omega)
        (by
          have e48 : (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 := rfl
          simp only [Region.Contains, e48] at hy; omega)
    · exact hsd.sub_right (Offset.sub_base _ (by decide))

end GenFrame

/-! ## The blocks -/

theorem imm32_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

/-- The next prime's search, in `phase`: all its counted candidates, and the
status that goes on. -/
theorem nextPrime_ok (h : GenFrame p original used st s) {phase : Nat} (hph : phase < 2) :
    WP isa (.block (nextPrime phase)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
        (4, BitVec.ofNat 64 phase)]) p.F [(10, (4 : BitVec 64))] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.header (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl11 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 88) 8 := scr.ld (d := 88) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs0 : InRegions s.wr p.stp 8 := by simpa only [off, BitVec.add_zero] using sst.st (d := 0) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  simp only [Nat.reduceMul] at h7 h11
  have hi := imm32_ofNat (n := phase) (by omega)
  have h4 : (4 : BitVec 32).setWidth 64 = (4 : BitVec 64) := by decide
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl11, hs10, hs0, hs4, h7, h11, hi, h4]

/-- The end of the key search with `status`: no phase or generations left. -/
theorem finishWith_ok (h : GenFrame p original used st s) {status : Nat} (hs : status < 4) :
    WP isa (.block (finishWith status)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(4, (0 : BitVec 64)), (5, (0 : BitVec 64))]) p.F
        [(10, BitVec.ofNat 64 status)] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  simp only [Nat.reduceMul] at h7
  have hi := imm32_ofNat (n := status) (by omega)
  have h0 : (0 : BitVec 32).setWidth 64 = (0 : BitVec 64) := by decide
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame finishWith
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hs10, hs4, hs5, h7, hi, h0]

/-- The status, stored. -/
theorem storeStatus_ok (h : GenFrame p original used st s) {status : Nat}
    (hs : s.gpr .rax = BitVec.ofNat 64 status) :
    WP isa (.block [.store (field 10) .rax]) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp []) p.F [(10, BitVec.ofNat 64 status)] ∧ Keep [] s t := by
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := h.scr.st (d := 80) (by decide)
  refine WP.keep [] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, h.r12, hs10, hs]

/-- The generations left, compared with 2. -/
theorem left_ok (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 7)), .mov .rcx (.mem (stw 5)), .alu .cmp .rcx (.imm 2)]) s fun t =>
      (eval .b t = some (decide (st.left < 2)) ∧ t.gpr .rax = p.stp ∧ t.gpr .rcx = BitVec.ofNat 64 st.left ∧
        t.mem = s.mem) ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl5 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 40) 8 := sst.ld (d := 40) (by decide)
  have h5 : s.mem.readW (p.stp + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 st.left := h.state.left
  simp only [Nat.reduceMul] at h7
  have hlt := h.state.left_lt
  have hb : decide ((BitVec.ofNat 64 st.left).toNat < BitVec.toNat (2 : BitVec 64)) = decide (st.left < 2) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rfl
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl5, h7, h5, eval, hb]

/-- The phase, tested. -/
theorem phase_ok (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 7)), .mov .rcx (.mem (stw 4)), .alu .test .rcx (.reg .rcx)]) s fun t =>
      (eval .e t = some (decide (phaseWord st.phase = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl4 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 32) 8 := sst.ld (d := 32) (by decide)
  have h4 : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) := h.state.phase
  simp only [Nat.reduceMul] at h7
  have he : (BitVec.ofNat 64 (phaseWord st.phase) &&& BitVec.ofNat 64 (phaseWord st.phase) == (0 : BitVec 64)) =
      decide (phaseWord st.phase = 0) := by
    have := phaseWord_le st.phase
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.and_self, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl4, h7, h4, eval, he]

end

end VG.Proof.RsaKeyGen.X86_64.Generate
