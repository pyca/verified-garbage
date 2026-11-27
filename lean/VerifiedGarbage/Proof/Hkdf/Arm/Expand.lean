module

public import VerifiedGarbage.Proof.Hkdf.Arm.Key
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
public import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Hkdf.Arm
meta import VerifiedGarbage.Proof.Hkdf.Arm.Key

/-!
# HKDF on 32-bit ARM: `vg_hkdf_expand`, correct and constant time

The contract the proof is written against (`expandR`), for the table `hmac`
of one hash function `w` (`HVar`), whose functions an indirect call of
`f`'s reaches: `expand(key, info, info_len, out, out_len, hmac)` writes
HKDF-Expand's `out_len` bytes to `out`, for every pseudorandom key the
states at `key` are keyed with (`Spec.Hkdf.Keyed`).

As on AArch64 (`Proof/Hkdf/AArch64/Expand.lean`): the frame (`eFr` bytes:
the save area, the counter's word, the length of `T(i - 1)`, `T(i)`, the
working state, then the working space) allocated, the prologue saves our
caller's registers and our return address and keeps the arguments and the
bytes of `out` left in callee-saved registers, and the counter and the
length of `T(i - 1)` in the frame (`pro_ok`, from which on `ER` holds). Each
block (`block_ok`) makes the working state the inner state at `key` (a copy
of its 192 bytes), absorbs `T(i - 1)`, `info` and the counter, finalizes
with the outer state at `key + 192` into `T(i)` in the frame, and copies its
first `min(D, rem)` bytes to `out`; before block `i + 1`, `out`'s first
`min(i D, L)` bytes are `T(1) ‖ … ‖ T(i)`'s (`EI`). The blocks run while
bytes of `out` are left (`loop_ok`), and the epilogue restores our caller's
registers and our return address.
-/

@[expose] public section

namespace VG.Proof.Hkdf.Arm.Expand

open VG VG.Arm VG.Arm.Steps
open VG.Impl.Hkdf.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns tD tB)
open VG.Proof.HmacTable.Arm (HVar TabOK TabMem tA)
open VG.Proof.Hkdf.Arm (HOk StackAt base stackAt toNat_addr TabFn tcall_ok tcall_rel push_gpr Ck rel_ck
  rel_blk rel_sp rel_both contains_pre bytes_keep repr_keep reprOK stateBytes_eq blockKey_len append_zero)
open VG.Arm.FrameStack (armStack addr_sub' sub_toNat')
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

/-- The stack `vg_hkdf_expand` uses: its frame, and the 32 bytes below it
that the calls use. -/
def eStack : Nat := eFr + 32

theorem eFr_eq : eFr = 2176 := rfl
theorem eStack_eq : eStack = 2208 := rfl

/-- `expand(key, info, info_len, out, out_len, hmac)`, with `N` bytes of
stack, for the table `hmac` of `w`, whose functions an indirect call of
`f`'s reaches, with the addresses of the functions `ns` public. -/
def expandR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let info : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let tab : Region := ⟨State.addr (stackArg s 1), 24⟩
    let args : Region := ⟨State.addr s.sp, 8⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 N, N⟩
    N ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧ s.rd = [key, info, tab, args] ∧ s.wr = [out] ∧
      key.Disjoint out ∧ info.Disjoint out ∧ out.Disjoint tab ∧ out.Disjoint args ∧
      stk.Disjoint key ∧ stk.Disjoint info ∧ stk.Disjoint out ∧ stk.Disjoint tab ∧ stk.Disjoint args ∧
      (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 24 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat ≤ 255 * w.F.H.D ∧ TabMem w.F s.syms (stackArg s 1) s.mem ∧
      s.mem.readW (tA (stackArg s 1) tD) 32 = BitVec.ofNat 32 w.F.H.D ∧
      s.mem.readW (tA (stackArg s 1) tB) 32 = BitVec.ofNat 32 w.F.H.B ∧ TabOK w.F f s.syms
  post s s' := ∀ prk, Spec.Hkdf.Keyed w.ok.hH.SH s.mem (State.addr (s.gpr .r0)) prk →
    Spec.Hkdf.expand w.ok.hH.SH.H w.F.H.D prk (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (stackArg s 0).toNat = some (bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-! ## Where things are -/

section
variable (s : State)

/-- The stack's lowest byte. -/
abbrev B : Addr := base s.sp eFr
/-- The frame's base. -/
abbrev fb : BitVec 32 := s.sp - BitVec.ofNat 32 eFr
/-- An address in the frame. -/
abbrev fA (o : Nat) : Addr := B s + BitVec.ofNat 64 (32 + o)

abbrev keyA : Addr := State.addr (s.gpr .r0)
abbrev infoA : Addr := State.addr (s.gpr .r1)
abbrev infoLen : Nat := (s.gpr .r2).toNat
abbrev outA : Addr := State.addr (s.gpr .r3)
abbrev outLen : Nat := (stackArg s 0).toNat

abbrev keyR : Region := ⟨keyA s, 384⟩
abbrev infoR : Region := ⟨infoA s, infoLen s⟩
abbrev outR : Region := ⟨outA s, outLen s⟩
abbrev tabR : Region := ⟨State.addr (stackArg s 1), 24⟩
abbrev argR : Region := ⟨State.addr s.sp, 8⟩
abbrev stkR : Region := ⟨B s, eStack⟩

/-- `info`. -/
abbrev infoOf : List Byte := bytesAt s.mem (infoA s) (infoLen s)

end

/-- The pseudorandom keys the states at `key` are keyed with. -/
abbrev Keyd (w : HVar) (s : State) (prk : List Byte) : Prop := Spec.Hkdf.Keyed w.ok.hH.SH s.mem (keyA s) prk

/-- The facts of `expandR`'s precondition, by name. -/
structure EP (w : HVar) (f : Fns) (s : State) : Prop where
  st : StackAt s.sp eFr (B s)
  sp : eStack ≤ s.sp.toNat
  sp8 : s.sp.toNat + 8 ≤ 2 ^ 32
  rd : s.rd = [keyR s, infoR s, tabR s, argR s]
  wr : s.wr = [outR s]
  k_o : (keyR s).Disjoint (outR s)
  i_o : (infoR s).Disjoint (outR s)
  o_t : (outR s).Disjoint (tabR s)
  o_a : (outR s).Disjoint (argR s)
  s_k : (stkR s).Disjoint (keyR s)
  s_i : (stkR s).Disjoint (infoR s)
  s_o : (stkR s).Disjoint (outR s)
  s_t : (stkR s).Disjoint (tabR s)
  s_a : (stkR s).Disjoint (argR s)
  nk : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  ni : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  no : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nt : (stackArg s 1).toNat + 24 ≤ 2 ^ 32
  ol : (stackArg s 0).toNat ≤ 255 * w.F.H.D
  tm : TabMem w.F s.syms (stackArg s 1) s.mem
  tD : s.mem.readW (tA (stackArg s 1) tD) 32 = BitVec.ofNat 32 w.F.H.D
  tB : s.mem.readW (tA (stackArg s 1) tB) 32 = BitVec.ofNat 32 w.F.H.B
  tok : TabOK w.F f s.syms

theorem ep_of {w : HVar} {f : Fns} {ns : List String} {s : State} (hp : (expandR w f ns eStack).pre s) :
    EP w f s :=
  let ⟨hsp, h8, hrd, hwr, ko, io, ot, oa, sk, si, so, st, sa, nk, ni, no, nt, ol, tm, td, tb, tok⟩ := hp
  ⟨stackAt hsp, hsp, h8, hrd, hwr, ko, io, ot, oa, sk, si, so, st, sa, nk, ni, no, nt, ol, tm, td, tb, tok⟩

/-! ## What the code keeps -/

/-- The registers the prologue sets that the code keeps from then on. -/
abbrev kregs : List Reg := [.r4, .r5, .r6, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

theorem eSaved_slots : Spill.Slots 0 36 eSaved := by decide

/-- What the code writes from the prologue on: the stack (the 32 bytes the
calls use, and the frame after the save area) and `out`. -/
def Wk (s : State) (r : Region) : Prop :=
  Region.Sub r ⟨B s, 32⟩ ∨ Region.Sub r ⟨B s + BitVec.ofNat 64 72, eFr - 40⟩ ∨ Region.Sub r (outR s)

/-- The registers and memory kept from the end of the prologue on. -/
structure ER (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr
  sp : t.sp = fb s
  sy : t.syms = s.syms
  r4 : t.gpr .r4 = s.gpr .r0
  r5 : t.gpr .r5 = s.gpr .r1
  r6 : t.gpr .r6 = s.gpr .r2
  r11 : t.gpr .r11 = stackArg s 1
  saved : Spill.Saved t.mem (State.addr (fb s)) s.gpr eSaved
  frame : Frame [stkR s, outR s] s.mem t.mem

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

theorem fA_eq {o : Nat} (ho : o ≤ eFr) : State.addr (fb s + BitVec.ofNat 32 o) = fA s o := hp.st.fo ho

omit hp in
/-- A part of the frame, within the stack. -/
theorem fr_sub {o n : Nat} (h : o + n ≤ eFr) : Region.Sub ⟨fA s o, n⟩ (stkR s) :=
  Offset.sub_base _ (by simp only [eStack]; omega_using [h])

theorem fb_addr : State.addr (fb s) = fA s 0 := hp.st.fb

theorem fb_add (d : Nat) : State.addr (fb s) + BitVec.ofNat 64 d = fA s d := by
  rw [fb_addr hp, fA, fA, Offset.add_add, Nat.add_zero]

/-- A part of the frame, in its region. -/
theorem fr_in {t : State} (hwr : t.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr) {o n : Nat} (h : o + n ≤ eFr) :
    InRegions t.wr (fA s o) n :=
  ⟨_, by rw [hwr]; exact List.mem_cons_self .., by
    rw [fb_addr hp]
    have := hp.st.bN; have := s.sp.isLt; have hfr := eFr_eq
    exact Offset.contains _ (by omega_using []) (by omega_using [h]) (by omega_using [h, this, hfr])⟩

theorem fr_in' {t : State} (hwr : t.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr) {o n : Nat} (h : o + n ≤ eFr) :
    InRegions (t.rd ++ t.wr) (fA s o) n :=
  let ⟨r, hr, hc⟩ := fr_in hp hwr h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A part of the frame, among the writable regions. -/
theorem fr_cov {t : State} (hwr : t.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr) {o n : Nat} (h : o + n ≤ eFr) :
    ∃ r' ∈ t.wr, ∃ off, fA s o = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨_, by rw [hwr]; exact List.mem_cons_self .., o, (fb_add hp o).symm, h⟩

/-- Two parts of the frame apart. -/
theorem fr_disj {o n o' n' : Nat} (h₁ : o + n ≤ o' ∨ o' + n' ≤ o) (h₂ : o + n ≤ eFr) (h₃ : o' + n' ≤ eFr) :
    Region.Disjoint ⟨fA s o, n⟩ ⟨fA s o', n'⟩ := by
  have hfr := eFr_eq
  exact hp.st.disj (.imp (fun h => by omega_using [h]) (fun h => by omega_using [h]) h₁) (by omega_using [h₂, hfr])
    (by omega_using [h₃, hfr])

/-- An offset in the frame, as a number. -/
theorem fbN {o : Nat} (ho : o ≤ eFr) : (fb s + BitVec.ofNat 32 o).toNat = (fb s).toNat + o := hp.st.foN ho

theorem fbN' : (fb s).toNat + eFr ≤ 2 ^ 32 := by
  have h1 : (fb s).toNat + eFr = s.sp.toNat := hp.st.fbN
  have := s.sp.isLt; omega_using [h1, this]

/-- The save area is apart from what the code writes from the prologue on. -/
theorem wk_saved {r : Region} (h : Wk s r) : Region.Disjoint ⟨State.addr (fb s) + BitVec.ofNat 64 0, 36 - 0⟩ r := by
  have hs : (⟨State.addr (fb s) + BitVec.ofNat 64 0, 36 - 0⟩ : Region) = ⟨B s + BitVec.ofNat 64 32, 36⟩ := by
    rw [fb_addr hp, BitVec.add_zero]
  rw [hs]
  have hfr := eFr_eq
  rcases h with h | h | h
  · exact (Offset.disjoint_base _ (by decide) (by
      have := hp.st.bN; have := s.sp.isLt; omega_using [this])).sub_right h
  · exact (hp.st.disj (.inl (by decide)) (by omega_using [hfr]) (by omega_using [hfr])).sub_right h
  · exact (hp.s_o.sub_left (fr_sub (o := 0) (n := 36) (by omega_using [hfr]))).sub_right h

omit hp in
/-- A part of the frame after the save area. -/
theorem wk_fr {o n : Nat} (h₁ : 40 ≤ o) (h₂ : o + n ≤ eFr) : Wk s ⟨fA s o, n⟩ := by
  have hfr := eFr_eq
  exact .inr (.inl (Offset.sub _ (by omega_using [h₁]) (by omega_using [h₂, hfr])))

/-- What a piece of code leaves keeps `ER`, if it writes only `Wk` regions
and keeps the registers of `kregs`. -/
theorem ER.keep {t t' : State} (h : ER s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hw : ∀ r ∈ ws, Wk s r) : ER s t' := by
  have hfr := eFr_eq
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide)).trans h.r4,
    (hg _ (by decide)).trans h.r5, (hg _ (by decide)).trans h.r6, (hg _ (by decide)).trans h.r11,
    h.saved.frame eSaved_slots hf fun r hr => wk_saved hp (hw r hr), h.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases hw r hr with h | h | h
  · exact ⟨_, List.mem_cons_self .., fun a ha => Region.sub_prefix (by decide) a (h a ha)⟩
  · exact ⟨_, List.mem_cons_self .., fun a ha => Offset.sub_base _ (by simp only [eStack]; omega_using [hfr])
      a (h a ha)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

/-- What writes only a register outside `kregs` keeps `ER`. -/
theorem ER.upd {t t' : State} (h : ER s t) {d : Reg} {v : BitVec 32} (u : Upd t t' d v) (hd : d ∉ kregs) :
    ER s t' :=
  h.keep hp u.rd u.wr u.sp u.syms (fun r hr => u.other r fun e => hd (e ▸ hr)) (ws := [])
    (by rw [u.mem]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

omit hp in
/-- The bytes of a region apart from the stack and `out` are as on entry. -/
theorem ER.bytes {t : State} (h : ER s t) {p : Addr} {n : Nat} (hk : Region.Disjoint ⟨p, n⟩ (stkR s))
    (hq : Region.Disjoint ⟨p, n⟩ (outR s)) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s.mem p n :=
  bytes_keep h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hk, hq]) hn

theorem ER.infoB {t : State} (h : ER s t) : bytesAt t.mem (infoA s) (infoLen s) = infoOf s :=
  h.bytes hp.s_i.symm hp.i_o (Nat.le_of_lt (Nat.lt_trans (s.gpr .r2).isLt (by decide)))

/-- A byte of `key` is as on entry. -/
theorem ER.keyB {t : State} (h : ER s t) {i : Nat} (hi : i < 384) :
    t.mem (keyA s + BitVec.ofNat 64 i) = s.mem (keyA s + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := keyR s) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.s_k.symm, hp.k_o]) (show 384 ≤ 2 ^ 64 by decide) hi

/-- A word of the table is as on entry. -/
theorem ER.tabW {t : State} (h : ER s t) {o : Nat} (ho : o + 4 ≤ 24) :
    t.mem.readW (tA (stackArg s 1) o) 32 = s.mem.readW (tA (stackArg s 1) o) 32 := by
  have hn := hp.nt
  have ha : tA (stackArg s 1) o = State.addr (stackArg s 1) + BitVec.ofNat 64 o :=
    VG.Arm.addr_add (by omega_using [hn, ho])
  rw [ha]
  exact h.frame.readW (r := tabR s) (Offset.contains_base _ ho (by omega_using [ho])) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.s_t.symm, hp.o_t.symm]) (by decide)

theorem tin {t : State} (h : ER s t) {o : Nat} (ho : o + 4 ≤ 24) :
    InRegions (t.rd ++ t.wr) (tA (stackArg s 1) o) 4 := by
  have hn := hp.nt
  have ha : tA (stackArg s 1) o = State.addr (stackArg s 1) + BitVec.ofNat 64 o :=
    VG.Arm.addr_add (by omega_using [hn, ho])
  rw [ha]
  exact ⟨tabR s, List.mem_append_left _ (by rw [h.rd, hp.rd]; simp), Offset.contains_base _ ho (by omega_using [ho])⟩

/-- The table's function `j`, through the table in `r11`. -/
theorem tabFn {t : State} (h : ER s t) {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hw : s.mem.readW (tA (stackArg s 1) (4 * j)) 32 = s.syms n)
    (hf : ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.syms n).setWidth 64) = some (n, c)) :
    TabFn t .r11 j n c ts := by
  refine ⟨by omega_using [hj], ?_, ?_, ?_⟩
  · rw [h.r11]; exact tin hp h (by omega_using [hj])
  · rw [h.r11, h.sy]; exact (h.tabW hp (by omega_using [hj])).trans hw
  · rw [h.sy]; exact hf

/-- The 32, 24 and 16 bytes below the frame, from a stack pointer at the frame's base. -/
theorem below32 {t : State} (ht : t.sp = fb s) :
    (⟨State.addr t.sp - BitVec.ofNat 64 32, 32⟩ : Region) = ⟨B s, 32⟩ := by
  rw [ht, hp.st.below32]

theorem stk24 {t : State} (ht : t.sp = fb s) : Proof.Pbkdf2.Whole.Arm.stk t = ⟨B s + BitVec.ofNat 64 8, 24⟩ := by
  show (⟨State.addr t.sp - 24, 24⟩ : Region) = _
  rw [ht, hp.st.stk24]

theorem stk24_wk {t : State} (ht : t.sp = fb s) : Wk s (Proof.Pbkdf2.Whole.Arm.stk t) := by
  rw [stk24 hp ht]; exact .inl (Offset.sub_base _ (by decide))

theorem stk16 {t : State} (ht : t.sp = fb s) :
    Pbkdf2.Stream.Arm.below t = ⟨B s + BitVec.ofNat 64 16, 16⟩ := by
  show (⟨State.addr t.sp - 16, 16⟩ : Region) = _
  rw [ht, hp.st.stk16]

theorem stk16_wk {t : State} (ht : t.sp = fb s) : Wk s (Pbkdf2.Stream.Arm.below t) := by
  rw [stk16 hp ht]; exact .inl (Offset.sub_base _ (by decide))

end

/-! ## The loop's invariant -/

/-- The length of `T(k)`: none for `T(0)`, `D` after. -/
abbrev pl (w : HVar) (k : Nat) : Nat := if k = 0 then 0 else w.F.H.D

/-- The bytes of `out` written after `k` blocks. -/
abbrev done (w : HVar) (s : State) (k : Nat) : Nat := min (k * w.F.H.D) (outLen s)

/-- Before block `k + 1`: the registers and memory kept, `out`'s first
`done` bytes, `T(k)` in the frame, the counter and the length of `T(k)` in
the frame, and the registers that count, with `Z` set iff no bytes of `out`
are left. -/
structure EI (w : HVar) (s : State) (k : Nat) (t : State) : Prop where
  er : ER s t
  r8 : t.gpr .r8 = s.gpr .r3 + BitVec.ofNat 32 (done w s k)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (outLen s - done w s k)
  z : t.z = (BitVec.ofNat 32 (outLen s - done w s k) == 0)
  c : t.mem.readW (fA s eC) 32 = BitVec.ofNat 32 (k + 1)
  l : t.mem.readW (fA s eL) 32 = BitVec.ofNat 32 (pl w k)
  ob : ∀ prk, Keyd w s prk → bytesAt t.mem (outA s) (done w s k) =
    (Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf s) k [] 1).take (done w s k)
  tb : ∀ prk, Keyd w s prk → bytesAt t.mem (fA s eT) (pl w k) = Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k

/-! ## The prologue -/

theorem pro_eq : expandPro = .addSp .r12 0 :: (eSaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .mov .r8 (.reg .r3), .ldr .r9 .r12 eFr,
      .ldr .r11 .r12 (eFr + 4), .mov .r0 (Impl.AesGcm.Arm.imm 1), .str .r0 .r12 eC, .mov .r0 (Impl.AesGcm.Arm.imm 0),
      .str .r0 .r12 eL, .cmp .r9 (Impl.AesGcm.Arm.imm 0)] : List Instr)) := rfl

theorem argAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem fb_eFr (s : State) : fb s + BitVec.ofNat 32 eFr = s.sp := BitVec.sub_add_cancel _ _

theorem fb_eFr4 (s : State) : fb s + BitVec.ofNat 32 (eFr + 4) = s.sp + BitVec.ofNat 32 (4 * 1) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, fb_eFr]

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

omit hp in
/-- A word at `a` is within the four bytes at `a`. -/
theorem cself (a : Addr) : (⟨a, 4⟩ : Region).Contains a (32 / 8) := Region.contains_self a 4

omit hp in
/-- A part of the frame, in the stack. -/
theorem fr_con {o n : Nat} (h : o + n ≤ eFr) : (stkR s).Contains (fA s o) n :=
  Offset.contains_base _ (by simp only [eStack]; omega_using [h]) (by have := eFr_eq; omega_using [h, this])

/-- The save area, as `Spill` states it, in the stack. -/
theorem saved_sub : Region.Sub ⟨State.addr (fb s) + BitVec.ofNat 64 0, 36 - 0⟩ (stkR s) := by
  rw [fb_add hp]; exact fr_sub (by decide)

theorem pro_ok : WP isa (.block expandPro) (allocated eFr s) (EI w s 0) := by
  have hfr := eFr_eq
  apply WP.of_syms
  rw [pro_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, BitVec.add_zero]; rfl
  refine Spill.saveList_ok eSaved t₁ _ (fun p hp' => by
      have hb := eSaved_slots.bound hp'
      have h1 : (fb s).toNat + eFr = s.sp.toNat := hp.st.fbN
      have h2 := s.sp.isLt
      refine ⟨by omega_using [hb], by rw [h12]; omega_using [hb, h1, h2, hfr], ?_⟩
      rw [h12, fb_add hp, u₁.wr]; exact fr_in hp rfl (by omega_using [hb, hfr]))
    fun t₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hsm : Spill.saveMem t₁.mem (State.addr (t₁.gpr .r12)) t₁.gpr eSaved =
      Spill.saveMem s.mem (State.addr (fb s)) s.gpr eSaved := by
    rw [h12, u₁.mem]
    exact Spill.saveMem_congr _ _ _ fun p hp' => by
      rw [u₁.other _ (by revert p; decide)]; rfl
  have hsa : ∀ (i : Nat), i < 2 → (Spill.saveMem s.mem (State.addr (fb s)) s.gpr eSaved).readW (stackArgAddr s i) 32 =
      stackArg s i := fun i hi => by
    have hc : (argR s).Contains (stackArgAddr s i) (32 / 8) := by
      have := hp.sp8
      rw [stackArgAddr, VG.Arm.addr_add (by omega_using [this, hi])]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    exact (Spill.saveMem_frame_slots eSaved_slots _ _ _).readW hc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.s_a.symm.sub_right (saved_sub hp)) (by decide)
  refine wp_movr fun t₃ u₃ => wp_movr fun t₄ u₄ => wp_movr fun t₅ u₅ => wp_movr fun t₆ u₆ => ?_
  have r12₆ : t₆.gpr .r12 = fb s := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂]; exact h12
  have rd₆ : t₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂]; exact u₁.rd
  have wr₆ : t₆.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr := by
    rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]; rfl
  have m₆ : t₆.mem = Spill.saveMem s.mem (State.addr (fb s)) s.gpr eSaved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]; exact hsm
  have ina : ∀ (i : Nat), i < 2 → InRegions (t₆.rd ++ t₆.wr) (stackArgAddr s i) 4 := fun i hi => by
    have := hp.sp8
    refine ⟨argR s, List.mem_append_left _ (by rw [rd₆, hp.rd]; simp), ?_⟩
    rw [stackArgAddr, VG.Arm.addr_add (by omega_using [this, hi])]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine wp_ldr (a := stackArgAddr s 0) (by decide) (by rw [r12₆, fb_eFr, argAddr0]) (ina 0 (by decide))
    fun t₇ u₇ => ?_
  refine wp_ldr (a := stackArgAddr s 1) (by decide) (by rw [u₇.other _ (by decide), r12₆, fb_eFr4]; rfl)
    (by rw [u₇.rd, u₇.wr]; exact ina 1 (by decide)) fun t₈ u₈ => ?_
  have r12₈ : t₈.gpr .r12 = fb s := by rw [u₈.other _ (by decide), u₇.other _ (by decide)]; exact r12₆
  have wr₈ : t₈.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr := by rw [u₈.wr, u₇.wr]; exact wr₆
  refine wp_movi (by decide) fun t₉ u₉ => ?_
  refine wp_str (a := fA s eC) (by decide) (by rw [u₉.other _ (by decide), r12₈]; exact fA_eq hp (by decide))
    (fr_in hp (t := t₉) (by rw [u₉.wr, wr₈]) (o := eC) (n := 4) (by decide)) fun t₁₀ u₁₀ => ?_
  refine wp_movi (by decide) fun t₁₁ u₁₁ => ?_
  refine wp_str (a := fA s eL) (by decide)
    (by rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), r12₈]; exact fA_eq hp (by decide))
    (fr_in hp (t := t₁₁) (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, wr₈]) (o := eL) (n := 4) (by decide)) fun t₁₂ u₁₂ => ?_
  refine wp_cmpi (by decide) fun t₁₃ g₁₃ f₁₃ => WP.block_nil fun sy => ?_
  -- The memory: the save area, then the counter's word and the length's.
  have hc1 : t₁₀.mem = (Spill.saveMem s.mem (State.addr (fb s)) s.gpr eSaved).writeW (fA s eC)
      (BitVec.ofNat 32 1) := by
    rw [u₁₀.mem, u₉.gpr, u₉.mem, u₈.mem, u₇.mem, m₆]
  have hm : t₁₃.mem = ((Spill.saveMem s.mem (State.addr (fb s)) s.gpr eSaved).writeW (fA s eC)
      (BitVec.ofNat 32 1)).writeW (fA s eL) (BitVec.ofNat 32 0) := by
    rw [f₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₁.mem, hc1]
  have hsep : Mem.Sep (fA s eC) (32 / 8) (fA s eL) (32 / 8) :=
    Region.Disjoint.sep (fr_disj hp (o := eC) (n := 4) (o' := eL) (n' := 4) (.inl (by decide)) (by decide) (by decide))
      (Region.contains_self _ _) (Region.contains_self _ _)
  have hfr1 : Frame [stkR s, outR s] s.mem t₁₃.mem := by
    rw [hm]
    refine (((Spill.saveMem_frame_slots eSaved_slots _ _ _).sub fun r hr => ?_).writeW List.mem_cons_self _
      (fr_con (o := eC) (n := 4) (by decide))).writeW List.mem_cons_self _ (fr_con (o := eL) (n := 4) (by decide))
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., saved_sub hp⟩
  have hsv : Spill.Saved t₁₃.mem (State.addr (fb s)) s.gpr eSaved := by
    rw [hm]
    refine (Spill.saveMem_saved (State.addr (fb s)) s.gpr s.mem eSaved eSaved_slots).frame eSaved_slots
      (rs := [⟨fA s eC, 4⟩, ⟨fA s eL, 4⟩]) (((Frame.refl _ _).writeW List.mem_cons_self _ (cself (fA s eC))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (cself (fA s eL))) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact wk_saved hp (wk_fr (by decide) (by decide))
    · exact wk_saved hp (wk_fr (by decide) (by decide))
  have r9₁₂ : t₁₂.gpr .r9 = stackArg s 0 := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, m₆]
    exact hsa 0 (by decide)
  have hd0 : done w s 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  refine ⟨⟨?_, ?_, ?_, sy, ?_, ?_, ?_, ?_, hsv, hfr1⟩, ?_, ?_, ?_, ?_, ?_, fun prk _ => ?_, fun prk _ => ?_⟩
  · rw [f₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆]
  · rw [f₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈]
  · rw [f₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl
  · upd_simp [g₁₃, u₁₂.gpr, u₁₁.other, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other,
      u₃.gpr, g₂, u₁.other]; rfl
  · upd_simp [g₁₃, u₁₂.gpr, u₁₁.other, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr,
      u₃.other, g₂, u₁.other]; rfl
  · upd_simp [g₁₃, u₁₂.gpr, u₁₁.other, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other,
      u₃.other, g₂, u₁.other]; rfl
  · upd_simp [g₁₃, u₁₂.gpr, u₁₁.other, u₁₀.gpr, u₉.other, u₈.gpr, u₇.mem, m₆]; exact hsa 1 (by decide)
  · upd_simp [g₁₃, u₁₂.gpr, u₁₁.other, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other,
      u₃.other, g₂, u₁.other, hd0, BitVec.add_zero]; rfl
  · rw [g₁₃, r9₁₂, hd0, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [f₁₃.z, r9₁₂, hd0, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact congrArg (· == 0) (BitVec.sub_zero _)
  · rw [hm, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32]
  · rw [hm, Mem.readW_writeW_self32]; rfl
  · rw [hd0]; rfl
  · rfl

end

/-! ## A block -/

theorem hash_length {w : HVar} (hw : HOk w) (m : List Byte) : (w.ok.hH.SH.H.hash m).length = w.F.H.D := hw.macLen m

/-- `T(k)` has `pl k` bytes. -/
theorem tBlock_len {w : HVar} (hw : HOk w) (prk info : List Byte) (k : Nat) :
    (Proof.Hkdf.tBlock w.ok.hH.SH.H prk info k).length = pl w k := by
  cases k with
  | zero => rfl
  | succ k => exact Proof.Hkdf.tBlock_length _ _ _ (hash_length hw) k

theorem pl_le (w : HVar) (k : Nat) : pl w k ≤ w.F.H.D := by unfold pl; split <;> omega_using []

theorem D_le (w : HVar) : w.F.H.D ≤ 64 := by have := w.ok.hH.hDF; have := w.ok.hH.hF; omega_arith

/-- What the code writes in a block but the copy to `out`: the 32 bytes the
calls use, and the frame from `T` on. -/
def WkB (s : State) (r : Region) : Prop :=
  Region.Sub r ⟨B s, 32⟩ ∨ Region.Sub r ⟨fA s eT, eFr - eT⟩

theorem wkB_wk {s : State} {r : Region} (h : WkB s r) : Wk s r := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (.inl fun a ha => Offset.sub (B s) (d := 32 + eT) (e := 72) (by decide) (by decide) a (h a ha))

/-- During block `k + 1`: the registers and memory kept, `out`'s first `k D`
bytes, the counter and the length of `T(k)` in the frame, and the registers
that count. -/
structure BR (w : HVar) (s : State) (k : Nat) (t : State) : Prop where
  er : ER s t
  r8 : t.gpr .r8 = s.gpr .r3 + BitVec.ofNat 32 (k * w.F.H.D)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (outLen s - k * w.F.H.D)
  c : t.mem.readW (fA s eC) 32 = BitVec.ofNat 32 (k + 1)
  l : t.mem.readW (fA s eL) 32 = BitVec.ofNat 32 (pl w k)
  lt : k * w.F.H.D < outLen s
  ob : ∀ prk, Keyd w s prk → bytesAt t.mem (outA s) (k * w.F.H.D) =
    Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf s) k [] 1

/-- `K₀` of a pseudorandom key. -/
abbrev k0 (w : HVar) (prk : List Byte) : List Byte := blockKey w.ok.hH.SH.H prk

/-- The working state represents `K₀ ⊕ ipad`, then `m`, for each
pseudorandom key the states are keyed with. -/
abbrev WS (w : HVar) (s : State) (t : State) (m : List Byte → List Byte) : Prop :=
  ∀ prk, Keyd w s prk → w.ok.hH.SH.Repr t.mem (fA s eW) (xorPad (k0 w prk) ipad ++ m prk)

/-- `T(k)` in the frame, for each pseudorandom key. -/
abbrev TB (w : HVar) (s : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s prk → bytesAt t.mem (fA s eT) (pl w k) = Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k

/-- What the registers of `BR` keep. -/
abbrev bregs : List Reg := [.r4, .r5, .r6, .r8, .r9, .r11]

theorem bregs_pres : ∀ r ∈ bregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

/-- What writes only `WkB` regions and keeps `bregs` keeps `BR`. -/
theorem BR.keep {k : Nat} {t t' : State} (h : BR w s k t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hsy : t'.syms = t.syms) (hg : ∀ r ∈ bregs, t'.gpr r = t.gpr r) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hw : ∀ r ∈ ws, WkB s r) : BR w s k t' := by
  have hfr := eFr_eq
  have het : eT = 48 := rfl
  have hd : ∀ (o : Nat), o + 4 ≤ eT → ∀ r ∈ ws, Region.Disjoint ⟨fA s o, 32 / 8⟩ r := fun o ho r hr => by
    rcases hw r hr with h | h
    · exact (Offset.disjoint_base (B s) (d := 32 + o) (n := 32 / 8) (k := 32) (by omega_using [])
        (by omega_using [ho, het])).sub_right h
    · exact (hp.st.disj (o := 32 + o) (n := 32 / 8) (o' := 32 + eT) (n' := eFr - eT) (.inl (by omega_using [ho]))
        (by omega_using [ho, het, hfr]) (by omega_using [hfr, het])).sub_right h
  refine ⟨h.er.keep hp hrd hwr hsp hsy (fun r hr => hg r (by revert r; decide)) hf fun r hr => wkB_wk (hw r hr),
    (hg _ (by decide)).trans h.r8, (hg _ (by decide)).trans h.r9,
    (hf.readW (Region.contains_self _ _) (hd eC (by decide)) (by decide)).trans h.c,
    (hf.readW (Region.contains_self _ _) (hd eL (by decide)) (by decide)).trans h.l, h.lt, fun prk hK => ?_⟩
  have hol : outLen s < 2 ^ 32 := (stackArg s 0).isLt
  rw [bytes_keep hf (fun r hr => ?_) (by have := h.lt; omega_using [this, hol])]
  · exact h.ob prk hK
  · have hs : Region.Sub ⟨outA s, k * w.F.H.D⟩ (outR s) := Region.sub_prefix (Nat.le_of_lt h.lt)
    rcases hw r hr with h' | h'
    · exact (hp.s_o.symm.sub_left hs).sub_right (fun a ha => Region.sub_prefix (by decide) a (h' a ha))
    · exact (hp.s_o.symm.sub_left hs).sub_right (fun a ha => fr_sub (o := eT) (n := eFr - eT) (by decide) a (h' a ha))

/-! ### The copy of the inner state -/

theorem copyW_ok {k : Nat} {t : State} (h : BR w s k t) :
    WP isa (.block copyW) t fun u => BR w s k u ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → u.gpr r = t.gpr r) ∧
      u.mem = t.mem ∧ u.gpr .r1 = s.gpr .r0 ∧ u.gpr .r2 = fb s + BitVec.ofNat 32 eW ∧
      u.gpr .r3 = BitVec.ofNat 32 192 := by
  unfold copyW
  refine wp_addSp (by decide) fun t₁ u₁ => wp_movr fun t₂ u₂ => wp_addi (by decide) fun t₃ u₃ =>
    wp_movi (by decide) fun t₄ u₄ => WP.block_nil ?_
  have hg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t₄.gpr r = t.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h4]
  have hm : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms])
      (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide))
      (ws := []) (by rw [hm]; exact Frame.refl _ _) (fun _ h => absurd h List.not_mem_nil), hg, hm, ?_, ?_, ?_⟩
  · upd_simp [u₄.other, u₃.other, u₂.gpr, u₁.other, h.er.r4]
  · upd_simp [u₄.other, u₃.gpr, u₂.other, u₁.gpr, h.er.sp, BitVec.add_zero]
  · upd_simp [u₄.gpr]

omit hp in
theorem bytesAt_take (m : Mem) (p : Addr) {n N : Nat} (h : n ≤ N) :
    bytesAt m p n = (bytesAt m p N).take n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (Proof.Hmac.Common.bytesAt_length _ _ _)]

omit hp in
theorem aes_bytes (m : Mem) (p : Addr) (n : Nat) : Spec.Aes.bytesAt m p n = bytesAt m p n := rfl

theorem copy_ok (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t) (ht : TB w s k t) :
    WP isa (.seq (.block copyW) Impl.AesGcm.Arm.copyLoop) t fun u =>
      BR w s k u ∧ TB w s k u ∧ WS w s u (fun _ => []) := by
  have hfr := eFr_eq; have hfN := fbN' hp
  refine WP.seq (WP.mono (copyW_ok hp h) fun t₁ ⟨b₁, g₁, m₁, h1, h2, h3⟩ => ?_)
  have eW' := fA_eq hp (o := eW) (by decide)
  have pre : Proof.AesGcm.Arm.LoopPre t₁ (s.gpr .r0) (fb s + BitVec.ofNat 32 eW) 192 :=
    { r1 := h1, r2 := h2, r3 := h3, pos := by decide, lt := by decide
      fitS := by have := hp.nk; omega_using [this]
      fitD := by rw [fbN hp (by decide)]; have heW : eW = 112 := rfl; omega_using [hfN, hfr, heW]
      rd := VG.Covers.left (VG.Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨keyR s, by rw [b₁.er.rd, hp.rd]; exact List.mem_cons_self .., 0, (BitVec.add_zero _).symm,
          show 0 + 192 ≤ 384 by decide⟩)
      wr := VG.Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [eW']; exact fr_cov hp b₁.er.wr (o := eW) (n := 192) (by decide)
      disj := by
        rw [eW']; exact (hp.s_k.symm.sub_left (Region.sub_prefix (by decide))).sub_right (fr_sub (by decide)) }
  refine WP.mono_syms (Proof.AesGcm.Arm.copyLoop_ok t₁ pre) fun u ⟨hm, lo⟩ sy => ?_
  rw [eW', aes_bytes] at hm
  have hl : (bytesAt t₁.mem (keyA s) 192).length = 192 := Proof.Hmac.Common.bytesAt_length _ _ _
  have F : Frame [⟨fA s eW, 192⟩] t₁.mem u.mem := by
    rw [hm]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have hWw : WkB s ⟨fA s eW, 192⟩ := .inr (Offset.sub _ (by decide) (by decide))
  refine ⟨b₁.keep hp lo.rd lo.wr lo.sp sy (fun r hr => lo.other r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)) F
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hWw), fun prk hK => ?_,
    fun prk hK => ?_⟩
  · have hpl := pl_le w k; have hD := D_le w
    rw [bytes_keep F (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact fr_disj hp (.inl (by simp only [eT, eW]; omega_using [hpl, hD])) (by simp only [eT]; omega_using [hpl, hD, hfr])
          (by decide))
      (by omega_using [hpl, hD]), m₁]
    exact ht prk hK
  · rw [List.append_nil]
    refine w.ok.hH.repr s.mem u.mem (keyA s) (fA s eW) _ (fun i hi => ?_) hK.1
    have hS := hw.hS
    rw [hm, Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [hl]; omega_using [hi, hS]) (by rw [hl]; decide),
      Proof.Hmac.Common.bytesAt_getD' _ _ (by omega_using [hi, hS]), m₁]
    exact h.er.keyB hp (by omega_using [hi, hS])

/-! ### The calls of `update` -/

/-- `info` fits HMAC's count with a block of key, `T(i - 1)` and the counter. -/
theorem info_lt : w.F.H.B + w.F.H.D + infoLen s + 1 < 2 ^ 32 := by
  have h := Proof.Pbkdf2.Whole.len_add_le hp.s_i (N := 2 ^ 32) (by
      show (B s).toNat + eStack ≤ 2 ^ 32
      have h1 := hp.st.bN; have h2 := s.sp.isLt; have hx : eStack = eFr + 32 := rfl
      omega_using [h1, h2, hx])
    (by show (State.addr (s.gpr .r1)).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32; rw [toNat_addr]; exact hp.ni)
  have hB := w.ok.hH.hBB
  have hD := D_le w
  have h' : eStack + infoLen s ≤ 2 ^ 32 := h
  have hx := eStack_eq
  omega_using [h', hB, hD, hx]

end

/-- What `update`'s arguments are, for `len` bytes at `dat`, after a text of
`ml` bytes. -/
structure UA (w : HVar) (s : State) (dat : BitVec 32) (len ml : Nat) (t : State) : Prop where
  r0 : t.gpr .r0 = fb s + BitVec.ofNat 32 eW
  r1 : t.gpr .r1 = dat
  r2 : t.gpr .r2 = BitVec.ofNat 32 (w.F.H.B + ml)
  r3 : t.gpr .r3 = 0
  r7 : t.gpr .r7 = BitVec.ofNat 32 len
  r10 : t.gpr .r10 = fb s + BitVec.ofNat 32 eWork
  hlen : len < 2 ^ 32
  cd : Covers [⟨State.addr dat, len⟩] (t.rd ++ t.wr)
  d_w : Region.Disjoint ⟨State.addr dat, len⟩ ⟨fA s eW, 192⟩
  d_s : Region.Disjoint ⟨State.addr dat, len⟩ ⟨fA s eWork, 1872⟩
  d_b : Region.Disjoint ⟨B s + BitVec.ofNat 64 16, 16⟩ ⟨State.addr dat, len⟩
  nd : dat.toNat + len ≤ 2 ^ 32
  hml : w.F.H.B + ml < 2 ^ 32

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

/-- `update`'s arguments, after the load of its address. -/
theorem upd_args (hw : HOk w) {t u : State} (k₀ : ER s t) {ml : Nat} {dat : BitVec 32} {len : Nat}
    (ha : UA w s dat len ml t) {v : BitVec 32} (hu : Upd t u .lr v) :
    Proof.Pbkdf2.Whole.Arm.UpdL w.ok.hH u (fb s + BitVec.ofNat 32 eW) dat (fb s + BitVec.ofNat 32 eWork) len := by
  have hfr := eFr_eq; have hS := hw.hS; have hWb := hw.hWb; have hfN := fbN' hp
  have heW : eW = 112 := rfl; have heWk : eWork = 304 := rfl
  have hb : Pbkdf2.Stream.Arm.below u = ⟨B s + BitVec.ofNat 64 16, 16⟩ := stk16 hp (by rw [hu.sp, k₀.sp])
  have e0 := fA_eq hp (o := eW) (by decide)
  have e3 := fA_eq hp (o := eWork) (by decide)
  have sW : Region.Sub ⟨fA s eW, w.F.H.S⟩ ⟨fA s eW, 192⟩ := Region.sub_prefix hS
  have sS : Region.Sub ⟨fA s eWork, w.ok.hH.Wb⟩ ⟨fA s eWork, 1872⟩ := Region.sub_prefix hWb
  exact
  { r0 := by rw [hu.other _ (by decide)]; exact ha.r0
    r1 := by rw [hu.other _ (by decide)]; exact ha.r1
    r7 := by rw [hu.other _ (by decide)]; exact ha.r7
    r10 := by rw [hu.other _ (by decide)]; exact ha.r10
    hlen := ha.hlen
    sp16 := by
      rw [hu.sp, k₀.sp]; have h1 : (fb s).toNat + eFr = s.sp.toNat := hp.st.fbN; have := hp.sp
      simp only [eStack] at this; omega_using [h1, this]
    cd := by rw [hu.rd, hu.wr]; exact ha.cd
    cw := by
      refine VG.Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e0]; exact fr_cov hp (by rw [hu.wr]; exact k₀.wr) (o := eW) (n := w.F.H.S) (by omega_using [hS, hfr, heW])
      · rw [e3]; exact fr_cov hp (by rw [hu.wr]; exact k₀.wr) (o := eWork) (n := w.ok.hH.Wb)
          (by omega_using [hWb, hfr, heWk])
    st_sc := by rw [e0, e3]; exact fr_disj hp (.inl (by omega_using [hS, heW, heWk])) (by omega_using [hS, hfr, heW])
                  (by omega_using [hWb, hfr, heWk])
    d_st := by rw [e0]; exact ha.d_w.sub_right sW
    d_sc := by rw [e3]; exact ha.d_s.sub_right sS
    b_st := by rw [hb, e0]; exact (hp.st.disj (.inl (by omega_using [heW])) (by decide)
                  (by omega_using [hfr, heW])).sub_right sW
    b_d := by rw [hb]; exact ha.d_b
    b_sc := by rw [hb, e3]; exact (hp.st.disj (.inl (by omega_using [heWk])) (by decide)
                  (by omega_using [hfr, heWk])).sub_right sS
    nst := by rw [fbN hp (by decide)]; omega_using [hS, hfr, hfN, heW]
    nd := ha.nd
    nsc := by rw [fbN hp (by decide)]; omega_using [hWb, hfr, hfN, heWk] }

theorem upd_step (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t) (ht : TB w s k t)
    {m : List Byte → List Byte} {ml : Nat} (hm : WS w s t m) (hml : ∀ prk, Keyd w s prk → (m prk).length = ml)
    {dat : BitVec 32} {len : Nat} (ha : UA w s dat len ml t) :
    WP isa (callUpd .r11 f) t fun u => BR w s k u ∧ TB w s k u ∧
      WS w s u (fun prk => m prk ++ bytesAt t.mem (State.addr dat) len) := by
  have hfr := eFr_eq; have hS := hw.hS; have hWb := hw.hWb; have hfN := fbN' hp
  have heW : eW = 112 := rfl; have heWk : eWork = 304 := rfl; have heT : eT = 48 := rfl
  refine tcall_ok (n := w.F.H.updN) (c := w.F.H.updC) (tabFn hp h.er (j := 1) (by decide) hp.tm.2.1 hp.tok.u)
    fun u hu => ?_
  have hb : Pbkdf2.Stream.Arm.below u = ⟨B s + BitVec.ofNat 64 16, 16⟩ := stk16 hp (by rw [hu.sp, h.er.sp])
  have e0 := fA_eq hp (o := eW) (by decide)
  have e3 := fA_eq hp (o := eWork) (by decide)
  apply WP.of_syms
  refine Proof.Pbkdf2.Whole.Arm.upd_frame w.ok.hH (s := u) (upd_args hp hw h.er ha hu) fun s' af hr sy => ?_
  have hws : ∀ r ∈ [(⟨State.addr (fb s + BitVec.ofNat 32 eW), w.F.H.S⟩ : Region),
      ⟨State.addr (fb s + BitVec.ofNat 32 eWork), w.ok.hH.Wb⟩] ++ [Pbkdf2.Stream.Arm.below u], WkB s r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e0]; exact .inr (Offset.sub _ (by omega_using [heW, heT]) (by omega_using [hS, hfr, heW, heT]))
    · rw [e3]; exact .inr (Offset.sub _ (by omega_using [heWk, heT]) (by omega_using [hWb, hfr, heWk, heT]))
    · rw [hb]; exact .inl (Offset.sub_base _ (by decide))
  have hu₁ : BR w s k u := h.keep hp hu.rd hu.wr hu.sp hu.syms (fun r hr => hu.other r (by revert r; decide))
    (ws := []) (by rw [hu.mem]; exact Frame.refl _ _) (fun _ h => absurd h List.not_mem_nil)
  refine ⟨hu₁.keep hp af.rd af.wr af.sp sy (fun r hr => af.cs r (bregs_pres r hr).1 (bregs_pres r hr).2) af.frame hws,
    fun prk hK => ?_, fun prk hK => ?_⟩
  · have hpl := pl_le w k; have hD := D_le w
    rw [bytes_keep af.frame (fun r hr => ?_) (by omega_using [hpl, hD]), hu.mem]
    · exact ht prk hK
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e0]; exact fr_disj hp (.inl (by omega_using [hpl, hD, heW, heT])) (by omega_using [hpl, hD, hfr, heT])
          (by omega_using [hS, hfr, heW])
      · rw [e3]; exact fr_disj hp (.inl (by omega_using [hpl, hD, heWk, heT])) (by omega_using [hpl, hD, hfr, heT])
          (by omega_using [hWb, hfr, heWk])
      · rw [hb]; exact (hp.st.disj (.inl (by omega_using [heT])) (by decide) (by omega_using [hpl, hD, hfr, heT])).symm
  · have hl : (xorPad (k0 w prk) ipad ++ m prk).length = w.F.H.B + ml := by
      rw [List.length_append, Proof.Hmac.Common.xorPad_length, blockKey_len hw, hml prk hK]
    have := hr (xorPad (k0 w prk) ipad ++ m prk) (by rw [hu.mem, e0]; exact hm prk hK) (by
      rw [Pbkdf2.Stream.Arm.count, hu.other _ (by decide), hu.other _ (by decide), ha.r3, ha.r2, hl]
      exact append_zero ha.hml)
    rw [e0, hu.mem, List.append_assoc] at this
    exact this

/-- What leaves the memory and `bregs` as they were keeps `BR`. -/
theorem BR.same {k : Nat} {t t' : State} (h : BR w s k t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hsy : t'.syms = t.syms) (hg : ∀ r ∈ bregs, t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) :
    BR w s k t' :=
  h.keep hp hrd hwr hsp hsy hg (ws := []) (by rw [hm]; exact Frame.refl _ _) (fun _ h => absurd h List.not_mem_nil)

/-- A part of the frame, as `update`'s data. -/
theorem ua_fr {t : State} (k : ER s t) {o n : Nat} (h₂ : o + n ≤ eW) :
    Covers [⟨State.addr (fb s + BitVec.ofNat 32 o), n⟩] (t.rd ++ t.wr) ∧
      Region.Disjoint ⟨State.addr (fb s + BitVec.ofNat 32 o), n⟩ ⟨fA s eW, 192⟩ ∧
      Region.Disjoint ⟨State.addr (fb s + BitVec.ofNat 32 o), n⟩ ⟨fA s eWork, 1872⟩ ∧
      Region.Disjoint ⟨B s + BitVec.ofNat 64 16, 16⟩ ⟨State.addr (fb s + BitVec.ofNat 32 o), n⟩ ∧
      (fb s + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  have hfr := eFr_eq; have heW : eW = 112 := rfl; have heWk : eWork = 304 := rfl; have heT : eT = 48 := rfl
  have hfN := fbN' hp
  have e := fA_eq hp (o := o) (by omega_using [h₂, heW, hfr])
  rw [e]
  refine ⟨VG.Covers.right (VG.Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fr_cov hp k.wr (o := o) (n := n) (by omega_using [h₂, heW, hfr])),
    fr_disj hp (.inl h₂) (by omega_using [h₂, heW, hfr]) (by omega_using [heW, hfr]),
    fr_disj hp (.inl (by omega_using [h₂, heW, heWk])) (by omega_using [h₂, heW, hfr]) (by omega_using [heWk, hfr]),
    hp.st.disj (.inl (by omega_using [])) (by decide) (by omega_using [h₂, heW, hfr]), ?_⟩
  rw [fbN hp (by omega_using [h₂, heW, hfr])]; omega_using [h₂, heW, hfr, hfN]

/-- `update`'s arguments for `T(k)`. -/
theorem argsT_ok {k : Nat} {t : State} (h : BR w s k t) {P : State → Prop}
    (hP : ∀ u, u.mem = t.mem → P u) :
    WP isa (.block updT) t fun u => BR w s k u ∧ P u ∧ UA w s (fb s + BitVec.ofNat 32 eT) (pl w k) 0 u := by
  have k₀ := h.er
  unfold updT
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ => wp_addi (by decide) fun t₃ u₃ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k₀.sp, BitVec.add_zero]
  have e₃ : State.addr (t₃.gpr .r12 + BitVec.ofNat 32 eL) = fA s eL := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), h12]; exact fA_eq hp (by decide)
  refine wp_ldr (a := fA s eL) (by decide) e₃
    (fr_in' hp (by rw [u₃.wr, u₂.wr, u₁.wr]; exact k₀.wr) (by decide)) fun t₄ u₄ => ?_
  refine wp_ldr (a := tA (stackArg s 1) tB) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), k₀.r11])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact tin hp k₀ (by decide)) fun t₅ u₅ => ?_
  refine wp_movi (by decide) fun t₆ u₆ => wp_addi (by decide) fun t₇ u₇ => WP.block_nil ?_
  have hm : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ua := ua_fr hp k₀ (o := eT) (n := pl w k) (by
    have h1 := pl_le w k; have h2 := D_le w; have h3 : eT = 48 := rfl; have h4 : eW = 112 := rfl
    omega_using [h1, h2, h3, h4])
  have hD := D_le w; have hpl := pl_le w k; have hB := w.ok.hH.hBB
  have cd₇ : Covers [⟨State.addr (fb s + BitVec.ofNat 32 eT), pl w k⟩] (t₇.rd ++ t₇.wr) := by
    rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    exact ua.1
  refine ⟨h.same hp (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
      (by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms])
      (fun r hr => by
        simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals upd_simp [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]) hm,
    hP _ hm, ?_, ?_, ?_, ?_, ?_, ?_, (by omega_using [hpl, hD]), cd₇, ua.2.1, ua.2.2.1, ua.2.2.2.1,
    ua.2.2.2.2, (by omega_using [hB])⟩
  · upd_simp [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, h12]
  · upd_simp [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, h12]
  · upd_simp [u₇.other, u₆.other, u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, Nat.add_zero]
    rw [k₀.tabW hp (by decide), hp.tB]
  · upd_simp [u₇.other, u₆.gpr]; rfl
  · upd_simp [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.mem, u₂.mem, u₁.mem]; exact h.l
  · upd_simp [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, h12]

/-- `update`'s arguments for `info`. -/
theorem argsI_ok {k : Nat} {t : State} (h : BR w s k t) {P : State → Prop} (hP : ∀ u, u.mem = t.mem → P u) :
    WP isa (.block updI) t fun u => BR w s k u ∧ P u ∧ UA w s (s.gpr .r1) (infoLen s) (pl w k) u := by
  have k₀ := h.er
  unfold updI
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ => wp_movr fun t₃ u₃ =>
    wp_movr fun t₄ u₄ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k₀.sp, BitVec.add_zero]
  refine wp_ldr (a := tA (stackArg s 1) tB) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), k₀.r11])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact tin hp k₀ (by decide)) fun t₅ u₅ => ?_
  refine wp_ldr (a := fA s eL) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h12]
        exact fA_eq hp (by decide))
    (fr_in' hp (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact k₀.wr) (by decide)) fun t₆ u₆ => ?_
  refine wp_addr fun t₇ u₇ => wp_movi (by decide) fun t₈ u₈ => wp_addi (by decide) fun t₉ u₉ => WP.block_nil ?_
  have hm : t₉.mem = t.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hD := D_le w; have hpl := pl_le w k; have hB := w.ok.hH.hBB
  have hil := info_lt hp (w := w)
  have hfr := eFr_eq; have heW : eW = 112 := rfl; have heWk : eWork = 304 := rfl
  have sbs : Region.Sub ⟨B s + BitVec.ofNat 64 16, 16⟩ (stkR s) := Offset.sub_base _ (by decide)
  have cd₉ : Covers [⟨State.addr (s.gpr .r1), infoLen s⟩] (t₉.rd ++ t₉.wr) := by
    rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd,
      u₂.wr, u₁.rd, u₁.wr, k₀.rd, hp.rd]
    exact VG.Covers.left (VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
  refine ⟨h.same hp (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
      (by rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms])
      (fun r hr => by
        simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          u₁.other]) hm,
    hP _ hm, ?_, ?_, ?_, ?_, ?_, ?_, (s.gpr .r2).isLt, cd₉,
    (hp.s_i.symm.sub_right (fr_sub (o := eW) (n := 192) (by omega_using [heW, hfr]))),
    (hp.s_i.symm.sub_right (fr_sub (o := eWork) (n := 1872) (by omega_using [heWk, hfr]))),
    hp.s_i.sub_left sbs, hp.ni, (by omega_using [hB, hpl, hD, hil])⟩
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, h12]
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, k₀.r5]
  · upd_simp [u₉.other, u₈.other, u₇.gpr, u₆.gpr, u₆.other, u₅.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rw [k₀.tabW hp (by decide), hp.tB, h.l, BitVec.ofNat_add]
  · upd_simp [u₉.other, u₈.gpr]; rfl
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, k₀.r6]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · upd_simp [u₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, h12]

/-- `update`'s arguments for the counter. -/
theorem argsC_ok {k : Nat} {t : State} (h : BR w s k t) {P : State → Prop} (hP : ∀ u, u.mem = t.mem → P u) :
    WP isa (.block updC) t fun u => BR w s k u ∧ P u ∧
      UA w s (fb s + BitVec.ofNat 32 eC) 1 (pl w k + infoLen s) u := by
  have k₀ := h.er
  unfold updC
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ => wp_addi (by decide) fun t₃ u₃ =>
    wp_movi (by decide) fun t₄ u₄ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k₀.sp, BitVec.add_zero]
  refine wp_ldr (a := tA (stackArg s 1) tB) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), k₀.r11])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact tin hp k₀ (by decide)) fun t₅ u₅ => ?_
  refine wp_ldr (a := fA s eL) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h12]
        exact fA_eq hp (by decide))
    (fr_in' hp (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact k₀.wr) (by decide)) fun t₆ u₆ => ?_
  refine wp_addr fun t₇ u₇ => wp_addr fun t₈ u₈ => wp_movi (by decide) fun t₉ u₉ =>
    wp_addi (by decide) fun t₁₀ u₁₀ => WP.block_nil ?_
  have hm : t₁₀.mem = t.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hD := D_le w; have hpl := pl_le w k; have hB := w.ok.hH.hBB
  have hil := info_lt hp (w := w)
  have ua := ua_fr hp k₀ (o := eC) (n := 1) (by decide)
  have cd₁₀ : Covers [⟨State.addr (fb s + BitVec.ofNat 32 eC), 1⟩] (t₁₀.rd ++ t₁₀.wr) := by
    rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd,
      u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    exact ua.1
  refine ⟨h.same hp (by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
      (by rw [u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms])
      (fun r hr => by
        simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals upd_simp [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
          u₂.other, u₁.other]) hm,
    hP _ hm, ?_, ?_, ?_, ?_, ?_, ?_, (by decide), cd₁₀, ua.2.1, ua.2.2.1, ua.2.2.2.1, ua.2.2.2.2,
    (by omega_using [hB, hpl, hD, hil])⟩
  · upd_simp [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, h12]
  · upd_simp [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, h12]
  · upd_simp [u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₅.mem, u₄.mem,
      u₃.mem, u₂.mem, u₁.mem, u₄.other, u₃.other, u₂.other, u₁.other, k₀.r6]
    rw [k₀.tabW hp (by decide), hp.tB, h.l,
      show s.gpr .r2 = BitVec.ofNat 32 (infoLen s) by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.add_assoc]
  · upd_simp [u₁₀.other, u₉.gpr]; rfl
  · upd_simp [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr]
  · upd_simp [u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, h12]

omit hp in
/-- The counter's byte, the low byte of its word. -/
theorem ctr_byte {m : Mem} {a : Addr} {k : Nat} (h : m.readW a 32 = BitVec.ofNat 32 (k + 1)) :
    bytesAt m a 1 = [BitVec.ofNat 8 (k + 1)] := by
  have e := Mem.readW_byte m a (i := 0) (by decide)
  rw [h] at e
  show [m (a + BitVec.ofNat 64 0)] = _
  rw [e]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.reducePow, Nat.shiftRight_zero, Nat.reduceDvd,
    Nat.mod_mod_of_dvd]

theorem stageT_ok (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t) (ht : TB w s k t)
    (hW : WS w s t fun _ => []) :
    WP isa (.seq (.block updT) (callUpd .r11 f)) t fun u => BR w s k u ∧ TB w s k u ∧
      WS w s u fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k := by
  refine WP.seq (WP.mono (argsT_ok hp h (P := fun u => TB w s k u ∧ WS w s u (fun _ => []))
    fun u hm => ⟨fun prk hK => by rw [hm]; exact ht prk hK, fun prk hK => by rw [hm]; exact hW prk hK⟩)
    fun t₁ ⟨b₁, ⟨h₁, w₁⟩, a₁⟩ => ?_)
  refine WP.mono (upd_step hp hw b₁ h₁ w₁ (ml := 0) (fun _ _ => rfl) a₁) fun u ⟨b, h', ws⟩ =>
    ⟨b, h', fun prk hK => ?_⟩
  have := ws prk hK
  rwa [List.nil_append, fA_eq hp (by decide), h₁ prk hK] at this

theorem stageI_ok (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t) (ht : TB w s k t)
    (hW : WS w s t fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k) :
    WP isa (.seq (.block updI) (callUpd .r11 f)) t fun u => BR w s k u ∧ TB w s k u ∧
      WS w s u fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s := by
  refine WP.seq (WP.mono (argsI_ok hp h (P := fun u => TB w s k u ∧
      WS w s u (fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k))
    fun u hm => ⟨fun prk hK => by rw [hm]; exact ht prk hK, fun prk hK => by rw [hm]; exact hW prk hK⟩)
    fun t₁ ⟨b₁, ⟨h₁, w₁⟩, a₁⟩ => ?_)
  refine WP.mono (upd_step hp hw b₁ h₁ w₁ (ml := pl w k) (fun prk _ => tBlock_len hw _ _ k) a₁) fun u ⟨b, h', ws⟩ =>
    ⟨b, h', fun prk hK => ?_⟩
  have := ws prk hK
  rwa [b₁.er.infoB hp] at this

theorem stageC_ok (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t) (ht : TB w s k t)
    (hW : WS w s t fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s) :
    WP isa (.seq (.block updC) (callUpd .r11 f)) t fun u => BR w s k u ∧ TB w s k u ∧
      WS w s u fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s ++ [BitVec.ofNat 8 (k + 1)] := by
  refine WP.seq (WP.mono (argsC_ok hp h (P := fun u => TB w s k u ∧
      WS w s u (fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s))
    fun u hm => ⟨fun prk hK => by rw [hm]; exact ht prk hK, fun prk hK => by rw [hm]; exact hW prk hK⟩)
    fun t₁ ⟨b₁, ⟨h₁, w₁⟩, a₁⟩ => ?_)
  refine WP.mono (upd_step hp hw b₁ h₁ w₁ (ml := pl w k + infoLen s) (fun prk _ => by
      rw [List.length_append, tBlock_len hw, Proof.Hmac.Common.bytesAt_length]) a₁) fun u ⟨b, h', ws⟩ =>
    ⟨b, h', fun prk hK => ?_⟩
  have := ws prk hK
  rwa [fA_eq hp (by decide), ctr_byte b₁.c] at this

end

/-! ### HMAC's `finalize` -/

/-- `finalize`'s arguments. -/
structure FA (w : HVar) (s : State) (k : Nat) (t : State) : Prop where
  r0 : t.gpr .r0 = fb s + BitVec.ofNat 32 eW
  r1 : t.gpr .r1 = s.gpr .r0 + BitVec.ofNat 32 192
  r2 : t.gpr .r2 = BitVec.ofNat 32 (w.F.H.B + (pl w k + infoLen s + 1))
  r3 : t.gpr .r3 = 0
  r10 : t.gpr .r10 = fb s + BitVec.ofNat 32 eT
  r12 : t.gpr .r12 = fb s + BitVec.ofNat 32 eWork

/-- After `finalize`: `T(k + 1)` in the frame, for each pseudorandom key. -/
abbrev TF (w : HVar) (s : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s prk → bytesAt t.mem (fA s eT) w.F.H.D = Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) (k + 1)

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

theorem argsF_ok {k : Nat} {t : State} (h : BR w s k t) {P : State → Prop} (hP : ∀ u, u.mem = t.mem → P u) :
    WP isa (.block finT) t fun u => BR w s k u ∧ P u ∧ FA w s k u := by
  have k₀ := h.er
  unfold finT
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ => wp_addi (by decide) fun t₃ u₃ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k₀.sp, BitVec.add_zero]
  refine wp_ldr (a := tA (stackArg s 1) tB) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), k₀.r11])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact tin hp k₀ (by decide)) fun t₄ u₄ => ?_
  refine wp_ldr (a := fA s eL) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h12]
        exact fA_eq hp (by decide))
    (fr_in' hp (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact k₀.wr) (by decide)) fun t₅ u₅ => ?_
  refine wp_addr fun t₆ u₆ => wp_addr fun t₇ u₇ => wp_addi (by decide) fun t₈ u₈ => wp_movi (by decide) fun t₉ u₉ =>
    wp_addi (by decide) fun t₁₀ u₁₀ => wp_addi (by decide) fun t₁₁ u₁₁ => WP.block_nil ?_
  have hm : t₁₁.mem = t.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.same hp (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
      (by rw [u₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms])
      (fun r hr => by
        simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other,
          u₃.other, u₂.other, u₁.other]) hm, hP _ hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr,
      h12]
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other,
      u₁.other, k₀.r4]
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other,
      u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.other, u₃.other, u₂.other, u₁.other, k₀.r6]
    rw [k₀.tabW hp (by decide), hp.tB, h.l,
      show s.gpr .r2 = BitVec.ofNat 32 (infoLen s) by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg _ (by omega_using [])
  · upd_simp [u₁₁.other, u₁₀.other, u₉.gpr]; rfl
  · upd_simp [u₁₁.other, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
      h12]
  · upd_simp [u₁₁.gpr, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
      h12]

theorem key192 : State.addr (s.gpr .r0 + BitVec.ofNat 32 192) = keyA s + BitVec.ofNat 64 192 := by
  have := hp.nk; exact VG.Arm.addr_add (by omega_using [this])

theorem fin_args (hw : HOk w) {k : Nat} {t u : State} (h : BR w s k t) (ha : FA w s k t) {v : BitVec 32}
    (hu : Upd t u .lr v) :
    Proof.Pbkdf2.Whole.Arm.HfArgs w.ok.hH.SH w.ok.Wf u (fb s + BitVec.ofNat 32 eW) (s.gpr .r0 + BitVec.ofNat 32 192)
      (fb s + BitVec.ofNat 32 eT) (fb s + BitVec.ofNat 32 eWork) := by
  have k₀ := h.er
  have hfr := eFr_eq; have hS := hw.hS; have hW := hw.hW; have hfN := fbN' hp; have hsb := stateBytes_eq w
  have heW : eW = 112 := rfl; have heWk : eWork = 304 := rfl; have heT : eT = 48 := rfl
  have hdb : w.ok.hH.SH.digestBytes = w.F.H.D := w.ok.hH.hD
  have hD := D_le w
  have hS' : w.ok.hH.SH.stateBytes ≤ 192 := by omega_using [hS, hsb]
  have hb := stk24 hp (by rw [hu.sp, k₀.sp])
  have e0 := fA_eq hp (o := eW) (by decide)
  have e2 := fA_eq hp (o := eT) (by decide)
  have e3 := fA_eq hp (o := eWork) (by decide)
  have nk := hp.nk
  have ou : Region.Sub ⟨State.addr (s.gpr .r0 + BitVec.ofNat 32 192), w.ok.hH.SH.stateBytes⟩ (keyR s) := by
    rw [key192 hp]; exact Offset.sub_base _ (by omega_using [hS'])
  have hbs : Region.Sub ⟨B s + BitVec.ofNat 64 8, 24⟩ (stkR s) := Offset.sub_base _ (by decide)
  exact
    { r0 := by rw [hu.other _ (by decide)]; exact ha.r0
      r1 := by rw [hu.other _ (by decide)]; exact ha.r1
      r10 := by rw [hu.other _ (by decide)]; exact ha.r10
      r12 := by rw [hu.other _ (by decide)]; exact ha.r12
      sp := by
        rw [hu.sp, k₀.sp]; have h1 : (fb s).toNat + eFr = s.sp.toNat := hp.st.fbN; have := hp.sp
        simp only [eStack] at this; omega_using [h1, this]
      cr := VG.Covers.left (VG.Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨keyR s, by rw [hu.rd, k₀.rd, hp.rd]; exact List.mem_cons_self .., 192, key192 hp,
          by dsimp only; omega_using [hS']⟩)
      cw := by
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact fr_cov hp (by rw [hu.wr]; exact k₀.wr) (o := eW) (n := w.ok.hH.SH.stateBytes)
            (by omega_using [hS', hfr, heW])
        · rw [e2]; exact fr_cov hp (by rw [hu.wr]; exact k₀.wr) (o := eT) (n := w.ok.hH.SH.digestBytes)
            (by omega_using [hdb, hD, hfr, heT])
        · rw [e3]; exact fr_cov hp (by rw [hu.wr]; exact k₀.wr) (o := eWork) (n := w.ok.Wf * 8)
            (by omega_using [hW, hfr, heWk])
      i_u := by rw [e0]; exact (hp.s_k.sub_left (fr_sub (o := eW) (n := w.ok.hH.SH.stateBytes)
                    (by omega_using [hS', hfr, heW]))).sub_right ou
      i_o := by rw [e0, e2]; exact fr_disj hp (.inr (by omega_using [hdb, hD, heW, heT]))
                    (by omega_using [hS', hfr, heW]) (by omega_using [hdb, hD, hfr, heT])
      i_s := by rw [e0, e3]; exact fr_disj hp (.inl (by omega_using [hS', heW, heWk]))
                    (by omega_using [hS', hfr, heW]) (by omega_using [hW, hfr, heWk])
      u_o := by rw [e2]; exact (hp.s_k.sub_left (fr_sub (o := eT) (n := w.ok.hH.SH.digestBytes)
                    (by omega_using [hdb, hD, hfr, heT]))).sub_right ou |>.symm
      u_s := by rw [e3]; exact (hp.s_k.sub_left (fr_sub (o := eWork) (n := w.ok.Wf * 8)
                    (by omega_using [hW, hfr, heWk]))).sub_right ou |>.symm
      o_s := by rw [e2, e3]; exact fr_disj hp (.inl (by omega_using [hdb, hD, heT, heWk]))
                    (by omega_using [hdb, hD, hfr, heT]) (by omega_using [hW, hfr, heWk])
      b_i := by rw [hb, e0]; exact hp.st.disj (.inl (by omega_using [heW])) (by decide)
                    (by omega_using [hS', hfr, heW])
      b_u := by rw [hb]; exact (hp.s_k.sub_left hbs).sub_right ou
      b_o := by rw [hb, e2]; exact hp.st.disj (.inl (by omega_using [heT])) (by decide)
                    (by omega_using [hdb, hD, hfr, heT])
      b_s := by rw [hb, e3]; exact hp.st.disj (.inl (by omega_using [heWk])) (by decide)
                    (by omega_using [hW, hfr, heWk])
      ni := by rw [fbN hp (by decide)]; omega_using [hS', hfr, hfN, heW]
      nu := by
        have : (s.gpr .r0 + BitVec.ofNat 32 192).toNat = (s.gpr .r0).toNat + 192 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 192) (by decide),
            Nat.mod_eq_of_lt (by omega_using [nk])]
        rw [this]; omega_using [hS', nk]
      no := by rw [fbN hp (by decide)]; omega_using [hdb, hD, hfr, hfN, heT]
      nsc := by rw [fbN hp (by decide)]; omega_using [hW, hfr, hfN, heWk] }

theorem fin_step (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t)
    (hW : WS w s t fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s ++ [BitVec.ofNat 8 (k + 1)])
    (ha : FA w s k t) : WP isa (callFin .r11 f) t fun u => BR w s k u ∧ TF w s k u := by
  have k₀ := h.er
  have hfr := eFr_eq; have hS := hw.hS; have hW' := hw.hW; have hsb := stateBytes_eq w
  have heW : eW = 112 := rfl; have heWk : eWork = 304 := rfl; have heT : eT = 48 := rfl
  have hdb : w.ok.hH.SH.digestBytes = w.F.H.D := w.ok.hH.hD
  have hD := D_le w
  have hS' : w.ok.hH.SH.stateBytes ≤ 192 := by omega_using [hS, hsb]
  refine tcall_ok (n := w.F.hfN) (c := w.F.hfC) (tabFn hp k₀ (j := 2) (by decide) hp.tm.2.2 hp.tok.f)
    fun u hu => ?_
  have e0 := fA_eq hp (o := eW) (by decide)
  have e2 := fA_eq hp (o := eT) (by decide)
  have e3 := fA_eq hp (o := eWork) (by decide)
  apply WP.of_syms
  refine Proof.Pbkdf2.Whole.Arm.hf_frame (reprOK w) (by rw [hsb]; have := w.ok.hH.hSB; omega_using [this])
    w.ok.hf w.ok.hfSt (fin_args hp hw h ha hu) fun s' hf hpost sy => ?_
  have hws : ∀ r ∈ Proof.Pbkdf2.Whole.Arm.HfArgs.wr w.ok.hH.SH w.ok.Wf (fb s + BitVec.ofNat 32 eW)
      (fb s + BitVec.ofNat 32 eT) (fb s + BitVec.ofNat 32 eWork) ++ [Proof.Pbkdf2.Whole.Arm.stk u], WkB s r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [e0]; exact .inr (Offset.sub _ (by omega_using [heW, heT]) (by omega_using [hS', hfr, heW, heT]))
    · rw [e2]; exact .inr (Offset.sub _ (by omega_using [heT]) (by omega_using [hdb, hD, hfr, heT]))
    · rw [e3]; exact .inr (Offset.sub _ (by omega_using [heWk, heT]) (by omega_using [hW', hfr, heWk, heT]))
    · rw [stk24 hp (by rw [hu.sp, k₀.sp])]; exact .inl (Offset.sub_base _ (by decide))
  have hu₁ : BR w s k u := h.same hp hu.rd hu.wr hu.sp hu.syms (fun r hr => hu.other r (by revert r; decide)) hu.mem
  refine ⟨hu₁.keep hp hf.rd hf.wr hf.sp sy (fun r hr => hf.cs r (bregs_pres r hr).1 (bregs_pres r hr).2) hf.frame hws,
    fun prk hK => ?_⟩
  have hl : (k0 w prk).length = w.ok.hH.SH.H.blockSize := by rw [blockKey_len hw, w.ok.hH.hB]
  have htl : (Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s ++ [BitVec.ofNat 8 (k + 1)]).length =
      pl w k + infoLen s + 1 := by
    rw [List.length_append, List.length_append, tBlock_len hw, Proof.Hmac.Common.bytesAt_length]; rfl
  have hil := info_lt hp (w := w); have hpl := pl_le w k; have hB := w.ok.hH.hBB
  -- The outer state at `key + 192`, as on entry.
  have ho : w.ok.hH.SH.Repr u.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 192)) (xorPad (k0 w prk) opad) := by
    rw [key192 hp]
    refine w.ok.hH.repr s.mem u.mem _ _ _ (fun i hi => ?_) hK.2
    rw [Offset.add_add, hu.mem]
    exact k₀.keyB hp (by omega_using [hi, hS])
  have := hpost (k0 w prk) (Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s ++ [BitVec.ofNat 8 (k + 1)]) hl (by rw [hl, htl, w.ok.hH.hB]; omega_using [hil, hpl, hB])
    (by rw [hu.mem, e0]; exact hW prk hK)
    (by rw [hu.other _ (by decide), hu.other _ (by decide), ha.r3, ha.r2, htl, w.ok.hH.hB]
        exact append_zero (by omega_using [hil, hpl, hB]))
    ho
  rw [hdb, e2] at this
  exact this

theorem stageF_ok (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t)
    (hW : WS w s t fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++ infoOf s ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.seq (.block finT) (callFin .r11 f)) t fun u => BR w s k u ∧ TF w s k u :=
  WP.seq (WP.mono (argsF_ok hp h (P := fun u => WS w s u fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) k ++
      infoOf s ++ [BitVec.ofNat 8 (k + 1)]) fun u hm prk hK => by rw [hm]; exact hW prk hK)
    fun _ ⟨b₁, w₁, a₁⟩ => fin_step hp hw b₁ w₁ a₁)

end

/-! ### The copy to `out` -/

/-- `min(D, rem)`, as `outArgs` computes it with no branch: `rem` plus
`D - rem` masked by the carry of that subtraction less one. -/
theorem minsel {D rem : Nat} (hD : D < 2 ^ 32) (hr : rem < 2 ^ 32) :
    BitVec.ofNat 32 rem + ((BitVec.ofNat 32 D - BitVec.ofNat 32 rem) &&&
      (BitVec.ofNat 32 0 + BitVec.ofNat 32 0 +
        (if decide ((BitVec.ofNat 32 rem).toNat ≤ (BitVec.ofNat 32 D).toNat) then 1 else 0) - BitVec.ofNat 32 1)) =
      BitVec.ofNat 32 (min D rem) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hr]
  by_cases h : rem ≤ D
  · simp only [h, decide_true, ite_true, Nat.min_eq_right h]
    simp
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_le h))]
    rw [show (BitVec.ofNat 32 0 + BitVec.ofNat 32 0 + 0 - BitVec.ofNat 32 1 : BitVec 32) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The bytes of `T(k + 1)` that block `k + 1` copies to `out`. -/
abbrev nb (w : HVar) (s : State) (k : Nat) : Nat := min w.F.H.D (outLen s - k * w.F.H.D)

/-- After `outArgs`: `copyLoop`'s arguments, and the count in `r7`. -/
structure OA (w : HVar) (s : State) (k : Nat) (t : State) : Prop where
  br : BR w s k t
  tf : TF w s k t
  r1 : t.gpr .r1 = fb s + BitVec.ofNat 32 eT
  r2 : t.gpr .r2 = s.gpr .r3 + BitVec.ofNat 32 (k * w.F.H.D)
  r3 : t.gpr .r3 = BitVec.ofNat 32 (nb w s k)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (nb w s k)

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

theorem oA_ok {k : Nat} {t : State} (h : BR w s k t) (hT : TF w s k t) : WP isa (.block outArgs) t (OA w s k) := by
  have k₀ := h.er
  unfold outArgs
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k₀.sp, BitVec.add_zero]
  refine wp_ldr (a := tA (stackArg s 1) tD) (by decide) (by rw [u₁.other _ (by decide), k₀.r11])
    (by rw [u₁.rd, u₁.wr]; exact tin hp k₀ (by decide)) fun t₂ u₂ => ?_
  refine wp_subsr fun t₃ u₃ => wp_movi (by decide) fun t₄ u₄ => wp_adci (by decide) fun t₅ u₅ =>
    wp_subi (by decide) fun t₆ u₆ => wp_andr fun t₇ u₇ => wp_addr fun t₈ u₈ => wp_movr fun t₉ u₉ =>
    wp_addi (by decide) fun t₁₀ u₁₀ => wp_movr fun t₁₁ u₁₁ => WP.block_nil ?_
  have hm : t₁₁.mem = t.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.fl.mem, u₂.mem, u₁.mem]
  have hD := D_le w
  have hol : outLen s < 2 ^ 32 := (stackArg s 0).isLt
  have r3₂ : t₂.gpr .r3 = BitVec.ofNat 32 w.F.H.D := by
    rw [u₂.gpr, u₁.mem, k₀.tabW hp (by decide), hp.tD]
  have r9₂ : t₂.gpr .r9 = BitVec.ofNat 32 (outLen s - k * w.F.H.D) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  have c₄ : t₄.c = decide ((t₂.gpr .r9).toNat ≤ (t₂.gpr .r3).toNat) := by rw [u₄.c, u₃.fl.c]
  have hsel : t₈.gpr .r3 = BitVec.ofNat 32 (nb w s k) := by
    upd_simp [u₈.gpr, u₇.other, u₇.gpr, u₆.other, u₆.gpr, u₅.other, u₅.gpr, u₄.other, u₄.gpr, c₄, u₃.gpr,
      u₃.other, r3₂, r9₂]
    exact minsel (by omega_using [hD]) (by omega_using [hol])
  refine ⟨h.same hp (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.fl.rd, u₂.rd, u₁.rd])
      (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.fl.wr, u₂.wr, u₁.wr])
      (by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.fl.sp, u₂.sp, u₁.sp])
      (by rw [u₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.fl.syms, u₂.syms, u₁.syms])
      (fun r hr => by
        simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other,
          u₃.other, u₂.other, u₁.other]) hm,
    fun prk hK => by rw [hm]; exact hT prk hK, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₁₁.other, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
      u₂.other, h12]
  · upd_simp [u₁₁.gpr, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
      u₂.other, u₁.other, h.r8]
  · upd_simp [u₁₁.other, u₁₀.other, u₉.other]; exact hsel
  · upd_simp [u₁₁.other, u₁₀.other, u₉.gpr]; exact hsel

end

/-- After the copy to `out`. -/
structure CP (w : HVar) (s : State) (k : Nat) (t : State) : Prop where
  er : ER s t
  r7 : t.gpr .r7 = BitVec.ofNat 32 (nb w s k)
  r8 : t.gpr .r8 = s.gpr .r3 + BitVec.ofNat 32 (k * w.F.H.D)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (outLen s - k * w.F.H.D)
  c : t.mem.readW (fA s eC) 32 = BitVec.ofNat 32 (k + 1)
  tf : TF w s k t
  lt : k * w.F.H.D < outLen s
  ob : ∀ prk, Keyd w s prk → bytesAt t.mem (outA s) (k * w.F.H.D + nb w s k) =
    Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf s) k [] 1 ++
      (Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf s) (k + 1)).take (nb w s k)

section
variable {w : HVar} {f : Fns} {s : State} (hp : EP w f s)
include hp

theorem outK {k : Nat} (hk : k * w.F.H.D < outLen s) :
    State.addr (s.gpr .r3 + BitVec.ofNat 32 (k * w.F.H.D)) = outA s + BitVec.ofNat 64 (k * w.F.H.D) := by
  have h : (s.gpr .r3).toNat + outLen s ≤ 2 ^ 32 := hp.no; exact VG.Arm.addr_add (by omega_using [h, hk])

theorem cp_ok {k : Nat} {t : State} (h : OA w s k t) : WP isa Impl.AesGcm.Arm.copyLoop t (CP w s k) := by
  have k₀ := h.br.er
  have hfr := eFr_eq; have heT : eT = 48 := rfl; have hfN := fbN' hp
  have hD := D_le w; have hD0 := w.ok.hH.hD0; have hlt := h.br.lt
  have hnb : nb w s k ≤ w.F.H.D := Nat.min_le_left _ _
  have hnb' : nb w s k ≤ outLen s - k * w.F.H.D := Nat.min_le_right _ _
  have hno : (s.gpr .r3).toNat + outLen s ≤ 2 ^ 32 := hp.no
  have eT' := fA_eq hp (o := eT) (by decide)
  have eO := outK hp hlt
  have tS : Region.Sub ⟨fA s eT, nb w s k⟩ (stkR s) := fr_sub (by omega_using [hnb, hD, hfr, heT])
  have oS : Region.Sub ⟨outA s + BitVec.ofNat 64 (k * w.F.H.D), nb w s k⟩ (outR s) := Offset.sub_base _ (by
    omega_using [hnb', hlt])
  have pre : Proof.AesGcm.Arm.LoopPre t (fb s + BitVec.ofNat 32 eT) (s.gpr .r3 + BitVec.ofNat 32 (k * w.F.H.D))
      (nb w s k) :=
    { r1 := h.r1, r2 := h.r2, r3 := h.r3
      pos := by
        have : 1 ≤ outLen s - k * w.F.H.D := by omega_using [hlt]
        exact Nat.le_min.mpr ⟨hD0, this⟩
      lt := by omega_using [hnb, hD]
      fitS := by rw [fbN hp (by decide)]; omega_using [hnb, hD, hfN, hfr, heT]
      fitD := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * w.F.H.D) (by omega_using [hlt, hno]),
          Nat.mod_eq_of_lt (by omega_using [hlt, hno])]
        omega_using [hnb', hlt, hno]
      rd := VG.Covers.right (VG.Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [eT']; exact fr_cov hp k₀.wr (o := eT) (n := nb w s k) (by omega_using [hnb, hD, hfr, heT]))
      wr := VG.Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨outR s, by rw [k₀.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
          k * w.F.H.D, eO, by dsimp only; omega_using [hnb', hlt]⟩
      disj := by rw [eT', eO]; exact (hp.s_o.sub_left tS).sub_right oS }
  refine WP.mono_syms (Proof.AesGcm.Arm.copyLoop_ok t pre) fun u ⟨hm, lo⟩ sy => ?_
  rw [eO, eT', aes_bytes] at hm
  have hl : (bytesAt t.mem (fA s eT) (nb w s k)).length = nb w s k := Proof.Hmac.Common.bytesAt_length _ _ _
  have F : Frame [⟨outA s + BitVec.ofNat 64 (k * w.F.H.D), nb w s k⟩] t.mem u.mem := by
    rw [hm]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have hfd : ∀ {R : Region}, Region.Sub R (stkR s) →
      ∀ r ∈ [(⟨outA s + BitVec.ofNat 64 (k * w.F.H.D), nb w s k⟩ : Region)], R.Disjoint r := fun hR r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.s_o.sub_left hR).sub_right oS
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → u.gpr r = t.gpr r := lo.other
  refine ⟨k₀.keep hp lo.rd lo.wr lo.sp sy (fun r hr => g r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)) F
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr oS)),
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r7,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.br.r8,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.br.r9,
    by rw [F.readW (r := ⟨fA s eC, 4⟩) (Region.contains_self _ _) (hfd (fr_sub (by decide))) (by decide)]
       exact h.br.c,
    fun prk hK => ?_, hlt, fun prk hK => ?_⟩
  · rw [bytes_keep F (hfd (fr_sub (by omega_using [hD, hfr, heT]))) (by omega_using [hD])]
    exact h.tf prk hK
  · rw [Proof.Hmac.Common.bytesAt_add, bytes_keep F (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hnb', hlt, hno])) (by omega_using [hlt, hno]),
      h.br.ob prk hK, hm]
    have hws := Proof.Hmac.Common.bytesAt_writeBytes_self t.mem (outA s + BitVec.ofNat 64 (k * w.F.H.D))
      (bytesAt t.mem (fA s eT) (nb w s k)) (by rw [hl]; omega_using [hnb, hD])
    rw [hl] at hws
    rw [hws, VG.Proof.Hkdf.Arm.Expand.bytesAt_take _ _ hnb, h.tf prk hK]

omit hp in
theorem done_succ {k : Nat} (h : k * w.F.H.D < outLen s) : done w s (k + 1) = k * w.F.H.D + nb w s k := by
  simp only [done, nb, Nat.succ_mul]
  omega_arith

theorem next_ok (hw : HOk w) {k : Nat} {t : State} (h : CP w s k t) : WP isa (.block nextBlock) t (EI w s (k + 1)) := by
  have k₀ := h.er
  have hfr := eFr_eq; have hD := D_le w
  have hlt := h.lt
  have hnb : nb w s k ≤ w.F.H.D := Nat.min_le_left _ _
  have hnb' : nb w s k ≤ outLen s - k * w.F.H.D := Nat.min_le_right _ _
  have hds := done_succ (w := w) (s := s) hlt
  unfold nextBlock
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addr fun t₂ u₂ => wp_subr fun t₃ u₃ => ?_
  have h12 : t₃.gpr .r12 = fb s := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, k₀.sp, BitVec.add_zero]
  refine wp_ldr (a := tA (stackArg s 1) tD) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), k₀.r11])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact tin hp k₀ (by decide)) fun t₄ u₄ => ?_
  have wr₄ : t₄.wr = ⟨State.addr (fb s), eFr⟩ :: s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact k₀.wr
  refine wp_str (a := fA s eL) (by decide) (by rw [u₄.other _ (by decide), h12]; exact fA_eq hp (by decide))
    (fr_in hp wr₄ (by decide)) fun t₅ u₅ => ?_
  refine wp_ldr (a := fA s eC) (by decide)
    (by rw [u₅.gpr, u₄.other _ (by decide), h12]; exact fA_eq hp (by decide))
    (fr_in' hp (by rw [u₅.wr]; exact wr₄) (by decide)) fun t₆ u₆ => ?_
  refine wp_addi (by decide) fun t₇ u₇ => ?_
  refine wp_str (a := fA s eC) (by decide)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), h12]
        exact fA_eq hp (by decide))
    (fr_in hp (by rw [u₇.wr, u₆.wr, u₅.wr]; exact wr₄) (by decide)) fun t₈ u₈ => ?_
  refine wp_cmpi (by decide) fun t₉ g₉ f₉ => WP.block_nil ?_
  -- The memory: the length's word, then the counter's.
  have hsep : Mem.Sep (fA s eC) (32 / 8) (fA s eL) (32 / 8) :=
    Region.Disjoint.sep (fr_disj hp (o := eC) (n := 4) (o' := eL) (n' := 4) (.inl (by decide)) (by decide) (by decide))
      (Region.contains_self _ _) (Region.contains_self _ _)
  have m₅ : t₅.mem = t.mem.writeW (fA s eL) (BitVec.ofNat 32 w.F.H.D) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, k₀.tabW hp (by decide), hp.tD]
  have c₅ : t₅.mem.readW (fA s eC) 32 = BitVec.ofNat 32 (k + 1) := by
    rw [m₅, Mem.readW_writeW_sep hsep (by decide)]; exact h.c
  have m₉ : t₉.mem = (t.mem.writeW (fA s eL) (BitVec.ofNat 32 w.F.H.D)).writeW (fA s eC)
      (BitVec.ofNat 32 (k + 1 + 1)) := by
    rw [f₉.mem, u₈.mem, u₇.gpr, u₆.gpr, u₇.mem, u₆.mem, c₅, m₅, BitVec.ofNat_add (k + 1) 1]
  have F : Frame [⟨fA s eL, 4⟩, ⟨fA s eC, 4⟩] t.mem t₉.mem := by
    rw [m₉]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cself _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (cself _)
  have hfd : ∀ {R : Region}, Region.Disjoint R (stkR s) → ∀ r ∈ [(⟨fA s eL, 4⟩ : Region), ⟨fA s eC, 4⟩],
      R.Disjoint r := fun hR r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hR.sub_right (fr_sub (by decide))
    · exact hR.sub_right (fr_sub (by decide))
  have hol : outLen s < 2 ^ 32 := (stackArg s 0).isLt
  have r9₃ : t₃.gpr .r9 = BitVec.ofNat 32 (outLen s - done w s (k + 1)) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide),
      h.r9, h.r7, hds, Offset.ofNat_sub_ofNat hnb']
    congr 1; omega_using [hnb']
  have hpl : pl w (k + 1) = w.F.H.D := by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
  have hsep' : Mem.Sep (fA s eL) (32 / 8) (fA s eC) (32 / 8) :=
    Region.Disjoint.sep (fr_disj hp (o := eL) (n := 4) (o' := eC) (n' := 4) (.inr (by decide)) (by decide) (by decide))
      (Region.contains_self _ _) (Region.contains_self _ _)
  refine ⟨k₀.keep hp (by rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
      (by rw [f₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms])
      (fun r hr => by
        simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        all_goals upd_simp [g₉, u₈.gpr, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other]) F
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact wk_fr (by decide) (by decide)
        · exact wk_fr (by decide) (by decide)), ?_, ?_, ?_, ?_, ?_, fun prk hK => ?_, fun prk hK => ?_⟩
  · upd_simp [g₉, u₈.gpr, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.gpr, u₁.other]
    rw [h.r8, h.r7, BitVec.add_assoc, ← BitVec.ofNat_add, hds]
  · upd_simp [g₉, u₈.gpr, u₇.other, u₆.other, u₅.gpr, u₄.other]; exact r9₃
  · rw [f₉.z, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), r9₃]
    exact congrArg (· == 0) (BitVec.sub_zero _)
  · rw [m₉, Mem.readW_writeW_self32]
  · rw [m₉, Mem.readW_writeW_sep hsep' (by decide), Mem.readW_writeW_self32, hpl]
  · have hle : k * w.F.H.D + nb w s k ≤ outLen s := by omega_using [hnb', hlt]
    rw [hds, bytes_keep (p := outA s) (n := k * w.F.H.D + nb w s k) F
        (hfd (hp.s_o.symm.sub_left (Region.sub_prefix hle))) (by omega_using [hle, hol]), h.ob prk hK,
      Proof.Hkdf.blocks_succ, List.take_append,
      List.take_of_length_le (l := Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf s) k [] 1)
        (by rw [Proof.Hkdf.blocks_length _ _ _ (hash_length hw)]; omega_using []),
      Proof.Hkdf.blocks_length _ _ _ (hash_length hw), Nat.add_sub_cancel_left]
  · have heT : eT = 48 := rfl
    rw [hpl, bytes_keep F (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fr_disj hp (.inr (by decide)) (by omega_using [hD, hfr, heT]) (by decide)
        · exact fr_disj hp (.inr (by decide)) (by omega_using [hD, hfr, heT]) (by decide))
      (by omega_using [hD])]
    exact h.tf prk hK

omit hp in
/-- `Z` clear before a block: bytes of `out` are left, and the block runs. -/
theorem ei_br (hw : HOk w) {k : Nat} {t : State} (h : EI w s k t) (hz : t.z = false) : BR w s k t ∧ TB w s k t := by
  have hd : done w s k = min (k * w.F.H.D) (outLen s) := rfl
  have h0 : outLen s - done w s k ≠ 0 := fun h0 => by
    have e := h.z; rw [hz, h0] at e; exact absurd e (by decide)
  have hlt : k * w.F.H.D < outLen s := by omega_using [hd, h0]
  have hd' : done w s k = k * w.F.H.D := by omega_using [hd, hlt]
  refine ⟨⟨h.er, by rw [h.r8, hd'], by rw [h.r9, hd'], h.c, h.l, hlt, fun prk hK => ?_⟩, h.tb⟩
  have := h.ob prk hK
  rwa [hd', List.take_of_length_le (Nat.le_of_eq (Proof.Hkdf.blocks_length _ _ _ (hash_length hw) k))] at this

omit hp in
/-- `Z` set after a block: no bytes of `out` are left. -/
theorem ei_z {k : Nat} {t : State} (h : EI w s k t) (hz : t.z = true) : outLen s ≤ k * w.F.H.D := by
  have hd : done w s k = min (k * w.F.H.D) (outLen s) := rfl
  have hol : outLen s < 2 ^ 32 := (stackArg s 0).isLt
  have h0 : outLen s - done w s k = 0 := by
    have e := h.z; rw [hz] at e
    have e' := congrArg BitVec.toNat (beq_iff_eq.mp e.symm)
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol])] at e'
  omega_using [hd, h0]

/-- Block `k + 1`. -/
theorem block_ok (hw : HOk w) {k : Nat} {t : State} (h : BR w s k t) (ht : TB w s k t) :
    WP isa (block f) t (EI w s (k + 1)) := by
  unfold block
  refine WP.assoc (WP.seq (WP.mono (copy_ok hp hw h ht) fun t₁ ⟨b₁, h₁, w₁⟩ => ?_))
  refine WP.assoc (WP.seq (WP.mono (stageT_ok hp hw b₁ h₁ w₁) fun t₂ ⟨b₂, h₂, w₂⟩ => ?_))
  refine WP.assoc (WP.seq (WP.mono (stageI_ok hp hw b₂ h₂ w₂) fun t₃ ⟨b₃, h₃, w₃⟩ => ?_))
  refine WP.assoc (WP.seq (WP.mono (stageC_ok hp hw b₃ h₃ w₃) fun t₄ ⟨b₄, _, w₄⟩ => ?_))
  refine WP.assoc (WP.seq (WP.mono (stageF_ok hp hw b₄ w₄) fun t₅ ⟨b₅, h₅⟩ => ?_))
  exact WP.seq (WP.mono (oA_ok hp b₅ h₅) fun t₆ h₆ => WP.seq (WP.mono (cp_ok hp h₆) fun t₇ h₇ => next_ok hp hw h₇))

/-- After the blocks: all of `out` written. -/
def EF (w : HVar) (s : State) (t : State) : Prop := ∃ k, EI w s k t ∧ outLen s ≤ k * w.F.H.D

/-- The blocks, while bytes of `out` are left. -/
theorem loop_ok (hw : HOk w) {k : Nat} {t : State} (h : EI w s k t) :
    WP isa (.ite .eq (.block []) (.loop (block f) .ne)) t (EF w s) := by
  refine WP.ite t.z rfl (fun hz => WP.block_nil ⟨k, h, ei_z h hz⟩) fun hz => ?_
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, EI w s j u ∧ u.z = false ∧ n = outLen s - done w s j)
    (fun n u hi => ?_) _ t ⟨k, h, hz, rfl⟩
  obtain ⟨j, hj, hz, hn⟩ := hi
  obtain ⟨b, tb⟩ := ei_br hw hj hz
  refine WP.mono (block_ok hp hw b tb) fun u hu => ?_
  cases hzu : u.z
  · have hlt := b.lt
    have hds := done_succ (w := w) (s := s) hlt
    have hd : done w s j = min (j * w.F.H.D) (outLen s) := rfl
    have hD0 := w.ok.hH.hD0
    have hnb : nb w s j = min w.F.H.D (outLen s - j * w.F.H.D) := rfl
    refine .inr ⟨by show some (!u.z) = some true; rw [hzu]; rfl, _, ?_, j + 1, hu, rfl, rfl⟩
    omega_using [hn, hds, hd, hnb, hlt, hD0]
  · exact .inl ⟨by show some (!u.z) = some false; rw [hzu]; rfl, j + 1, hu, ei_z hu hzu⟩

/-! ## The epilogue -/

omit hp in
theorem epi_eq : expandEpi = .addSp .r12 0 :: eSaved.map (fun p => Instr.ldr p.1 .r12 p.2) := rfl

omit hp in
theorem eSaved_restorable : Spill.Restorable .r12 eSaved := by decide

/-- The epilogue restores our caller's registers and our return address. -/
theorem epi_ok {t : State} (k : ER s t) :
    WP isa (.block expandEpi) t fun u => (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.sp = fb s ∧ u.mem = t.mem := by
  have hfr := eFr_eq
  rw [epi_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h12 : t₁.gpr .r12 = fb s := by rw [u₁.gpr, k.sp, BitVec.add_zero]
  rw [← List.append_nil (List.map _ eSaved)]
  refine Spill.restore_slots_ok eSaved_slots eSaved_restorable (g := s.gpr) (by
      rw [h12]; have h1 : (fb s).toNat + eFr = s.sp.toNat := hp.st.fbN; have := s.sp.isLt
      omega_using [h1, this, hfr])
    (fun d _ hd => by rw [h12, fb_add hp, u₁.rd, u₁.wr]; exact fr_in' hp k.wr (by omega_using [hd, hfr]))
    (by rw [h12, u₁.mem]; exact k.saved) fun u hr _ hm _ _ hsp => WP.block_nil ⟨fun r hr' => ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Spill.restored_reg hr (by decide)
  · rw [hsp, u₁.sp, k.sp]
  · rw [hm, u₁.mem]

end

/-- `vg_hkdf_expand` meets `expandR` and keeps the callee-saved registers
and the stack pointer. -/
theorem expand_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (expandR w f ns eStack).pre s) :
    WP isa (expand f) s fun s' => abiPreserved s s' ∧ (expandR w f ns eStack).post s s' := by
  have p := ep_of hp
  unfold expand
  refine WP.alloc (by decide) (by have := p.sp; simp only [eStack] at this; omega_using [this]) ?_
  unfold expandMain
  refine WP.seq (WP.mono (pro_ok p) fun t₁ h₁ => WP.seq (WP.mono (loop_ok p hw h₁) fun t₂ ⟨k, h₂, hk⟩ => ?_))
  refine WP.mono (epi_ok p h₂.er) fun u ⟨hcs, hsp, hm⟩ m uk hfm => ⟨⟨fun r hr => hcs r hr, ?_⟩, fun prk hK => ?_⟩
  · show u.sp + BitVec.ofNat 32 eFr = s.sp
    rw [hsp]; exact fb_eFr s
  · have hol : outLen s < 2 ^ 32 := (stackArg s 0).isLt
    have hD0 := w.ok.hH.hD0
    have e : bytesAt m (outA s) (outLen s) = bytesAt u.mem (outA s) (outLen s) :=
      bytes_keep hfm (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [fb_addr p]; exact (p.s_o.sub_left (fr_sub (o := 0) (n := eFr) (by omega_using []))).symm)
        (by omega_using [hol])
    have hd : done w s k = min (k * w.F.H.D) (outLen s) := rfl
    have hd' : done w s k = outLen s := by omega_using [hd, hk]
    have ob := h₂.ob prk hK
    rw [hd'] at ob
    have hn : outLen s ≤ (outLen s + w.F.H.D - 1) / w.F.H.D * w.F.H.D := by
      have h1 := Nat.div_add_mod (outLen s + w.F.H.D - 1) w.F.H.D
      have h2 := Nat.mod_lt (outLen s + w.F.H.D - 1) hD0
      rw [Nat.mul_comm] at h1
      omega_using [h1, h2, hD0]
    show Spec.Hkdf.expand _ _ prk (infoOf s) (outLen s) = some (bytesAt m (outA s) (outLen s))
    rw [e, hm, ob]
    unfold Spec.Hkdf.expand
    simp only [Nat.not_lt.mpr p.ol, ↓reduceIte]
    congr 1
    rcases Nat.le_total k ((outLen s + w.F.H.D - 1) / w.F.H.D) with hkn | hkn
    · rw [← Nat.add_sub_cancel' hkn, Proof.Hkdf.blocks_take _ _ _ (hash_length hw) hk]
    · rw [← Nat.add_sub_cancel' hkn, Proof.Hkdf.blocks_take _ _ _ (hash_length hw) hn]

/-! ## Constant time -/

theorem pro_ck : Ck [.r12] (.block expandPro.tail) := ⟨_, by taint_decide⟩
theorem copyW_ck : Ck [.r12] (.block copyW.tail) := ⟨_, by taint_decide⟩
theorem cl_ck : Ck [.r1, .r2, .r3] Impl.AesGcm.Arm.copyLoop := ⟨_, by taint_decide⟩
theorem updT_ck : Ck [.r12, .r11] (.block updT.tail) := ⟨_, by taint_decide⟩
theorem updI_ck : Ck [.r12, .r11] (.block updI.tail) := ⟨_, by taint_decide⟩
theorem updC_ck : Ck [.r12, .r11] (.block updC.tail) := ⟨_, by taint_decide⟩
theorem finT_ck : Ck [.r12, .r11] (.block finT.tail) := ⟨_, by taint_decide⟩
theorem outArgs_ck : Ck [.r12, .r11] (.block outArgs.tail) := ⟨_, by taint_decide⟩
theorem next_ck : Ck [.r12, .r11] (.block nextBlock.tail) := ⟨_, by taint_decide⟩
theorem epi_ck : Ck [.r12] (.block expandEpi.tail) := ⟨_, by taint_decide⟩


/-- Two runs whose public data agree. -/
structure Two (w : HVar) (f : Fns) (e e' : State) : Prop where
  hp : EP w f e
  hp' : EP w f e'
  sp : e.sp = e'.sp
  r0 : e.gpr .r0 = e'.gpr .r0
  r1 : e.gpr .r1 = e'.gpr .r1
  r2 : e.gpr .r2 = e'.gpr .r2
  r3 : e.gpr .r3 = e'.gpr .r3
  a0 : stackArg e 0 = stackArg e' 0
  a1 : stackArg e 1 = stackArg e' 1
  su : e.syms w.F.H.updN = e'.syms w.F.H.updN
  sf : e.syms w.F.hfN = e'.syms w.F.hfN

/-- The bytes `out` has left shrink with each block. -/
theorem done_lt {w : HVar} {s : State} {k : Nat} (hlt : k * w.F.H.D < outLen s) :
    outLen s - done w s (k + 1) < outLen s - done w s k := by
  have hds := done_succ (w := w) (s := s) hlt
  have hd : done w s k = min (k * w.F.H.D) (outLen s) := rfl
  have hD0 := w.ok.hH.hD0
  have hnb : nb w s k = min w.F.H.D (outLen s - k * w.F.H.D) := rfl
  omega_using [hds, hd, hnb, hlt, hD0]

theorem z_of_ne {x : State} {b : Bool} (h : isa.eval .ne x = some b) : x.z = !b := by
  have h' : some (!x.z) = some b := h
  rw [Option.some.injEq] at h'
  rw [← h', Bool.not_not]

section
variable {w : HVar} {f : Fns} {e e' : State} (T : Two w f e e')
include T

theorem Two.fbe : fb e' = fb e := by rw [Expand.fb, Expand.fb, T.sp]
theorem Two.ole : outLen e' = outLen e := by rw [Expand.outLen, Expand.outLen, T.a0]
theorem Two.ile : infoLen e' = infoLen e := by rw [Expand.infoLen, Expand.infoLen, T.r2]
theorem Two.donee (k : Nat) : done w e' k = done w e k := by rw [Expand.done, Expand.done, T.ole]
theorem Two.nbe (k : Nat) : nb w e' k = nb w e k := by rw [Expand.nb, Expand.nb, T.ole]

theorem callUpd_rel (hw : HOk w) {P : State → State → Prop} {dat : BitVec 32} {len ml : Nat}
    (hP : ∀ x y, P x y → ER e x ∧ ER e' y ∧ UA w e dat len ml x ∧ UA w e' dat len ml y) :
    RelCT isa P (callUpd .r11 f) fun _ _ => True :=
  tcall_rel (fun x y hxy => by
      obtain ⟨k, k', -, -⟩ := hP x y hxy
      exact ⟨tabFn T.hp k (j := 1) (by decide) T.hp.tm.2.1 T.hp.tok.u,
        tabFn T.hp' k' (j := 1) (by decide) T.hp'.tm.2.1 T.hp'.tok.u, by rw [k.r11, k'.r11, T.a1],
        by rw [k.sy, k'.sy, T.su], by rw [k.sp, k'.sp, T.fbe]⟩)
    (Proof.Pbkdf2.Whole.Arm.upd_rel w.ok.hH (sp := fb e) fun u u' hu => by
      obtain ⟨x, x', hxy, v, v'⟩ := hu
      obtain ⟨k, k', a, a'⟩ := hP x x' hxy
      have := upd_args T.hp' hw k' a' v'
      rw [T.fbe] at this
      refine ⟨upd_args T.hp hw k a v, this, ?_, by rw [v.sp, k.sp], by rw [v'.sp, k'.sp, T.fbe]⟩
      simp only [Pbkdf2.Stream.Arm.count]
      rw [v.other _ (by decide), v.other _ (by decide), v'.other _ (by decide), v'.other _ (by decide), a.r2,
        a.r3, a'.r2, a'.r3])

theorem callFin_rel (hw : HOk w) {k : Nat} {P : State → State → Prop}
    (hP : ∀ x y, P x y → BR w e k x ∧ BR w e' k y ∧ FA w e k x ∧ FA w e' k y) :
    RelCT isa P (callFin .r11 f) fun _ _ => True :=
  tcall_rel (fun x y hxy => by
      obtain ⟨b, b', -, -⟩ := hP x y hxy
      exact ⟨tabFn T.hp b.er (j := 2) (by decide) T.hp.tm.2.2 T.hp.tok.f,
        tabFn T.hp' b'.er (j := 2) (by decide) T.hp'.tm.2.2 T.hp'.tok.f, by rw [b.er.r11, b'.er.r11, T.a1],
        by rw [b.er.sy, b'.er.sy, T.sf], by rw [b.er.sp, b'.er.sp, T.fbe]⟩)
    (Proof.Pbkdf2.Whole.Arm.hf_rel w.ok.hf (sp := fb e) fun u u' hu => by
      obtain ⟨x, x', hxy, v, v'⟩ := hu
      obtain ⟨b, b', a, a'⟩ := hP x x' hxy
      have := fin_args T.hp' hw b' a' v'
      rw [T.fbe, ← T.r0] at this
      exact ⟨fin_args T.hp hw b a v, this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.r2, a'.r2, T.ile],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.r3, a'.r3],
        by rw [v.sp, b.er.sp], by rw [v'.sp, b'.er.sp, T.fbe]⟩)

/-- The copy of the inner state. -/
theorem pA (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y => (BR w e k x ∧ TB w e k x) ∧ (BR w e' k y ∧ TB w e' k y))
      (.seq (.block copyW) Impl.AesGcm.Arm.copyLoop) fun x y =>
        (BR w e k x ∧ TB w e k x ∧ WS w e x fun _ => []) ∧ (BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun _ => []) := by
  have a1 := rel_both (P₁ := fun x => BR w e k x ∧ TB w e k x) (P₂ := fun y => BR w e' k y ∧ TB w e' k y)
    (c := .block copyW) (rel_blk copyW_ck fun x y h => ⟨by rw [h.1.1.er.sp, h.2.1.er.sp, T.fbe], fun _ h => absurd h List.not_mem_nil⟩)
    (G₁ := fun u => BR w e k u ∧ u.gpr .r1 = e.gpr .r0 ∧ u.gpr .r2 = fb e + BitVec.ofNat 32 eW ∧
      u.gpr .r3 = BitVec.ofNat 32 192)
    (G₂ := fun u => BR w e' k u ∧ u.gpr .r1 = e'.gpr .r0 ∧ u.gpr .r2 = fb e' + BitVec.ofNat 32 eW ∧
      u.gpr .r3 = BitVec.ofNat 32 192)
    (fun x h => WP.mono (copyW_ok T.hp h.1) fun _ ⟨b, _, _, r1, r2, r3⟩ => ⟨b, r1, r2, r3⟩)
    (fun y h => WP.mono (copyW_ok T.hp' h.1) fun _ ⟨b, _, _, r1, r2, r3⟩ => ⟨b, r1, r2, r3⟩)
  refine rel_both (a1.seq (rel_ck cl_ck fun x y h => ?_)) (fun x h => copy_ok T.hp hw h.1 h.2)
    (fun y h => copy_ok T.hp' hw h.1 h.2)
  obtain ⟨⟨-, x1, x2, x3⟩, ⟨-, y1, y2, y3⟩⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [x1, y1, T.r0]
  · rw [x2, y2, T.fbe]
  · rw [x3, y3]

/-- The absorption of `T(k)`. -/
theorem pT (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y => (BR w e k x ∧ TB w e k x ∧ WS w e x fun _ => []) ∧
        (BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun _ => []))
      (.seq (.block updT) (callUpd .r11 f)) fun x y =>
        (BR w e k x ∧ TB w e k x ∧ WS w e x fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k) ∧
        (BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k) := by
  have a1 := rel_both (P₁ := fun x => BR w e k x ∧ TB w e k x ∧ WS w e x fun _ => [])
    (P₂ := fun y => BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun _ => []) (c := .block updT)
    (rel_blk updT_ck fun x y h => ⟨by rw [h.1.1.er.sp, h.2.1.er.sp, T.fbe], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.er.r11, h.2.1.er.r11, T.a1]⟩)
    (fun x h => argsT_ok T.hp h.1 (P := fun _ => True) fun _ _ => trivial)
    (fun y h => argsT_ok T.hp' h.1 (P := fun _ => True) fun _ _ => trivial)
  exact rel_both (a1.seq (callUpd_rel T hw fun x y h => ⟨h.1.1.er, h.2.1.er, h.1.2.2, by
      have := h.2.2.2; rwa [T.fbe] at this⟩))
    (fun x h => stageT_ok T.hp hw h.1 h.2.1 h.2.2) (fun y h => stageT_ok T.hp' hw h.1 h.2.1 h.2.2)

/-- The absorption of `info`. -/
theorem pI (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y =>
        (BR w e k x ∧ TB w e k x ∧ WS w e x fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k) ∧
        (BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k))
      (.seq (.block updI) (callUpd .r11 f)) fun x y =>
        (BR w e k x ∧ TB w e k x ∧
          WS w e x fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k ++ infoOf e) ∧
        (BR w e' k y ∧ TB w e' k y ∧
          WS w e' y fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k ++ infoOf e') := by
  have a1 := rel_both
    (P₁ := fun x => BR w e k x ∧ TB w e k x ∧ WS w e x fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k)
    (P₂ := fun y => BR w e' k y ∧ TB w e' k y ∧
      WS w e' y fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k) (c := .block updI)
    (rel_blk updI_ck fun x y h => ⟨by rw [h.1.1.er.sp, h.2.1.er.sp, T.fbe], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.er.r11, h.2.1.er.r11, T.a1]⟩)
    (fun x h => argsI_ok T.hp h.1 (P := fun _ => True) fun _ _ => trivial)
    (fun y h => argsI_ok T.hp' h.1 (P := fun _ => True) fun _ _ => trivial)
  exact rel_both (a1.seq (callUpd_rel T hw fun x y h => ⟨h.1.1.er, h.2.1.er, h.1.2.2, by
      have := h.2.2.2; rwa [← T.r1, T.ile] at this⟩))
    (fun x h => stageI_ok T.hp hw h.1 h.2.1 h.2.2) (fun y h => stageI_ok T.hp' hw h.1 h.2.1 h.2.2)

/-- The absorption of the counter. -/
theorem pC (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y =>
        (BR w e k x ∧ TB w e k x ∧
          WS w e x fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k ++ infoOf e) ∧
        (BR w e' k y ∧ TB w e' k y ∧
          WS w e' y fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k ++ infoOf e'))
      (.seq (.block updC) (callUpd .r11 f)) fun x y =>
        (BR w e k x ∧ TB w e k x ∧ WS w e x fun prk =>
          Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k ++ infoOf e ++ [BitVec.ofNat 8 (k + 1)]) ∧
        (BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun prk =>
          Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k ++ infoOf e' ++ [BitVec.ofNat 8 (k + 1)]) := by
  have a1 := rel_both
    (P₁ := fun x => BR w e k x ∧ TB w e k x ∧
      WS w e x fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k ++ infoOf e)
    (P₂ := fun y => BR w e' k y ∧ TB w e' k y ∧
      WS w e' y fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k ++ infoOf e') (c := .block updC)
    (rel_blk updC_ck fun x y h => ⟨by rw [h.1.1.er.sp, h.2.1.er.sp, T.fbe], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.er.r11, h.2.1.er.r11, T.a1]⟩)
    (fun x h => argsC_ok T.hp h.1 (P := fun _ => True) fun _ _ => trivial)
    (fun y h => argsC_ok T.hp' h.1 (P := fun _ => True) fun _ _ => trivial)
  exact rel_both (a1.seq (callUpd_rel T hw fun x y h => ⟨h.1.1.er, h.2.1.er, h.1.2.2, by
      have := h.2.2.2; rwa [T.fbe, T.ile] at this⟩))
    (fun x h => stageC_ok T.hp hw h.1 h.2.1 h.2.2) (fun y h => stageC_ok T.hp' hw h.1 h.2.1 h.2.2)

/-- HMAC's `finalize` into `T(k + 1)`. -/
theorem pF (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y =>
        (BR w e k x ∧ TB w e k x ∧ WS w e x fun prk =>
          Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k ++ infoOf e ++ [BitVec.ofNat 8 (k + 1)]) ∧
        (BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun prk =>
          Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k ++ infoOf e' ++ [BitVec.ofNat 8 (k + 1)]))
      (.seq (.block finT) (callFin .r11 f)) fun x y => (BR w e k x ∧ TF w e k x) ∧ (BR w e' k y ∧ TF w e' k y) := by
  have a1 := rel_both
    (P₁ := fun x => BR w e k x ∧ TB w e k x ∧ WS w e x fun prk =>
      Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e) k ++ infoOf e ++ [BitVec.ofNat 8 (k + 1)])
    (P₂ := fun y => BR w e' k y ∧ TB w e' k y ∧ WS w e' y fun prk =>
      Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf e') k ++ infoOf e' ++ [BitVec.ofNat 8 (k + 1)]) (c := .block finT)
    (rel_blk finT_ck fun x y h => ⟨by rw [h.1.1.er.sp, h.2.1.er.sp, T.fbe], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.er.r11, h.2.1.er.r11, T.a1]⟩)
    (fun x h => argsF_ok T.hp h.1 (P := fun _ => True) fun _ _ => trivial)
    (fun y h => argsF_ok T.hp' h.1 (P := fun _ => True) fun _ _ => trivial)
  exact rel_both (a1.seq (callFin_rel T hw fun x y h => ⟨h.1.1, h.2.1, h.1.2.2, h.2.2.2⟩))
    (fun x h => stageF_ok T.hp hw h.1 h.2.2) (fun y h => stageF_ok T.hp' hw h.1 h.2.2)

/-- The count of bytes to copy to `out`. -/
theorem pO (k : Nat) :
    RelCT isa (fun x y => (BR w e k x ∧ TF w e k x) ∧ (BR w e' k y ∧ TF w e' k y)) (.block outArgs)
      fun x y => OA w e k x ∧ OA w e' k y :=
  rel_both (P₁ := fun x => BR w e k x ∧ TF w e k x) (P₂ := fun y => BR w e' k y ∧ TF w e' k y)
    (c := .block outArgs)
    (rel_blk outArgs_ck fun x y h => ⟨by rw [h.1.1.er.sp, h.2.1.er.sp, T.fbe], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.er.r11, h.2.1.er.r11, T.a1]⟩)
    (fun x h => oA_ok T.hp h.1 h.2) (fun y h => oA_ok T.hp' h.1 h.2)

/-- The copy to `out`. -/
theorem pCp (k : Nat) :
    RelCT isa (fun x y => OA w e k x ∧ OA w e' k y) Impl.AesGcm.Arm.copyLoop fun x y => CP w e k x ∧ CP w e' k y :=
  rel_both (rel_ck cl_ck fun x y h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.r1, h.2.r1, T.fbe]
      · rw [h.1.r2, h.2.r2, T.r3]
      · rw [h.1.r3, h.2.r3, T.nbe])
    (fun x h => cp_ok T.hp h) (fun y h => cp_ok T.hp' h)

/-- The next block's count, counter and length. -/
theorem pN (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y => CP w e k x ∧ CP w e' k y) (.block nextBlock) fun x y => EI w e (k + 1) x ∧ EI w e' (k + 1) y :=
  rel_both (P₁ := CP w e k) (P₂ := CP w e' k) (c := .block nextBlock)
    (rel_blk next_ck fun x y h => ⟨by rw [h.1.er.sp, h.2.er.sp, T.fbe], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.er.r11, h.2.er.r11, T.a1]⟩)
    (fun x h => next_ok T.hp hw h) (fun y h => next_ok T.hp' hw h)

/-- Block `k + 1`, in two runs. -/
theorem body_rel (hw : HOk w) (k : Nat) :
    RelCT isa (fun x y => (BR w e k x ∧ TB w e k x) ∧ (BR w e' k y ∧ TB w e' k y)) (block f)
      fun x y => EI w e (k + 1) x ∧ EI w e' (k + 1) y := by
  unfold block
  exact RelCT.assoc ((pA T hw k).seq (RelCT.assoc ((pT T hw k).seq (RelCT.assoc ((pI T hw k).seq
    (RelCT.assoc ((pC T hw k).seq (RelCT.assoc ((pF T hw k).seq ((pO T k).seq ((pCp T k).seq (pN T hw k))))))))))))

/-- The loop's invariant in two runs: the same block next, with bytes of
`out` left. -/
def LI (w : HVar) (e e' : State) (n : Nat) (x y : State) : Prop :=
  ∃ k, (EI w e k x ∧ x.z = false) ∧ (EI w e' k y ∧ y.z = false) ∧ n = outLen e - done w e k

/-- The blocks, in two runs. -/
theorem loop_rel (hw : HOk w) (n : Nat) :
    RelCT isa (LI w e e' n) (.loop (block f) .ne) fun x y => EF w e x ∧ EF w e' y := by
  refine RelCT.loop (M := isa) (LI w e e') (fun n => ?_) n
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, ⟨h₁, z₁⟩, ⟨h₂, z₂⟩, hn⟩ e₁ e₂
  obtain ⟨b₁, tb₁⟩ := ei_br hw h₁ z₁
  obtain ⟨b₂, tb₂⟩ := ei_br hw h₂ z₂
  obtain ⟨ht, g₁, g₂⟩ := body_rel T hw k _ _ _ _ _ _ ⟨⟨b₁, tb₁⟩, ⟨b₂, tb₂⟩⟩ e₁ e₂
  have hz : s₂'.z = s₁'.z := by rw [g₁.z, g₂.z, T.ole, T.donee]
  have hc : isa.eval .ne s₁' = isa.eval .ne s₂' := by
    show some (!s₁'.z) = some (!s₂'.z); rw [hz]
  refine ⟨ht, hc, fun hf => ⟨⟨k + 1, g₁, ei_z g₁ ?_⟩, ⟨k + 1, g₂, ei_z g₂ ?_⟩⟩, fun ht' => ?_⟩
  · rw [z_of_ne hf]; rfl
  · rw [hz, z_of_ne hf]; rfl
  · have y₁ : s₁'.z = false := by rw [z_of_ne ht']; rfl
    exact ⟨_, by rw [hn]; exact done_lt b₁.lt, k + 1, ⟨g₁, y₁⟩, ⟨g₂, by rw [hz, y₁]⟩, rfl⟩

end

/-- `vg_hkdf_expand` is constant time: two runs whose public data agree leak
the same trace. -/
theorem expand_ct {w : HVar} {f : Fns} {ns : List String} (hw : HOk w)
    (hns : ∀ n ∈ [w.F.H.updN, w.F.hfN], n ∈ ns) :
    ConstantTime isa (expandR w f ns eStack).pre (expandR w f ns eStack).pub (expand f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  obtain ⟨qsp, q0, q1, q2, q3, qa0, qa1, qn⟩ := hpub
  have T : Two w f e e' := ⟨ep_of h, ep_of h', qsp, q0, q1, q2, q3, qa0, qa1, qn _ (hns _ (by simp)),
    qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (expand f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold expand expandMain
  refine RelCT.allocFrame ?_
  have r1 : RelCT isa (fun x y => ∃ s₁ s₂, (s₁ = e ∧ s₂ = e') ∧ x = allocated eFr s₁ ∧ y = allocated eFr s₂)
      (.block expandPro) fun x y => EI w e 0 x ∧ EI w e' 0 y := by
    refine ((rel_blk pro_ck fun x y hxy => ?_).wp fun x y hxy => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    · obtain ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ := hxy
      subst e₁ e₂ hx hy; exact ⟨by simp only [allocated, qsp], fun _ h => absurd h List.not_mem_nil⟩
    · obtain ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ := hxy
      subst e₁ e₂ hx hy; exact ⟨pro_ok T.hp, pro_ok T.hp'⟩
  have hz : ∀ x y, EI w e 0 x ∧ EI w e' 0 y → y.z = x.z := fun x y ⟨h₁, h₂⟩ => by
    rw [h₁.z, h₂.z, T.ole, T.donee]
  have r2 : RelCT isa (fun x y => EI w e 0 x ∧ EI w e' 0 y) (.ite .eq (.block []) (.loop (block f) .ne))
      fun x y => EF w e x ∧ EF w e' y := by
    refine RelCT.ite (fun x y h => by show some x.z = some y.z; rw [hz x y h])
      (RelCT.block_nil fun x y ⟨h, hc⟩ => ?_) ((loop_rel T hw (outLen e - done w e 0)).mono (fun x y ⟨h, hc⟩ => ?_) fun _ _ h => h)
    · have h1 : x.z = true := Option.some.inj hc
      exact ⟨⟨0, h.1, ei_z h.1 h1⟩, ⟨0, h.2, ei_z h.2 (by rw [hz x y h, h1])⟩⟩
    · have h1 : x.z = false := Option.some.inj hc
      exact ⟨0, ⟨h.1, h1⟩, ⟨h.2, by rw [hz x y h, h1]⟩, rfl⟩
  have r3 : RelCT isa (fun x y => EF w e x ∧ EF w e' y) (.block expandEpi) fun _ _ => True :=
    rel_blk epi_ck fun x y ⟨⟨_, h₁, _⟩, ⟨_, h₂, _⟩⟩ =>
      ⟨by rw [h₁.er.sp, h₂.er.sp, T.fbe], fun _ h => absurd h List.not_mem_nil⟩
  exact r1.seq (r2.seq r3)

end VG.Proof.Hkdf.Arm.Expand
