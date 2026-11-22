module

public import VerifiedGarbage.Proof.Hkdf.AArch64.Key
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkLoop
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.Hkdf.AArch64

/-!
# HKDF on AArch64: `vg_hkdf_expand`, correct and constant time

The contract the proof is written against (`expandR`), for the table `hmac`
of one variant `w` (`MdHash`), whose functions an indirect call of `f`'s
reaches: `expand(key, info, info_len, out, out_len, hmac)` writes
HKDF-Expand's `out_len` bytes to `out`, for every pseudorandom key the
states at `key` are keyed with (`Spec.Hkdf.Keyed`).

As on x86-64 (`Proof/Hkdf/X86_64/Expand.lean`): the return address pushed
and the frame (`eFr` bytes: the save area, the working state, `T(i)`, the
counter's byte, then the working space) allocated, the prologue saves our
caller's registers and keeps the arguments, the bytes of `out` left, the
counter and the length of `T(i - 1)` in callee-saved registers (`pro_ok`,
from which on `ER` holds). Each block (`block_ok`) makes the working state
the inner state at `key` (a copy of its hash value), absorbs `T(i - 1)`,
`info` and the counter, finalizes with the outer state at `key + 192` into
`T(i)` in the frame, and copies its first `min(D, rem)` bytes to `out`;
before block `i + 1`, `out`'s first `min(i D, L)` bytes are
`T(1) ‖ … ‖ T(i)`'s (`EI`). The blocks run while bytes of `out` are left
(`loop_ok`), and the epilogue restores our caller's registers.

Constant time: the taint analysis checks each piece between the calls from
the registers both runs agree on (`rel_agree`), which the single-run facts
give; `min(D, rem)` comes from a `csel`, whose result the analysis takes to
be secret, but `D` and `rem` are public, so both runs agree on it too.
-/

@[expose] public section

namespace VG.Proof.Hkdf.AArch64.Expand

open VG VG.AArch64 VG.AArch64.Steps
open VG.Impl.Hkdf.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (TabOK TabMem)
open VG.Proof.Hkdf.AArch64 (HOk StackAt base stackAt entered toNat_addN repr_keep Ck rel_agree)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame)

/-- `expand(key, info, info_len, out, out_len, hmac)`, with `N` bytes of
stack, for the table `hmac` of `w`, whose functions an indirect call of
`f`'s reaches, with the addresses of the functions `ns` public. -/
def expandR (w : MdHash) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let info : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let out : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let tab : Region := ⟨s.gpr .x5, 48⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 N, N⟩
    N ≤ s.sp.toNat ∧ s.rd = [key, info, tab] ∧ s.wr = [out] ∧
      key.Disjoint out ∧ info.Disjoint out ∧ out.Disjoint tab ∧
      stk.Disjoint key ∧ stk.Disjoint info ∧ stk.Disjoint out ∧ stk.Disjoint tab ∧
      (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat ≤ 255 * w.H.D ∧ TabMem w.H s.syms (s.gpr .x5) s.mem ∧
      s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B ∧ TabOK w.H f s.syms
  post s s' := ∀ prk, Spec.Hkdf.Keyed w.ok.SH s.mem (s.gpr .x0) prk →
    Spec.Hkdf.expand w.ok.SH.H w.H.D prk (Spec.Sha256.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (s.gpr .x4).toNat = some (Spec.Sha256.bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_expand` uses: the return address, its frame, and the
16 bytes below it that the calls use. -/
def eStack : Nat := eFr + 32

theorem eFr_eq : eFr = 2208 := rfl
theorem eStack_eq : eStack = 2240 := rfl

/-! ## The frame's body -/

section
variable (s₀ : State)

/-- The arguments, on entry to the frame's body. -/
abbrev keyA : Addr := s₀.gpr .x0
abbrev infoA : Addr := s₀.gpr .x1
abbrev infoLen : Nat := (s₀.gpr .x2).toNat
abbrev outA : Addr := s₀.gpr .x3
abbrev outLen : Nat := (s₀.gpr .x4).toNat
abbrev tabA : Addr := s₀.gpr .x5

/-- An address in the frame. -/
abbrev sA (o : Nat) : Addr := s₀.sp + BitVec.ofNat 64 o

abbrev frR : Region := ⟨s₀.sp, eFr⟩
/-- The return address pushed, above the frame. -/
abbrev pushR : Region := ⟨sA s₀ eFr, 16⟩
abbrev kyR : Region := ⟨keyA s₀, 384⟩
abbrev inR : Region := ⟨infoA s₀, infoLen s₀⟩
abbrev otR : Region := ⟨outA s₀, outLen s₀⟩
abbrev tbR : Region := ⟨tabA s₀, 48⟩
/-- The stack below the frame that the calls use. -/
abbrev stk : Region := below s₀.sp 16

/-- The regions the frame's body writes. -/
abbrev wrs : List Region := [frR s₀, otR s₀, stk s₀]

end

/-- The state the frame's body starts in. -/
structure Pre (w : MdHash) (f : Fns) (s₀ : State) : Prop where
  hw : HOk w
  rd : s₀.rd = [kyR s₀, inR s₀, tbR s₀]
  wr : s₀.wr = [frR s₀, pushR s₀, otR s₀]
  ol : outLen s₀ ≤ 255 * w.H.D
  k_o : (kyR s₀).Disjoint (otR s₀)
  i_o : (inR s₀).Disjoint (otR s₀)
  o_t : (otR s₀).Disjoint (tbR s₀)
  f_k : (frR s₀).Disjoint (kyR s₀)
  f_i : (frR s₀).Disjoint (inR s₀)
  f_o : (frR s₀).Disjoint (otR s₀)
  f_t : (frR s₀).Disjoint (tbR s₀)
  b_k : (stk s₀).Disjoint (kyR s₀)
  b_i : (stk s₀).Disjoint (inR s₀)
  b_o : (stk s₀).Disjoint (otR s₀)
  b_t : (stk s₀).Disjoint (tbR s₀)
  b_f : (stk s₀).Disjoint (frR s₀)
  p_f : (pushR s₀).Disjoint (frR s₀)
  p_o : (pushR s₀).Disjoint (otR s₀)
  p_b : (pushR s₀).Disjoint (stk s₀)
  sp : 16 ≤ s₀.sp.toNat
  top : s₀.sp.toNat + (eFr + 16) ≤ 2 ^ 64
  nk : (keyA s₀).toNat + 384 ≤ 2 ^ 64
  ni : (infoA s₀).toNat + infoLen s₀ ≤ 2 ^ 64
  no : (outA s₀).toNat + outLen s₀ ≤ 2 ^ 64
  nt : (tabA s₀).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w.H s₀.syms (tabA s₀) s₀.mem
  tD : s₀.mem.readW (tabA s₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D
  tB : s₀.mem.readW (tabA s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B
  tok : TabOK w.H f s₀.syms
  ret : s₀.mem.read (sA s₀ eFr) 8 = s₀.gpr .x30

/-- The push writes only its 16 bytes. -/
theorem entered_frame (s : State) : Frame [⟨s.sp - 16, 16⟩] s.mem (entered eFr s).mem :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)

/-- The push's 16 bytes, within the stack the contract gives. -/
theorem push_sub {s : State} (hS : StackAt s eFr (base s eFr)) :
    Region.Sub ⟨s.sp - 16, 16⟩ ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
  rw [hS.push]
  exact Offset.sub_base _ (by omega_using [eStack_eq, eFr_eq])

/-- The return address's slot, from the frame's body. -/
theorem sA_push {s : State} (hS : StackAt s eFr (base s eFr)) : sA (entered eFr s) eFr = s.sp - 16 := by
  show (entered eFr s).sp + BitVec.ofNat 64 eFr = _
  rw [show (entered eFr s).sp = base s eFr + BitVec.ofNat 64 16 from hS.frame, Offset.add_add, hS.push,
    Nat.add_comm]

section
variable {w : MdHash} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hw : HOk w) (hp : (expandR w f ns eStack).pre s) : Pre w f (entered eFr s) := by
  obtain ⟨hN, hrd, hwr, ko, io, ot, sk, si, so, st, nk, ni, no, nt, hol, tm, td, tb, tok⟩ := hp
  have hS := stackAt s eFr (by rw [eStack] at hN; exact hN)
  have hfr := eFr_eq
  have hnw := hS.nw
  have hsp : (entered eFr s).sp = base s eFr + BitVec.ofNat 64 16 := hS.frame
  have hB : (base s eFr).toNat + eStack ≤ 2 ^ 64 := hnw
  obtain subF : Region.Sub (frR (entered eFr s)) ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
    show Region.Sub ⟨(entered eFr s).sp, eFr⟩ ⟨base s eFr, eStack⟩
    rw [hsp]; exact Offset.sub_base _ (by rw [eStack_eq, eFr_eq]; decide)
  obtain hpu : pushR (entered eFr s) = ⟨s.sp - 16, 16⟩ := by
    show (⟨sA (entered eFr s) eFr, 16⟩ : Region) = _; rw [sA_push hS]
  obtain hbe : stk (entered eFr s) = ⟨base s eFr, 16⟩ := by
    show (⟨(entered eFr s).sp - BitVec.ofNat 64 16, 16⟩ : Region) = _
    rw [hsp, BitVec.add_sub_cancel]
  obtain subB : Region.Sub (stk (entered eFr s)) ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
    rw [hbe]; exact Region.sub_prefix (by rw [eStack_eq]; decide)
  obtain subP : Region.Sub (pushR (entered eFr s)) ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
    rw [hpu]; exact push_sub hS
  have pf := entered_frame s
  have ptab : ∀ o, o + 8 ≤ 48 → (entered eFr s).mem.readW (s.gpr .x5 + BitVec.ofNat 64 o) 64 =
      s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 o) 64 := fun o ho =>
    pf.readW (r := ⟨s.gpr .x5, 48⟩) (Offset.contains_base _ ho (by omega_using [ho]))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact st.symm.sub_right (push_sub hS)) (by decide)
  refine ⟨hw, hrd, ?_, hol, ko, io, ot, sk.sub_left subF, si.sub_left subF, so.sub_left subF, st.sub_left subF,
    sk.sub_left subB, si.sub_left subB, so.sub_left subB, st.sub_left subB, ?_, ?_, ?_, ?_, ?_, ?_, nk, ni, no, nt,
    ⟨(ptab 0 (by decide)).trans tm.1, (ptab 8 (by decide)).trans tm.2.1, (ptab 16 (by decide)).trans tm.2.2⟩,
    (ptab 32 (by decide)).trans td, (ptab 40 (by decide)).trans tb, tok, ?_⟩
  · show (⟨(entered eFr s).sp, eFr⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
    rw [hwr, hpu]; rfl
  · rw [hbe]; show Region.Disjoint ⟨base s eFr, 16⟩ ⟨(entered eFr s).sp, eFr⟩
    rw [hsp]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hfr])
  · show Region.Disjoint (pushR (entered eFr s)) ⟨(entered eFr s).sp, eFr⟩
    rw [hpu, hS.push, hsp]
    exact Offset.disjoint _ (.inr (by omega_using [hfr])) (by omega_using [hfr]) (by omega_using [hfr])
  · exact (so.sub_left subP)
  · rw [hpu, hbe, hS.push]; exact Offset.disjoint_base _ (by omega_using []) (by omega_using [hfr])
  · rw [hsp, toNat_addN (by rw [eStack_eq] at hB; omega_using [hB])]; omega_using []
  · rw [hsp, toNat_addN (by rw [eStack_eq] at hB; omega_using [hB])]
    rw [eStack_eq] at hB; omega_using [hB, hfr]
  · rw [sA_push hS]; exact read_write_self _ _ _

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the end of the prologue on. -/
structure ER (w : MdHash) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  x19 : t.gpr .x19 = keyA s₀
  x20 : t.gpr .x20 = infoA s₀
  x21 : t.gpr .x21 = s₀.gpr .x2
  x24 : t.gpr .x24 = tabA s₀
  x27 : t.gpr .x27 = s₀.gpr .x27
  x28 : t.gpr .x28 = s₀.gpr .x28
  saved : Spill.Saved s₀.sp s₀.gpr eSaved t.mem
  frame : Frame (wrs s₀) s₀.mem t.mem

/-- The registers `ER` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x21, .x24, .x27, .x28]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem saved_fits : Spill.Fits eSaved := by decide

theorem saved_in : ∀ q ∈ eSaved, 0 ≤ q.2 ∧ q.2 + 8 ≤ 0 + 64 := by decide

/-- A part of the frame after the save area, `out`, or the stack below the
frame. -/
def Wk (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ Region.Sub r (otR s₀) ∨ r = stk s₀

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem Wk.ok {r : Region} (h : Wk s₀ r) :
    Region.Disjoint ⟨s₀.sp + BitVec.ofNat 64 0, 64⟩ r ∧ ∃ r' ∈ wrs s₀, Region.Sub r r' := by
  have hfr := eFr_eq
  have sv : Region.Sub ⟨s₀.sp + BitVec.ofNat 64 0, 64⟩ (frR s₀) := Offset.sub_base _ (by omega_using [hfr])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | rfl
  · exact ⟨Offset.disjoint _ (.inl (by omega_using [h₁])) (by decide) (by omega_using [h₂, hfr]),
      _, by simp, Offset.sub_base _ h₂⟩
  · exact ⟨(hp.f_o.sub_left sv).sub_right h, _, by simp, h⟩
  · exact ⟨hp.b_f.symm.sub_left sv, _, by simp, fun _ h => h⟩

theorem ER.keep {t t' : State} (h : ER w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk s₀ r) : ER w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x24,
    (hg _ (by simp)).trans h.x27, (hg _ (by simp)).trans h.x28,
    h.saved.frame_in saved_in hf fun r hr => (Wk.ok hp (hw r hr)).1,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem ER.same {t t' : State} (h : ER w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) : ER w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x24,
    (hg _ (by simp)).trans h.x27, (hg _ (by simp)).trans h.x28, by rw [hm]; exact h.saved,
    by rw [hm]; exact h.frame⟩

omit hp in
theorem ER.upd {t t' : State} (h : ER w s₀ t) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd t t' d v) : ER w s₀ t' :=
  h.same u.rd u.wr u.sp u.syms (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A part of the frame is in the writable regions. -/
theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ eFr) : InRegions t.wr (sA s₀ o) n :=
  ⟨_, by rw [hwr, hp.wr]; exact List.mem_cons_self,
    Offset.contains_base _ h (by have := eFr_eq; omega_using [h, this])⟩

theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ eFr) :
    InRegions (t.rd ++ t.wr) (sA s₀ o) n :=
  let ⟨r, hr, hc⟩ := in_frw hp hwr h; ⟨r, List.mem_append_right _ hr, hc⟩

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem ER.bytes {t : State} (hk : ER w s₀ t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

/-- The bytes of `key`'s region are those on entry. -/
theorem ER.keyB {t : State} (hk : ER w s₀ t) {o n : Nat} (hon : o + n ≤ 384) (i : Nat) (hi : i < n) :
    t.mem (keyA s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
      s₀.mem (keyA s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hs : Region.Sub ⟨keyA s₀ + BitVec.ofNat 64 o, n⟩ (kyR s₀) := Offset.sub_base _ hon
  exact hk.frame.bytes (R := ⟨keyA s₀ + BitVec.ofNat 64 o, n⟩) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_k.symm.sub_left hs
    · exact hp.k_o.sub_left hs
    · exact hp.b_k.symm.sub_left hs) (by show n ≤ 2 ^ 64; omega_using [hon]) hi

theorem ER.infoB {t : State} (hk : ER w s₀ t) :
    bytesAt t.mem (infoA s₀) (infoLen s₀) = bytesAt s₀.mem (infoA s₀) (infoLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_i.symm
    · exact hp.i_o
    · exact hp.b_i.symm) (Nat.le_of_lt (s₀.gpr .x2).isLt)

/-- A word of the table is as on entry. -/
theorem ER.tabW {t : State} (hk : ER w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tabA s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tabA s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tbR s₀) (Offset.contains_base _ ho (by omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.f_t.symm
      · exact hp.o_t.symm
      · exact hp.b_t.symm) (by decide)

theorem tin {t : State} (hk : ER w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (tabA s₀ + BitVec.ofNat 64 o) 8 :=
  ⟨tbR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp), Offset.contains_base _ ho (by omega_using [ho])⟩

/-- An offset of the frame, as a number. -/
theorem sA_toNat {o : Nat} (ho : o ≤ eFr) : (sA s₀ o).toNat = s₀.sp.toNat + o := by
  have top := hp.top
  have hfr := eFr_eq
  rw [sA, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, hfr]),
    Nat.mod_eq_of_lt (by omega_using [ho, top, hfr])]

/-- A load of a word of the table, `ldr d, [x24, #o]`. -/
theorem tload {t : State} (k : ER w s₀ t) {d : Reg} {o : Nat} (ho : o % 8 = 0 ∧ o + 8 ≤ 48) {is : List Instr}
    {Q : State → Prop}
    (h : ∀ t', Upd t t' d (s₀.mem.readW (tabA s₀ + BitVec.ofNat 64 o) 64) → WP isa (.block is) t' Q) :
    WP isa (.block (.ldr .x d .x24 o :: is)) t Q :=
  wp_ldr ⟨ho.1, by omega_using [ho.2]⟩ (by rw [k.x24]) (tin hp k ho.2) fun t' u => h t' (by rw [← k.tabW hp ho.2]; exact u)

end

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-! ## The loop's invariant -/

/-- The length of `T(k)`: none for `T(0)`, `D` after. -/
abbrev pl (w : MdHash) (k : Nat) : Nat := if k = 0 then 0 else w.H.D

/-- `info`. -/
abbrev infoOf (s₀ : State) : List Byte := bytesAt s₀.mem (infoA s₀) (infoLen s₀)

/-- The pseudorandom keys the states at `key` are keyed with. -/
abbrev Keyd (w : MdHash) (s₀ : State) (prk : List Byte) : Prop := Spec.Hkdf.Keyed w.ok.SH s₀.mem (keyA s₀) prk

/-- The bytes of `out` written after `k` blocks. -/
abbrev done (w : MdHash) (s₀ : State) (k : Nat) : Nat := min (k * w.H.D) (outLen s₀)

/-- Before block `k + 1`: the registers and memory kept, `out`'s first
`done` bytes, `T(k)` in the frame, and the registers that count. -/
structure EI (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop where
  er : ER w s₀ t
  x22 : t.gpr .x22 = outA s₀ + BitVec.ofNat 64 (done w s₀ k)
  x23 : t.gpr .x23 = BitVec.ofNat 64 (outLen s₀ - done w s₀ k)
  x26 : t.gpr .x26 = BitVec.ofNat 64 (pl w k)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (k + 1)
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (outA s₀) (done w s₀ k) =
    (Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) k [] 1).take (done w s₀ k)
  tb : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) (pl w k) = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k

/-! ## The prologue -/

theorem pro_eq : expandPro = .addSp .x9 0 :: (Spill.saveCode .x9 eSaved ++
    ([mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5,
      .movz .x .x25 1 0, .movz .x .x26 0 0] : List Instr)) := rfl

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem pro_ok : WP isa (.block expandPro) s₀ (EI w s₀ 0) := by
  rw [pro_eq]
  have hfr := eFr_eq
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain x9 : s₁.gpr .x9 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine Spill.save_ok (b := .x9) (by decide) (fun q hq => ?_) ?_
  · rw [x9, u₁.wr]; exact in_frw hp (t := s₀) rfl (by have := saved_in q hq; omega_using [hfr, this])
  refine wp_addImm (by decide) fun s₂ u₂ => wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_addImm (by decide) fun s₅ u₅ => wp_addImm (by decide) fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ =>
    wp_movz fun s₈ u₈ => wp_movz fun s₉ u₉ => WP.block_nil ?_
  obtain mm : s₉.mem = Spill.saveMem s₁.mem (s₁.gpr .x9) s₁.gpr eSaved := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain hd0 : done w s₀ 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  have er : ER w s₀ s₉ := ⟨by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd,
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr,
    by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp,
    by rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]; exact u₁.syms,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
  · rw [mm]
    intro q hq
    rw [x9, Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    exact u₁.other _ (by revert q; decide)
  · rw [mm, x9, u₁.mem]
    have := Spill.saveMem_frame_base (n := 64) (fun p hp' => by have := (saved_in p hp').2; omega_using [this])
      (by decide) s₀.mem s₀.sp s₁.gpr (l := eSaved)
    exact this.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨frR s₀, by simp, Region.sub_prefix (by omega_using [hfr])⟩
  refine ⟨er, ?_, ?_, ?_, ?_, fun prk _ => ?_, fun prk _ => ?_⟩
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
    rw [hd0, BitVec.add_zero]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]
    rw [hd0, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]; rfl
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other,
      u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.other, BitVec.add_zero]; rfl
  · rw [hd0]; rfl
  · rfl

end

/-! ## A block -/

theorem hash_length (w : MdHash) (m : List Byte) : (w.ok.SH.H.hash m).length = w.H.D := by
  have := w.ok.sizes.DN
  simp only [w.ok.hash, List.length_take, Proof.MdStream.Md.hash, w.ok.md.digest_length]
  omega_using [this]

theorem D_le (w : MdHash) : w.H.D ≤ 64 := by
  have h1 := w.ok.sizes.DN; have h2 := w.ok.N_le; omega_using [h1, h2]

theorem B_le (w : MdHash) : w.H.P.B ≤ 128 := w.ok.B_le

/-- HMAC's key, its block size. -/
theorem blockKey_length (w : MdHash) (k : List Byte) : (blockKey w.ok.SH.H k).length = w.H.P.B := by
  have hB := w.ok.hB
  have hDB : w.H.D ≤ w.H.P.B := by have h1 := w.ok.sizes.DN; have h2 := w.ok.sizes.NL; omega_using [h1, h2]
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · have : (w.ok.SH.H.hash k).length ≤ w.H.D := by rw [w.ok.hash]; exact List.length_take_le _ _
    omega_using [this, hDB]
  · omega_arith

/-- `T(k)` has `pl k` bytes. -/
theorem tBlock_len (w : MdHash) (prk info : List Byte) (k : Nat) :
    (Proof.Hkdf.tBlock w.ok.SH.H prk info k).length = pl w k := by
  cases k with
  | zero => rfl
  | succ k => exact Proof.Hkdf.tBlock_length _ _ _ (hash_length w) k

theorem pl_le (w : MdHash) (k : Nat) : pl w k ≤ w.H.D := by unfold pl; split <;> omega_using []

/-- During block `k + 1`: the registers and memory kept, `out`'s first `k D`
bytes, and the registers that count. -/
structure BR (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop where
  er : ER w s₀ t
  x22 : t.gpr .x22 = outA s₀ + BitVec.ofNat 64 (k * w.H.D)
  x23 : t.gpr .x23 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D)
  x26 : t.gpr .x26 = BitVec.ofNat 64 (pl w k)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (k + 1)
  lt : k * w.H.D < outLen s₀
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (outA s₀) (k * w.H.D) =
    Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) k [] 1

/-- The regions of the frame the block uses. -/
abbrev wR (w : MdHash) (s₀ : State) : Region := ⟨sA s₀ eW, w.H.S⟩
abbrev tR (w : MdHash) (s₀ : State) : Region := ⟨sA s₀ eT, w.H.D⟩
abbrev cR (s₀ : State) : Region := ⟨sA s₀ eC, 1⟩

/-- `K₀` of a pseudorandom key. -/
abbrev k0 (w : MdHash) (prk : List Byte) : List Byte := blockKey w.ok.SH.H prk

/-- The working state represents `K₀ ⊕ ipad`, then `m`, for each
pseudorandom key the states are keyed with. -/
abbrev WS (w : MdHash) (s₀ : State) (t : State) (m : List Byte → List Byte) : Prop :=
  ∀ prk, Keyd w s₀ prk → w.ok.SH.Repr t.mem (sA s₀ eW) (xorPad (k0 w prk) ipad ++ m prk)

/-- `T(k)` in the frame, for each pseudorandom key. -/
abbrev TB (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) (pl w k) = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k

/-- What the registers of `BR` keep. -/
abbrev bregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

theorem bregs_pres : ∀ r ∈ bregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem BR.keep {w : MdHash} {s₀ : State} {k : Nat} {t t' : State} (h : BR w s₀ k t) (he : ER w s₀ t')
    (hg : ∀ r ∈ bregs, t'.gpr r = t.gpr r)
    (hb : bytesAt t'.mem (outA s₀) (k * w.H.D) = bytesAt t.mem (outA s₀) (k * w.H.D)) : BR w s₀ k t' :=
  ⟨he, (hg _ (by simp)).trans h.x22, (hg _ (by simp)).trans h.x23, (hg _ (by simp)).trans h.x26,
    (hg _ (by simp)).trans h.x25, h.lt, fun prk hK => hb.trans (h.ob prk hK)⟩

/-- A state represents a message of whole blocks by its hash value alone. -/
theorem reprN (w : MdHash) {m m' : Mem} {p q : Addr} {msg : List Byte}
    (h : ∀ i < w.H.P.N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) (hl : msg.length % w.H.P.B = 0)
    (hr : w.ok.SH.Repr m p msg) : w.ok.SH.Repr m' q msg := by
  have hr' := (w.ok.repr _ _ _).1 hr
  refine (w.ok.repr _ _ _).2 ⟨by rw [w.ok.reloc m m' p q h]; exact hr'.1, ?_⟩
  have e := hr'.2
  rw [hl] at e ⊢
  exact e

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem wR_sub : Region.Sub (wR w s₀) (frR s₀) :=
  Offset.sub_base _ (by have hS := hp.hw.hS; have hfr := eFr_eq; simp only [eW]; omega_using [hS, hfr])

omit hp in
theorem tR_sub : Region.Sub (tR w s₀) (frR s₀) :=
  Offset.sub_base _ (by have hD := D_le w; have hfr := eFr_eq; simp only [eT]; omega_using [hD, hfr])

theorem w_t : (wR w s₀).Disjoint (tR w s₀) := by
  have hS := hp.hw.hS; have hD := D_le w
  exact Offset.disjoint _ (.inl (by simp only [eW, eT]; omega_using [hS])) (by simp only [eW]; omega_using [hS])
    (by simp only [eT]; omega_using [hD])

theorem w_c : (wR w s₀).Disjoint (cR s₀) := by
  have hS := hp.hw.hS
  exact Offset.disjoint _ (.inl (by simp only [eW, eC]; omega_using [hS])) (by simp only [eW]; omega_using [hS])
    (by decide)

omit hp in
theorem workR {n : Nat} (hn : n ≤ 1872) : Region.Sub ⟨sA s₀ eWork, n⟩ (frR s₀) :=
  Offset.sub_base _ (by have hfr := eFr_eq; simp only [eWork]; omega_using [hn, hfr])

theorem w_s {n : Nat} (hn : n ≤ 1872) : Region.Disjoint (wR w s₀) ⟨sA s₀ eWork, n⟩ := by
  have hS := hp.hw.hS
  exact Offset.disjoint _ (.inl (by simp only [eW, eWork]; omega_using [hS])) (by simp only [eW]; omega_using [hS])
    (by simp only [eWork]; omega_using [hn])

omit hp in
theorem t_s {n : Nat} (hn : n ≤ 1872) : Region.Disjoint (tR w s₀) ⟨sA s₀ eWork, n⟩ := by
  have hD := D_le w
  exact Offset.disjoint _ (.inl (by simp only [eT, eWork]; omega_using [hD])) (by simp only [eT]; omega_using [hD])
    (by simp only [eWork]; omega_using [hn])

/-- The stack below the frame, apart from a part of the frame. -/
theorem stk_fr {o n : Nat} (h : o + n ≤ eFr) : Region.Disjoint (stk s₀) ⟨sA s₀ o, n⟩ :=
  hp.b_f.sub_right (Offset.sub_base _ h)

/-- `info` fits HMAC's count with a block of key, `T(i - 1)` and the counter. -/
theorem info_lt : w.H.P.B + w.H.D + infoLen s₀ + 1 < 2 ^ 64 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hp.f_i.symm hp.ni (by
    show s₀.sp.toNat + eFr ≤ 2 ^ 64; have := hp.top; omega_using [this])
  have hB := B_le w
  have hD := D_le w
  have hfr := eFr_eq
  have h' : infoLen s₀ + eFr ≤ 2 ^ 64 := h
  omega_using [h', hB, hD, hfr]

omit hp in
/-- The bytes of a region apart from `rs` are kept. -/
theorem keep_fr {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    (hR : R.len ≤ 2 ^ 64) : bytesAt m' R.base R.len = bytesAt m R.base R.len :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes hd hR hi

/-- `out` is apart from the frame and the stack below it. -/
theorem out_apart {o n : Nat} (h : o + n ≤ outLen s₀) {r : Region}
    (hr' : (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ r = stk s₀) :
    Region.Disjoint ⟨outA s₀ + BitVec.ofNat 64 o, n⟩ r := by
  have hs : Region.Sub ⟨outA s₀ + BitVec.ofNat 64 o, n⟩ (otR s₀) := Offset.sub_base _ h
  rcases hr' with ⟨o', n', rfl, _, h₂⟩ | rfl
  · exact (hp.f_o.symm.sub_left hs).sub_right (Offset.sub_base _ h₂)
  · exact hp.b_o.symm.sub_left hs

/-- `out`'s first `k D` bytes, apart from `rs`, are kept. -/
theorem out_keep {k : Nat} (hk : k * w.H.D < outLen s₀) {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hw : ∀ r ∈ rs, (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ r = stk s₀) :
    bytesAt m' (outA s₀) (k * w.H.D) = bytesAt m (outA s₀) (k * w.H.D) := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have := keep_fr hf (R := ⟨outA s₀ + BitVec.ofNat 64 0, k * w.H.D⟩)
    (fun r hr => out_apart hp (by omega_using [hk]) (hw r hr)) (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
  simpa only [BitVec.add_zero] using this

end

/-! ## The copy of the inner state's hash value -/

theorem copyW_eq : copyW = (List.range 8).flatMap fun j =>
    ([.ldr .x .x9 .x19 (8 * j), .strSp .x9 (eW + 8 * j)] : List Instr) := rfl

/-- After `j` words of the copy. -/
structure CW (s₀ t : State) (j : Nat) (u : State) : Prop where
  mem : u.mem = writeBytes t.mem (sA s₀ eW) (bytesAt t.mem (keyA s₀) (8 * j))
  gpr : ∀ r, r ≠ .x9 → u.gpr r = t.gpr r
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  syms : u.syms = t.syms

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem copyW_step {t : State} (k : ER w s₀ t) {j : Nat} (hj : j < 8) {u : State} (hu : CW s₀ t j u) :
    WP isa (.block [.ldr .x .x9 .x19 (8 * j), .strSp .x9 (eW + 8 * j)]) u (CW s₀ t (j + 1)) := by
  have hfr := eFr_eq
  have hx19 : u.gpr .x19 = keyA s₀ := (hu.gpr _ (by decide)).trans k.x19
  refine wp_ldr (a := keyA s₀ + BitVec.ofNat 64 (8 * j)) ⟨by omega_using [], by omega_using [hj]⟩ (by rw [hx19])
    ⟨kyR s₀, List.mem_append_left _ (by rw [hu.rd, k.rd, hp.rd]; simp),
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩ fun u₁ v₁ => ?_
  refine wp_strSp (a := sA s₀ eW + BitVec.ofNat 64 (8 * j))
    ⟨by simp only [eW]; omega_using [], by simp only [eW]; omega_using [hj]⟩
    (by rw [v₁.sp, hu.sp, k.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
    (by rw [v₁.wr, hu.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact in_frw hp k.wr (by simp only [eW]; omega_using [hj, hfr])) fun u₂ v₂ => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [v₂.rd, v₁.rd, hu.rd], by rw [v₂.wr, v₁.wr, hu.wr], by rw [v₂.sp, v₁.sp, hu.sp],
    by rw [v₂.syms, v₁.syms, hu.syms]⟩
  · have hsep : Mem.Sep (keyA s₀) (8 * j + 8) (sA s₀ eW) (8 * j + 8) :=
      Region.Disjoint.sep ((hp.f_k.sub_left (Offset.sub_base _ (by simp only [eW]; omega_using [hj, hfr]))).sub_right
        (Region.sub_prefix (by omega_using [hj]))).symm (Region.contains_self _ _) (Region.contains_self _ _)
    have := VG.Proof.Hmac.Common.copy_mem t.mem (keyA s₀) (sA s₀ eW) j 8 hsep (by omega_using [hj])
    rw [v₂.mem, v₁.gpr, v₁.mem, hu.mem, Nat.mul_succ]
    simp only [Nat.reduceMul] at this
    exact this
  · rw [v₂.gpr, v₁.other r hr, hu.gpr r hr]

theorem copyW_gen {t : State} (k : ER w s₀ t) : ∀ n ≤ 8,
    WP isa (.block ((List.range n).flatMap fun j =>
      ([.ldr .x .x9 .x19 (8 * j), .strSp .x9 (eW + 8 * j)] : List Instr))) t (CW s₀ t n)
  | 0, _ => WP.block_nil ⟨by simp only [Nat.mul_zero]; rw [show bytesAt t.mem (keyA s₀) 0 = [] from rfl,
      writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyW_gen k n (by omega_using [hn])) fun u hu => copyW_step hp k (by omega_using [hn]) hu

omit hp in
/-- The working state, as the inner state at `key`, for each pseudorandom key. -/
theorem ws_of {t : State}
    (hc : ∀ i < 64, t.mem (sA s₀ eW + BitVec.ofNat 64 i) = s₀.mem (keyA s₀ + BitVec.ofNat 64 i)) :
    WS w s₀ t fun _ => [] := by
  intro prk hK
  rw [List.append_nil]
  refine reprN w (fun i hi => hc i (by have := w.ok.N_le; omega_using [this, hi])) ?_ hK.1
  rw [xorPad_length, blockKey_length, Nat.mod_self]

/-- The copy of the inner state at `key`'s hash value to the working state. -/
theorem copy_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) :
    WP isa (.block copyW) t fun u => BR w s₀ k u ∧ TB w s₀ k u ∧ WS w s₀ u (fun _ => []) := by
  have hfr := eFr_eq
  rw [copyW_eq]
  refine WP.mono (copyW_gen hp h.er 8 (Nat.le_refl _)) fun u hu => ?_
  have F : Frame [⟨sA s₀ eW, 64⟩] t.mem u.mem := by
    rw [hu.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have hwr' : Wk s₀ ⟨sA s₀ eW, 64⟩ := .inl ⟨eW, 64, rfl, by decide, by simp only [eW]; omega_using [hfr]⟩
  have hg : ∀ r ∈ bregs, u.gpr r = t.gpr r := fun r hr => hu.gpr r (by revert r; decide)
  have ku : ER w s₀ u := h.er.keep hp hu.rd hu.wr hu.sp hu.syms (fun r hr => hu.gpr r (by revert r; decide)) F
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwr')
  have hD := D_le w
  have hpl := pl_le w k
  refine ⟨h.keep ku hg (out_keep hp h.lt F fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl ⟨eW, 64, rfl, by decide, by simp only [eW]; omega_using [hfr]⟩),
    fun prk hK => ?_, ws_of fun i hi => ?_⟩
  · have hd : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ ⟨sA s₀ eW, 64⟩ :=
      Offset.disjoint _ (.inr (by simp only [eW, eT]; omega_using [])) (by simp only [eT]; omega_using [hpl, hD])
        (by simp only [eW]; omega_using [])
    have e := keep_fr F (R := ⟨sA s₀ eT, pl w k⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
      (by show pl w k ≤ 2 ^ 64; omega_using [hpl, hD])
    exact e.trans (ht prk hK)
  · have hl : (bytesAt t.mem (keyA s₀) (8 * 8)).length = 64 := bytesAt_length _ _ _
    have e1 := VG.Proof.Hmac.Common.writeBytes_at t.mem (sA s₀ eW) (bytesAt t.mem (keyA s₀) (8 * 8)) (i := i)
      (by rw [hl]; exact hi) (by rw [hl]; decide)
    have e2 := VG.Proof.Hmac.Common.bytesAt_getD' t.mem (keyA s₀) (n := 8 * 8) (i := i) (by omega_using [hi])
    have e3 := ER.keyB hp h.er (o := 0) (n := 64) (by decide) i hi
    rw [BitVec.add_zero] at e3
    rw [hu.mem, e1, e2, e3]

end

/-! ## The calls of a block -/

/-- What `update`'s arguments are, for `len` bytes at `dat`. -/
structure UA (w : MdHash) (s₀ : State) (dat : Addr) (len : Nat) (t : State) : Prop where
  x0 : t.gpr .x0 = sA s₀ eW
  x2 : t.gpr .x2 = dat
  x3 : (t.gpr .x3).toNat = len
  x4 : t.gpr .x4 = sA s₀ eWork
  d_w : Region.Disjoint ⟨dat, len⟩ (wR w s₀)
  d_s : Region.Disjoint ⟨dat, len⟩ ⟨sA s₀ eWork, w.ok.stream.Wb⟩
  d_b : Region.Disjoint (stk s₀) ⟨dat, len⟩
  cov : Covers [⟨dat, len⟩] (t.rd ++ t.wr)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem upd_args {k : Nat} {t t' : State} (h : BR w s₀ k t) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    {v : Addr} (u : Upd t t' .x16 v) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs w.ok.stream t' (sA s₀ eW) dat (sA s₀ eWork) len := by
  have g : ∀ r, r ≠ .x16 → t'.gpr r = t.gpr r := u.other
  have hb : below t'.sp 16 = stk s₀ := by rw [u.sp, h.er.sp]
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  have hfr := eFr_eq
  have hSS : w.H.stream.S = w.H.S := rfl
  exact
    { x0 := by rw [g _ (by decide), ha.x0]
      x2 := by rw [g _ (by decide), ha.x2]
      x3 := by rw [g _ (by decide), ha.x3]
      x4 := by rw [g _ (by decide), ha.x4]
      cd := by rw [u.rd, u.wr]; exact ha.cov
      cw := by
        rw [u.wr, h.er.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨frR s₀, by simp, eW, rfl, by dsimp only; simp only [eW]; omega_using [hSS, hS, hfr]⟩
        · exact ⟨frR s₀, by simp, eWork, rfl, by dsimp only; simp only [eWork]; omega_using [hWb, hfr]⟩
      st_sc := w_s hp hWb
      d_st := ha.d_w
      d_sc := ha.d_s
      sp16 := by rw [u.sp, h.er.sp]; exact hp.sp
      stk_st := by rw [hb]; exact stk_fr hp (by simp only [eW]; omega_using [hSS, hS, hfr])
      stk_d := by rw [hb]; exact ha.d_b
      stk_sc := by rw [hb]; exact stk_fr hp (by simp only [eWork]; omega_using [hWb, hfr]) }

/-- `update` with `len` bytes at `dat`, once the load of its address wrote
`x16`: the working state absorbs them, and `BR` and `T(k)` are kept. -/
theorem upd_step {k : Nat} {t t' : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) {m : List Byte → List Byte}
    (hw : WS w s₀ t m) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    (hc : t.gpr .x1 = BitVec.ofNat 64 (w.H.P.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) {v : Addr} (u : Upd t t' .x16 v) :
    WP isa (.call w.H.updN w.H.updC) t' fun u' => BR w s₀ k u' ∧ TB w s₀ k u' ∧
      WS w s₀ u' (fun prk => m prk ++ bytesAt t.mem dat len) := by
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  have hfr := eFr_eq
  have hSS : w.H.stream.S = w.H.S := rfl
  have hb : below t'.sp 16 = stk s₀ := by rw [u.sp, h.er.sp]
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call w.ok.stream (upd_args hp h ha u) fun s' a hu => ?_
  have hW : ∀ r ∈ ([⟨sA s₀ eW, w.H.stream.S⟩, ⟨sA s₀ eWork, w.ok.stream.Wb⟩] ++ [below t'.sp 16] :
      List Region), (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ r = stk s₀ :=
    fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl ⟨eW, _, rfl, by decide, by simp only [eW]; omega_using [hSS, hS, hfr]⟩
      · exact .inl ⟨eWork, _, rfl, by decide, by simp only [eWork]; omega_using [hWb, hfr]⟩
      · exact .inr hb
  have k' : ER w s₀ s' := (h.er.upd (by decide) u).keep hp a.rd a.wr a.sp a.syms
    (fun r hr => a.cs r (kregs_pres r hr).1 (kregs_pres r hr).2)
    a.frame fun r hr => (hW r hr).elim .inl fun h' => .inr (.inr h')
  have hm : t'.mem = t.mem := u.mem
  have apart : ∀ {R : Region}, R.Disjoint (wR w s₀) → R.Disjoint ⟨sA s₀ eWork, w.ok.stream.Wb⟩ →
      R.Disjoint (stk s₀) → R.len ≤ 2 ^ 64 → bytesAt s'.mem R.base R.len = bytesAt t.mem R.base R.len :=
    fun h₁ h₂ h₃ hl => (keep_fr a.frame (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · rw [hb]; exact h₃) hl).trans (by rw [hm])
  have hD := D_le w
  have hpl := pl_le w k
  refine ⟨h.keep k' (fun r hr => (a.cs r (bregs_pres r hr).1 (bregs_pres r hr).2).trans
      (u.other r (by revert r; decide))) ((out_keep hp h.lt a.frame hW).trans (by rw [hm])),
    fun prk hK => ?_, fun prk hK => ?_⟩
  · have d₁ : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (wR w s₀) :=
      Offset.disjoint _ (.inr (by simp only [eW, eT]; omega_using [hS])) (by simp only [eT]; omega_using [hpl, hD])
        (by simp only [eW]; omega_using [hS])
    have d₂ : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ ⟨sA s₀ eWork, w.ok.stream.Wb⟩ :=
      Offset.disjoint _ (.inl (by simp only [eT, eWork]; omega_using [hpl, hD])) (by simp only [eT]; omega_using [hpl, hD])
        (by simp only [eWork]; omega_using [hWb])
    have d₃ : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (stk s₀) :=
      (stk_fr hp (by simp only [eT]; omega_using [hpl, hD, hfr])).symm
    exact (apart d₁ d₂ d₃ (by show pl w k ≤ 2 ^ 64; omega_using [hpl, hD])).trans (ht prk hK)
  · have := hu _ (by rw [hm]; exact hw prk hK) (by
      rw [u.other _ (by decide), hc, List.length_append, xorPad_length, blockKey_length, hml prk])
    rwa [hm, List.append_assoc] at this

/-- `update` with `len` bytes at `dat`, through the table. -/
theorem upd_stage {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) {m : List Byte → List Byte}
    (hw : WS w s₀ t m) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    (hc : t.gpr .x1 = BitVec.ofNat 64 (w.H.P.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) :
    WP isa (tcall .x24 1 f.upd) t fun u' => BR w s₀ k u' ∧ TB w s₀ k u' ∧
      WS w s₀ u' (fun prk => m prk ++ bytesAt t.mem dat len) := by
  unfold tcall
  refine WP.seq (tload hp h.er (d := .x16) (o := 8 * 1) ⟨by decide, by decide⟩ fun t' u => WP.block_nil ?_)
  have hx16 : t'.gpr .x16 = s₀.syms w.H.updN := by rw [u.gpr]; exact hp.tmem.2.1
  refine WP.icalls_of_call (a := t'.gpr .x16) (n := w.H.updN) (c := w.H.updC) rfl ?_
    (upd_step hp h ht hw ha hc hml u)
  show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .x16) = _
  rw [hx16, u.syms, h.er.sy]; exact hp.tok.u

/-- The frame's part at `o` of `n` bytes, apart from the working state, its
working space and the stack below the frame, and covered by the regions. -/
theorem fr_ua {t : State} (k : ER w s₀ t) {o n : Nat} (h₁ : eW + w.H.S ≤ o) (h₂ : o + n ≤ eWork) :
    Region.Disjoint ⟨sA s₀ o, n⟩ (wR w s₀) ∧ Region.Disjoint ⟨sA s₀ o, n⟩ ⟨sA s₀ eWork, w.ok.stream.Wb⟩ ∧
      Region.Disjoint (stk s₀) ⟨sA s₀ o, n⟩ ∧ Covers [⟨sA s₀ o, n⟩] (t.rd ++ t.wr) := by
  have hfr := eFr_eq
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  refine ⟨Offset.disjoint _ (.inr h₁) (by simp only [eWork] at h₂; omega_using [h₂]) (by simp only [eW]; omega_using [hS]),
    Offset.disjoint _ (.inl h₂) (by simp only [eWork] at h₂; omega_using [h₂]) (by simp only [eWork]; omega_using [hWb]),
    stk_fr hp (by simp only [eWork] at h₂; omega_using [h₂, hfr]),
    VG.Covers.one (in_fr hp k.wr (by simp only [eWork] at h₂; omega_using [h₂, hfr]))⟩

end

/-- `update`'s arguments for `len` bytes at `dat`, the working state
holding `B + n` bytes (`m`). -/
structure AT (w : MdHash) (s₀ : State) (k : Nat) (dat : Addr) (len n : Nat) (m : List Byte → List Byte)
    (t : State) : Prop where
  br : BR w s₀ k t
  tb : TB w s₀ k t
  ws : WS w s₀ t m
  ua : UA w s₀ dat len t
  x1 : t.gpr .x1 = BitVec.ofNat 64 (w.H.P.B + n)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `update`'s arguments for `T(k)`. -/
theorem argsT_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) (hw : WS w s₀ t fun _ => []) :
    WP isa (.block updT) t (AT w s₀ k (sA s₀ eT) (pl w k) 0 fun _ => []) := by
  have hD := D_le w
  have hpl := pl_le w k
  have hS := hp.hw.hS
  unfold updT
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  refine tload hp (h.er.upd (by decide) u₁) (o := 40) ⟨by decide, by decide⟩ fun t₂ u₂ => wp_addSp (by decide)
    fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ => wp_addSp (by decide) fun t₅ u₅ => WP.block_nil ?_
  have k₅ : ER w s₀ t₅ := (((h.er.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃ |>.upd (by decide) u₄).upd
    (by decide) u₅
  have m₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g : ∀ r ∈ bregs, t₅.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  have h₅ : BR w s₀ k t₅ := h.keep k₅ g (by rw [m₅])
  obtain ⟨dw, ds, db, cov⟩ := fr_ua hp k₅ (o := eT) (n := pl w k) (by simp only [eW, eT]; omega_using [hS])
    (by simp only [eT, eWork]; omega_using [hpl, hD])
  have ua : UA w s₀ (sA s₀ eT) (pl w k) t₅ :=
    ⟨by upd_simp [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.er.sp],
      by upd_simp [u₅.other, u₄.other, u₃.gpr, u₂.sp, u₁.sp, h.er.sp],
      by upd_simp [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, h.x26, BitVec.add_zero]
         rw [BitVec.toNat_ofNat]; omega_using [hpl, hD],
      by upd_simp [u₅.gpr, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.er.sp],
      dw, ds, db, cov⟩
  exact ⟨h₅, fun prk hK => by rw [m₅]; exact ht prk hK, fun prk hK => by rw [m₅]; exact hw prk hK, ua,
    by upd_simp [u₅.other, u₄.other, u₃.other, u₂.gpr]; rw [hp.tB, Nat.add_zero]⟩

/-- What `update` with `T(k)` gives. -/
abbrev PT (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k)

theorem callT_ok {k : Nat} {t : State} (a : AT w s₀ k (sA s₀ eT) (pl w k) 0 (fun _ => []) t) :
    WP isa (tcall .x24 1 f.upd) t (PT w s₀ k) :=
  WP.mono (upd_stage hp a.br a.tb a.ws a.ua a.x1 (fun _ => rfl))
    fun _ ⟨hv, htv, hwv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [List.nil_append, a.tb prk hK] at this⟩

/-- `update` with `T(k)`. -/
theorem stageT_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) (hw : WS w s₀ t fun _ => []) :
    WP isa (.seq (.block updT) (tcall .x24 1 f.upd)) t (PT w s₀ k) :=
  WP.seq (WP.mono (argsT_ok hp h ht hw) fun _ a => callT_ok hp a)

/-- `update`'s arguments for `info`. -/
theorem argsI_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) :
    WP isa (.block updI) t
      (AT w s₀ k (infoA s₀) (infoLen s₀) (pl w k) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) := by
  unfold updI
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  refine tload hp (h.er.upd (by decide) u₁) (o := 40) ⟨by decide, by decide⟩ fun t₂ u₂ => wp_add fun t₃ u₃ =>
    wp_addImm (by decide) fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ => wp_addSp (by decide) fun t₆ u₆ =>
    WP.block_nil ?_
  have k₆ : ER w s₀ t₆ := ((((h.er.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃ |>.upd (by decide)
    u₄).upd (by decide) u₅).upd (by decide) u₆
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g : ∀ r ∈ bregs, t₆.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  have h₆ : BR w s₀ k t₆ := h.keep k₆ g (by rw [m₆])
  have ua : UA w s₀ (infoA s₀) (infoLen s₀) t₆ :=
    ⟨by upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.er.sp],
      by upd_simp [u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, h.er.x20, BitVec.add_zero],
      by upd_simp [u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, h.er.x21, BitVec.add_zero],
      by upd_simp [u₆.gpr, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.er.sp],
      hp.f_i.symm.sub_right (wR_sub hp), hp.f_i.symm.sub_right (workR hp.hw.hWb), hp.b_i,
      VG.Covers.one ⟨inR s₀, List.mem_append_left _ (by rw [k₆.rd, hp.rd]; simp), Region.contains_self _ _⟩⟩
  refine ⟨h₆, fun prk hK => by rw [m₆]; exact ht prk hK, fun prk hK => by rw [m₆]; exact hw prk hK, ua, ?_⟩
  upd_simp [u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.gpr, u₂.other, u₁.other, h.x26]
  rw [hp.tB, BitVec.ofNat_add_ofNat]

/-- What `update` with `info` gives. -/
abbrev PI (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀)

theorem callI_ok {k : Nat} {t : State}
    (a : AT w s₀ k (infoA s₀) (infoLen s₀) (pl w k) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) t) :
    WP isa (tcall .x24 1 f.upd) t (PI w s₀ k) :=
  WP.mono (upd_stage hp a.br a.tb a.ws a.ua (by rw [a.x1, tBlock_len]) (fun prk => by rw [tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.br.er.infoB hp] at this⟩

/-- `update` with `info`. -/
theorem stageI_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) :
    WP isa (.seq (.block updI) (tcall .x24 1 f.upd)) t (PI w s₀ k) :=
  WP.seq (WP.mono (argsI_ok hp h ht hw) fun _ a => callI_ok hp a)

omit hp in
theorem byte_eq (k : Nat) : (BitVec.ofNat 64 (k + 1)).setWidth 8 = BitVec.ofNat 8 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- The counter's byte stored in the frame; `update`'s arguments for it. -/
theorem argsC_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.block updC) t fun u =>
      AT w s₀ k (sA s₀ eC) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++
        infoOf s₀) u ∧ bytesAt u.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)] := by
  have hfr := eFr_eq
  have hD := D_le w
  have hpl := pl_le w k
  have hB := B_le w
  have hS := hp.hw.hS
  have hil := info_lt hp
  unfold updC
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  refine wp_strb (a := sA s₀ eC) (by decide) (by rw [u₁.gpr, BitVec.add_zero, h.er.sp])
    (by rw [u₁.wr]; exact in_frw hp h.er.wr (by simp only [eC]; omega_using [hfr])) fun t₂ m₂ => ?_
  have F₁ : Frame [cR s₀] t₁.mem t₂.mem := by
    rw [m₂.mem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have F : Frame [cR s₀] t.mem t₂.mem := by rw [← u₁.mem]; exact F₁
  have hwc : Wk s₀ (cR s₀) := .inl ⟨eC, 1, rfl, by decide, by simp only [eC]; omega_using [hfr]⟩
  have k₂ : ER w s₀ t₂ := (h.er.upd (by decide) u₁).keep hp m₂.rd m₂.wr m₂.sp m₂.syms (fun r _ => by rw [m₂.gpr])
    F₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwc)
  refine wp_addSp (by decide) fun t₃ u₃ => ?_
  refine tload hp (k₂.upd (by decide) u₃) (o := 40) ⟨by decide, by decide⟩ fun t₄ u₄ => wp_add fun t₅ u₅ =>
    wp_add fun t₆ u₆ => wp_movz fun t₇ u₇ => wp_addSp (by decide) fun t₈ u₈ => WP.block_nil ?_
  have k₈ : ER w s₀ t₈ := (((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide)
    u₆).upd (by decide) u₇).upd (by decide) u₈
  have m₈ : t₈.mem = t₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g : ∀ r ∈ bregs, t₈.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, m₂.gpr, u₁.other]
  have apart : ∀ {R : Region}, R.Disjoint (cR s₀) → R.len ≤ 2 ^ 64 →
      bytesAt t₈.mem R.base R.len = bytesAt t.mem R.base R.len := fun hd hl => by
    rw [m₈]; exact keep_fr F (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hk := h.lt
  have h₈ : BR w s₀ k t₈ := h.keep k₈ g (by
    rw [m₈]
    exact out_keep hp hk F fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨eC, 1, rfl, by decide, by simp only [eC]; omega_using [hfr]⟩)
  have tb : TB w s₀ k t₈ := fun prk hK => by
    have d : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (cR s₀) :=
      Offset.disjoint _ (.inl (by simp only [eT, eC]; omega_using [hpl, hD])) (by simp only [eT]; omega_using [hpl, hD])
        (by decide)
    exact (apart d (by show pl w k ≤ 2 ^ 64; omega_using [hpl, hD])).trans (ht prk hK)
  have ws : WS w s₀ t₈ fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ := fun prk hK => by
    rw [m₈]
    exact repr_keep (w := w) (m := t.mem) (fun i hi => F.bytes (R := wR w s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_c hp) (by show w.H.S ≤ 2 ^ 64; omega_using [hS]) hi)
      (hw prk hK)
  obtain ⟨dw, ds, db, cov⟩ := fr_ua hp k₈ (o := eC) (n := 1) (by simp only [eW, eC]; omega_using [hS])
    (by decide)
  have ua : UA w s₀ (sA s₀ eC) 1 t₈ :=
    ⟨by upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, m₂.sp, u₁.sp, h.er.sp],
      by upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, m₂.gpr, u₁.gpr, h.er.sp],
      by upd_simp [u₈.other, u₇.gpr]; rfl,
      by upd_simp [u₈.gpr, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, m₂.sp, u₁.sp, h.er.sp],
      dw, ds, db, cov⟩
  have hbyte : bytesAt t₈.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)] := by
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
    rw [m₈, m₂.mem, VG.Proof.RsaOaep.AArch64.write1_apply, ite_eq_left rfl, u₁.other _ (by decide), h.x25, byte_eq]
  refine ⟨⟨h₈, tb, ws, ua, ?_⟩, hbyte⟩
  upd_simp [u₈.other, u₇.other, u₆.gpr, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.other, m₂.gpr, u₁.other, h.x26,
    h.er.x21]
  rw [hp.tB]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (s₀.gpr .x2).toNat < 2 ^ 64 := (s₀.gpr .x2).isLt
  have hil' : infoLen s₀ = (s₀.gpr .x2).toNat := rfl
  omega_using [hB, hpl, hD, hil, hil', this]

/-- `update`'s arguments for the counter. -/
abbrev AC (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop :=
  AT w s₀ k (sA s₀ eC) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++
    infoOf s₀) u ∧ bytesAt u.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)]

/-- What `update` with the counter gives. -/
abbrev PC (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])

theorem callC_ok {k : Nat} {t : State} (a : AC w s₀ k t) : WP isa (tcall .x24 1 f.upd) t (PC w s₀ k) :=
  WP.mono (upd_stage hp a.1.br a.1.tb a.1.ws a.1.ua
      (by rw [a.1.x1, List.length_append, tBlock_len, bytesAt_length])
      (fun prk => by rw [List.length_append, List.length_append, tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.2] at this⟩

/-- `update` with the counter's byte, stored in the frame first. -/
theorem stageC_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.seq (.block updC) (tcall .x24 1 f.upd)) t (PC w s₀ k) :=
  WP.seq (WP.mono (argsC_ok hp h ht hw) fun _ a => callC_ok hp a)

end

/-! ## HMAC's `finalize` -/

theorem hF (w : MdHash) :
    Verified AArch64.target w.H.hmacFin (Proof.Pbkdf2.Md.AArch64.Calls.finG w.ok.SH w.H.W) :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_ok w.ok w.C (by rw [w.hSH, w.hW]; exact w.hmacFin.2.2)

theorem hFd (w : MdHash) : w.H.hmacFin.aarch64Depth ≤ 1 :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_fdepth w.ok.stream.finDepth w.ok.comp.noFrames

/-- `finalize`'s arguments. -/
structure FA (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop where
  x0 : t.gpr .x0 = sA s₀ eW
  x1 : t.gpr .x1 = keyA s₀ + BitVec.ofNat 64 192
  x2 : t.gpr .x2 = BitVec.ofNat 64 (w.H.P.B + (pl w k + infoLen s₀ + 1))
  x3 : t.gpr .x3 = sA s₀ eT
  x4 : t.gpr .x4 = sA s₀ eWork

/-- The outer state's region, within `key`. -/
abbrev ouR (w : MdHash) (s₀ : State) : Region := ⟨keyA s₀ + BitVec.ofNat 64 192, w.H.S⟩

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem ou_sub : Region.Sub (ouR w s₀) (kyR s₀) :=
  Offset.sub_base _ (by have hS := hp.hw.hS; omega_using [hS])

theorem fin_args {k : Nat} {t t' : State} (h : BR w s₀ k t) (ha : FA w s₀ k t) {v : Addr}
    (u : Upd t t' .x16 v) :
    Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := w.H) t' (sA s₀ eW) (keyA s₀ + BitVec.ofNat 64 192)
      (BitVec.ofNat 64 (w.H.P.B + (pl w k + infoLen s₀ + 1))) (sA s₀ eT) (sA s₀ eWork) := by
  have g : ∀ r, r ≠ .x16 → t'.gpr r = t.gpr r := u.other
  have hb : below t'.sp 16 = stk s₀ := by rw [u.sp, h.er.sp]
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hD := D_le w
  have hfr := eFr_eq
  exact
    { x0 := by rw [g _ (by decide), ha.x0]
      x1 := by rw [g _ (by decide), ha.x1]
      x2 := by rw [g _ (by decide), ha.x2]
      x3 := by rw [g _ (by decide), ha.x3]
      x4 := by rw [g _ (by decide), ha.x4]
      cr := by
        rw [u.rd, u.wr, h.er.rd, h.er.wr, hp.rd, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨kyR s₀, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩
      cw := by
        rw [u.wr, h.er.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨frR s₀, by simp, eW, rfl, by dsimp only; simp only [eW]; omega_using [hS, hfr]⟩
        · exact ⟨frR s₀, by simp, eT, rfl, by dsimp only; simp only [eT]; omega_using [hD, hfr]⟩
        · exact ⟨frR s₀, by simp, eWork, rfl, by dsimp only; simp only [eWork]; omega_using [hW, hfr]⟩
      i_u := (hp.f_k.sub_left (wR_sub hp)).sub_right (ou_sub hp)
      i_o := w_t hp
      i_s := w_s hp hW
      u_o := (hp.f_k.symm.sub_left (ou_sub hp)).sub_right tR_sub
      u_s := (hp.f_k.symm.sub_left (ou_sub hp)).sub_right (workR hW)
      o_s := t_s hW
      sp16 := by rw [u.sp, h.er.sp]; exact hp.sp
      stk_i := by rw [hb]; exact stk_fr hp (by simp only [eW]; omega_using [hS, hfr])
      stk_u := by rw [hb]; exact hp.b_k.sub_right (ou_sub hp)
      stk_o := by rw [hb]; exact stk_fr hp (by simp only [eT]; omega_using [hD, hfr])
      stk_s := by rw [hb]; exact stk_fr hp (by simp only [eWork]; omega_using [hW, hfr])
      scnw := by
        rw [sA_toNat hp (by simp only [eWork]; omega_using [hfr])]
        have := hp.top; simp only [eWork]; omega_using [hW, hfr, this] }

/-- `T(k + 1)` in the frame, for each pseudorandom key. -/
abbrev TF (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) w.H.D = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) (k + 1)

/-- `finalize`, once the load of its address wrote `x16`: `T(k + 1)`. -/
theorem fin_step {k : Nat} {t t' : State} (h : BR w s₀ k t) (ha : FA w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
    {v : Addr} (u : Upd t t' .x16 v) :
    WP isa (.call w.H.hmacFinN w.H.hmacFin) t' fun u' => BR w s₀ k u' ∧ TF w s₀ k u' := by
  have hfr := eFr_eq
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hD := D_le w
  have hb : below t'.sp 16 = stk s₀ := by rw [u.sp, h.er.sp]
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call w.ok (hF w) (hFd w) (fin_args hp h ha u) fun s' a hpost => ?_
  have hW' : ∀ r ∈ ([⟨sA s₀ eW, w.H.S⟩, ⟨sA s₀ eT, w.H.D⟩, ⟨sA s₀ eWork, 8 * w.H.W⟩] ++
      [below t'.sp 16] : List Region),
      (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ r = stk s₀ := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨eW, _, rfl, by decide, by simp only [eW]; omega_using [hS, hfr]⟩
    · exact .inl ⟨eT, _, rfl, by decide, by simp only [eT]; omega_using [hD, hfr]⟩
    · exact .inl ⟨eWork, _, rfl, by decide, by simp only [eWork]; omega_using [hW, hfr]⟩
    · exact .inr hb
  have k' : ER w s₀ s' := (h.er.upd (by decide) u).keep hp a.rd a.wr a.sp a.syms
    (fun r hr => a.cs r (kregs_pres r hr).1 (kregs_pres r hr).2)
    a.frame fun r hr => (hW' r hr).elim .inl fun h' => .inr (.inr h')
  have hm : t'.mem = t.mem := u.mem
  have hk := h.lt
  have hpl := pl_le w k
  have hil := info_lt hp
  refine ⟨h.keep k' (fun r hr => (a.cs r (bregs_pres r hr).1 (bregs_pres r hr).2).trans
    (u.other r (by revert r; decide))) ((out_keep hp hk a.frame hW').trans (by rw [hm])), fun prk hK => ?_⟩
  have hl : (k0 w prk).length = w.H.P.B := blockKey_length w prk
  have hou : w.ok.SH.Repr t.mem (keyA s₀ + BitVec.ofNat 64 192) (xorPad (k0 w prk) opad) :=
    repr_keep (w := w) (m := s₀.mem) (fun i hi => ER.keyB hp h.er (o := 192) (n := w.H.S)
      (by omega_using [hS]) i hi) hK.2
  have htl : (Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]).length =
      pl w k + infoLen s₀ + 1 := by
    rw [List.length_append, List.length_append, tBlock_len, bytesAt_length]; rfl
  exact hpost (k0 w prk) (Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
    hl (by rw [hl, htl]; omega_using [hil, hpl]) (by rw [hm]; exact hw prk hK) (by rw [htl])
    (by rw [hm]; exact hou)

/-- `finalize`'s arguments. -/
theorem argsF_ok {k : Nat} {t : State} (h : BR w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.block finT) t fun u => BR w s₀ k u ∧ FA w s₀ k u ∧
      WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) := by
  have hD := D_le w
  have hpl := pl_le w k
  have hB := B_le w
  have hil := info_lt hp
  unfold finT
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addImm (by decide) fun t₂ u₂ => ?_
  refine tload hp ((h.er.upd (by decide) u₁).upd (by decide) u₂) (o := 40) ⟨by decide, by decide⟩ fun t₃ u₃ =>
    wp_add fun t₄ u₄ => wp_add fun t₅ u₅ => wp_addImm (by decide) fun t₆ u₆ => wp_addSp (by decide) fun t₇ u₇ =>
    wp_addSp (by decide) fun t₈ u₈ => WP.block_nil ?_
  have k₈ : ER w s₀ t₈ := ((((((h.er.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide)
    u₄).upd (by decide) u₅).upd (by decide) u₆ |>.upd (by decide) u₇).upd (by decide) u₈
  have m₈ : t₈.mem = t.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g : ∀ r ∈ bregs, t₈.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  refine ⟨h.keep k₈ g (by rw [m₈]), ⟨?_, ?_, ?_, ?_, ?_⟩, fun prk hK => by rw [m₈]; exact hw prk hK⟩
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.er.sp]
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h.er.x19]
  · upd_simp [u₈.other, u₇.other, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₆.other, u₅.other, u₄.other, u₃.other,
      u₂.other, u₁.other, h.x26, h.er.x21]
    rw [hp.tB]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (s₀.gpr .x2).toNat < 2 ^ 64 := (s₀.gpr .x2).isLt
    have hil' : infoLen s₀ = (s₀.gpr .x2).toNat := rfl
    omega_using [hB, hpl, hD, hil, hil', this]
  · upd_simp [u₈.other, u₇.gpr, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.er.sp]
  · upd_simp [u₈.gpr, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.er.sp]

/-- `finalize` through the table. -/
theorem callF_ok {k : Nat} {t : State} (h : BR w s₀ k t) (fa : FA w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (tcall .x24 2 f.fin) t fun u => BR w s₀ k u ∧ TF w s₀ k u := by
  unfold tcall
  refine WP.seq (tload hp h.er (d := .x16) (o := 8 * 2) ⟨by decide, by decide⟩ fun t' u => WP.block_nil ?_)
  have hx16 : t'.gpr .x16 = s₀.syms w.H.hmacFinN := by rw [u.gpr]; exact hp.tmem.2.2
  refine WP.icalls_of_call (a := t'.gpr .x16) (n := w.H.hmacFinN) (c := w.H.hmacFin) rfl ?_ (fin_step hp h fa hw u)
  show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .x16) = _
  rw [hx16, u.syms, h.er.sy]; exact hp.tok.f

/-- `finalize`'s arguments, then `finalize` through the table. -/
theorem stageF_ok {k : Nat} {t : State} (h : BR w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.seq (.block finT) (tcall .x24 2 f.fin)) t fun u => BR w s₀ k u ∧ TF w s₀ k u :=
  WP.seq (WP.mono (argsF_ok hp h hw) fun _ ⟨hb, fa, hw'⟩ => callF_ok hp hb fa hw')

end

/-! ## The copy to `out` -/

/-- The bytes of `T(k + 1)` block `k + 1` writes to `out`. -/
abbrev nb (w : MdHash) (s₀ : State) (k : Nat) : Nat := min w.H.D (outLen s₀ - k * w.H.D)

theorem done_succ {w : MdHash} {s₀ : State} {k : Nat} (h : k * w.H.D < outLen s₀) :
    done w s₀ (k + 1) = k * w.H.D + nb w s₀ k := by
  unfold done nb; rw [Nat.succ_mul]; omega_using [h]

/-- The first `n` of `N` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n N : Nat} (h : n ≤ N) :
    bytesAt m p n = (bytesAt m p N).take n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

/-- What `csel` chooses after `subs`: `min(d, r)`. -/
theorem min_sel {d r : Nat} {c : Bool} (hc : c = decide (d ≤ r)) :
    (if c = true then BitVec.ofNat 64 d else BitVec.ofNat 64 r) = BitVec.ofNat 64 (min d r) := by
  subst hc
  by_cases h : d ≤ r
  · rw [ite_eq_left (decide_eq_true h), Nat.min_eq_left h]
  · rw [ite_eq_right (fun e => h (of_decide_eq_true e)), Nat.min_eq_right (by omega_using [h])]

/-- What `outArgs` leaves: the copy's arguments, `min(D, rem)` in `x13` and
`x14`. -/
structure OA (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop where
  br : BR w s₀ k u
  tf : TF w s₀ k u
  x11 : u.gpr .x11 = sA s₀ eT
  x12 : u.gpr .x12 = outA s₀ + BitVec.ofNat 64 (k * w.H.D)
  x13 : u.gpr .x13 = BitVec.ofNat 64 (nb w s₀ k)
  x14 : u.gpr .x14 = BitVec.ofNat 64 (nb w s₀ k)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `min(D, rem)`, and the copy's arguments. -/
theorem oA_ok {k : Nat} {t : State} (h : BR w s₀ k t) (hT : TF w s₀ k t) : WP isa (.block outArgs) t (OA w s₀ k) := by
  have hD := D_le w
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  unfold outArgs
  refine tload hp h.er (d := .x14) (o := 32) ⟨by decide, by decide⟩ fun t₁ u₁ => wp_subs fun t₂ u₂ hc₂ =>
    wp_cselHs fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ => wp_addSp (by decide) fun t₅ u₅ =>
    wp_addImm (by decide) fun t₆ u₆ => WP.block_nil ?_
  have h14 : t₁.gpr .x14 = BitVec.ofNat 64 w.H.D := by rw [u₁.gpr, hp.tD]
  have h23 : t₁.gpr .x23 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D) := by rw [u₁.other _ (by decide), h.x23]
  have hc : t₂.c = decide (w.H.D ≤ outLen s₀ - k * w.H.D) := by
    rw [hc₂, h14, h23, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w.H.D) (by omega_using [hD]),
      Nat.mod_eq_of_lt (a := outLen s₀ - k * w.H.D) (by omega_using [hol])]
  have x14 : t₃.gpr .x14 = BitVec.ofNat 64 (nb w s₀ k) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), h14, h23]; exact min_sel hc
  have k₆ : ER w s₀ t₆ := (((((h.er.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide)
    u₄).upd (by decide) u₅).upd (by decide) u₆
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g : ∀ r ∈ bregs, t₆.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  refine ⟨h.keep k₆ g (by rw [m₆]), fun prk hK => by rw [m₆]; exact hT prk hK, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₆.other, u₅.gpr, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.er.sp]
  · upd_simp [u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.x22, BitVec.add_zero]
  · upd_simp [u₆.other, u₅.other, u₄.gpr, BitVec.add_zero]; exact x14
  · upd_simp [u₆.other, u₅.other, u₄.other]; exact x14

/-- The copy of `nb` bytes of `T(k + 1)` to `out`, then the registers for
block `k + 2`. -/
theorem next_ok {k : Nat} {t : State} (h : OA w s₀ k t) :
    WP isa (.seq Impl.Ecdsa.Rfc6979.AArch64.Cfg.cpLoop (.block nextBlock)) t (EI w s₀ (k + 1)) := by
  have hfr := eFr_eq
  have hD := D_le w
  have hD0 := w.ok.sizes.D0
  have hk := h.br.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have hn0 : 0 < nb w s₀ k := by unfold nb; omega_using [hD0, hk]
  have hnD : nb w s₀ k ≤ w.H.D := Nat.min_le_left _ _
  have hnR : k * w.H.D + nb w s₀ k ≤ outLen s₀ := by unfold nb; omega_using [hk]
  have k₁ := h.br.er
  have dTO : ∀ {n : Nat}, n ≤ w.H.D →
      Region.Disjoint ⟨outA s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ ⟨sA s₀ eT, n⟩ := fun hn =>
    out_apart hp hnR (.inl ⟨eT, _, rfl, by decide, by simp only [eT]; omega_using [hn, hD, hfr]⟩)
  refine WP.seq (WP.mono (Proof.Ecdsa.Rfc6979.AArch64.cpRaw_ok (u₀ := t)
    (p := outA s₀ + BitVec.ofNat 64 (k * w.H.D)) (q := sA s₀ eT) (n := nb w s₀ k) hn0
    (by omega_using [hnD, hD])
    (by rw [k₁.wr, hp.wr]
        exact ⟨otR s₀, by simp, Offset.contains_base _ hnR (by omega_using [hnR, hol])⟩)
    (fun i hi => by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr hp k₁.wr (by simp only [eT]; omega_using [hi, hnD, hD, hfr]))
    (fun i hi hc => dTO (Nat.le_refl _) _ hc (Offset.contains_base _ (by omega_using [hi, hnD]) (by omega_using [hi, hnD, hD])))
    h.x11 h.x12 h.x13) fun t₂ I => ?_)
  have F : Frame [⟨outA s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩] t.mem t₂.mem := fun x hx => by
    rw [I.mem x, ite_eq_right (hx _ (List.mem_singleton_self _))]
  have hcp : bytesAt t₂.mem (outA s₀ + BitVec.ofNat 64 (k * w.H.D)) (nb w s₀ k) = bytesAt t.mem (sA s₀ eT) (nb w s₀ k) := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [I.mem, ite_eq_left (Offset.contains_base _ (d := i) (by omega_using [hi]) (by omega_using [hi, hnD, hD])),
      Offset.add_sub_cancel_left]
  have k₂ : ER w s₀ t₂ := k₁.keep hp I.rd I.wr I.sp I.syms
    (fun r hr => I.gpr r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) F
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub_base _ hnR)))
  unfold nextBlock
  refine wp_add fun t₃ u₃ => wp_sub fun t₄ u₄ => tload hp ((k₂.upd (by decide) u₃).upd (by decide) u₄) (o := 32)
    ⟨by decide, by decide⟩ fun t₅ u₅ => wp_addImm (by decide) fun t₆ u₆ => WP.block_nil ?_
  have k₆ : ER w s₀ t₆ := (((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆
  have m₆ : t₆.mem = t₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hds := done_succ (w := w) (s₀ := s₀) hk
  have hpl : pl w (k + 1) = w.H.D := by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
  have e14 : t₂.gpr .x14 = BitVec.ofNat 64 (nb w s₀ k) := by
    rw [I.gpr _ (by decide) (by decide) (by decide) (by decide), h.x14]
  refine ⟨k₆, ?_, ?_, ?_, ?_, fun prk hK => ?_, fun prk hK => ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e14,
      I.gpr _ (by decide) (by decide) (by decide) (by decide), h.br.x22, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hds]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), e14,
      I.gpr _ (by decide) (by decide) (by decide) (by decide), h.br.x23,
      Offset.ofNat_sub_ofNat (by omega_using [hnR]), hds]
    congr 1; omega_using [hnR]
  · rw [u₆.other _ (by decide), u₅.gpr, hp.tD, hpl]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      I.gpr _ (by decide) (by decide) (by decide) (by decide), h.br.x25, BitVec.ofNat_add_ofNat]
  · have hbl := Proof.Hkdf.blocks_length w.ok.SH.H prk (infoOf s₀) (hash_length w) k
    rw [hds, Proof.Hkdf.blocks_succ, List.take_append, List.take_of_length_le (by omega_using [hbl]),
      hbl, Nat.add_sub_cancel_left, VG.Proof.Hmac.Common.bytesAt_add, ← h.br.ob prk hK, m₆]
    congr 1
    · have := keep_fr F (R := ⟨outA s₀ + BitVec.ofNat 64 0, k * w.H.D⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hk, hol]) (by omega_using [hnR, hol]))
        (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
      simpa only [BitVec.add_zero] using this
    · rw [hcp, bytesAt_take _ _ hnD, h.tf prk hK]
  · rw [hpl, m₆, keep_fr F (R := ⟨sA s₀ eT, w.H.D⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dTO (Nat.le_refl _)).symm)
      (by show w.H.D ≤ 2 ^ 64; omega_using [hD])]
    exact h.tf prk hK

/-- After `finalize`: `min(D, rem)` bytes of `T(k + 1)` to `out`, then the
registers for block `k + 2`. -/
theorem out_ok {k : Nat} {t : State} (h : BR w s₀ k t) (hT : TF w s₀ k t) :
    WP isa (.seq (.block outArgs) (.seq Impl.Ecdsa.Rfc6979.AArch64.Cfg.cpLoop (.block nextBlock))) t
      (EI w s₀ (k + 1)) :=
  WP.seq (WP.mono (oA_ok hp h hT) fun _ a => next_ok hp a)

end

/-! ## The blocks -/

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

omit hp in
/-- While bytes of `out` are left, the state before block `k + 1` is one during it. -/
theorem ei_br {k : Nat} {t : State} (h : EI w s₀ k t) (hs : outLen s₀ - done w s₀ k ≠ 0) :
    BR w s₀ k t ∧ TB w s₀ k t := by
  have hlt : k * w.H.D < outLen s₀ := by
    refine Nat.lt_of_not_le fun hc => hs ?_
    rw [show done w s₀ k = outLen s₀ from Nat.min_eq_right hc, Nat.sub_self]
  have hd : done w s₀ k = k * w.H.D := Nat.min_eq_left (Nat.le_of_lt hlt)
  refine ⟨⟨h.er, by rw [h.x22, hd], by rw [h.x23, hd], h.x26, h.x25, hlt, fun prk hK => ?_⟩, h.tb⟩
  have := h.ob prk hK
  rw [hd] at this
  rw [this, List.take_of_length_le (by
    rw [Proof.Hkdf.blocks_length w.ok.SH.H prk (infoOf s₀) (hash_length w) k])]

omit hp in
theorem block_eq (f : Fns) : block f = .seq (.block copyW) (.seq (.seq (.block updT) (tcall .x24 1 f.upd))
    (.seq (.seq (.block updI) (tcall .x24 1 f.upd)) (.seq (.seq (.block updC) (tcall .x24 1 f.upd))
    (.seq (.seq (.block finT) (tcall .x24 2 f.fin)) (.seq (.block outArgs)
    (.seq Impl.Ecdsa.Rfc6979.AArch64.Cfg.cpLoop (.block nextBlock))))))) := rfl

/-- One block. -/
theorem block_ok {k : Nat} {t : State} (h : EI w s₀ k t) (hs : outLen s₀ - done w s₀ k ≠ 0) :
    WP isa (block f) t (EI w s₀ (k + 1)) := by
  obtain ⟨hb, ht⟩ := ei_br h hs
  rw [block_eq]
  refine WP.seq (WP.mono (copy_ok hp hb ht) fun t₁ ⟨b₁, h₁, w₁⟩ => ?_)
  refine WP.seq (WP.mono (stageT_ok hp b₁ h₁ w₁) fun t₂ ⟨b₂, h₂, w₂⟩ => ?_)
  refine WP.seq (WP.mono (stageI_ok hp b₂ h₂ w₂) fun t₃ ⟨b₃, h₃, w₃⟩ => ?_)
  refine WP.seq (WP.mono (stageC_ok hp b₃ h₃ w₃) fun t₄ ⟨b₄, h₄, w₄⟩ => ?_)
  refine WP.seq (WP.mono (stageF_ok hp b₄ w₄) fun t₅ ⟨b₅, h₅⟩ => ?_)
  exact out_ok hp b₅ h₅

omit hp in
theorem ofNat_bne {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = decide (x ≠ 0) := by
  have e : BitVec.ofNat 64 x = 0 ↔ x = 0 := ⟨fun e => by
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this, fun e => by rw [e]; rfl⟩
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, e, decide_eq_true_eq]

omit hp in
/-- Whether bytes of `out` are left, as the loop's condition reads it. -/
theorem eval_ne {k : Nat} {t : State} (h : EI w s₀ k t) :
    isa.eval (.nonzero .x .x23) t = some (decide (outLen s₀ - done w s₀ k ≠ 0)) := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  rw [VG.Proof.RsaOaep.AArch64.eval_nonzero, h.x23, ofNat_bne (by omega_using [hol])]

/-- The blocks, while bytes of `out` are left. -/
theorem loop_ok {k : Nat} {t : State} (h : EI w s₀ k t) (hs : outLen s₀ - done w s₀ k ≠ 0) :
    WP isa (.loop (block f) (.nonzero .x .x23)) t fun u => ∃ K, EI w s₀ K u ∧ outLen s₀ ≤ K * w.H.D := by
  have hD0 := w.ok.sizes.D0
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧ EI w s₀ j u ∧
    outLen s₀ - done w s₀ j ≠ 0) ?_ _ t ⟨k, rfl, h, hs⟩
  rintro n u ⟨j, rfl, hj, hu⟩
  have hlt := (ei_br hj hu).1.lt
  refine WP.mono (block_ok hp hj hu) fun v hv => ?_
  rw [eval_ne hv]
  by_cases e : outLen s₀ ≤ (j + 1) * w.H.D
  · refine .inl ⟨?_, j + 1, hv, e⟩
    rw [show done w s₀ (j + 1) = outLen s₀ from Nat.min_eq_right e, Nat.sub_self]; rfl
  · have hd : done w s₀ (j + 1) = (j + 1) * w.H.D := Nat.min_eq_left (by omega_using [e])
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    refine .inr ⟨?_, outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, e, hD0, hsm], j + 1, rfl, hv, ?_⟩
    · rw [hd, decide_eq_true (by omega_using [e] : outLen s₀ - (j + 1) * w.H.D ≠ 0)]
    · rw [hd]; omega_using [e]

omit hp in
theorem epi_eq : expandEpi = .addSp .x9 0 :: Spill.restoreCode .x9 eSaved := rfl

omit hp in
theorem main_eq (f : Fns) : expandMain f = .seq (.block expandPro)
    (.seq (.ite (.nonzero .x .x23) (.loop (block f) (.nonzero .x .x23)) (.block [])) (.block expandEpi)) := rfl

omit hp in
theorem restorable : Spill.Restorable .x9 eSaved := by decide

/-- The epilogue: our caller's registers restored. -/
theorem epi_ok {t : State} (k : ER w s₀ t) : WP isa (.block expandEpi) t fun u =>
    (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s₀.gpr r) ∧ u.sp = s₀.sp ∧ u.mem = t.mem := by
  have hfr := eFr_eq
  rw [epi_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  refine WP.mono (Spill.restore_wp (b := .x9) (B := s₀.sp) (by rw [u₁.gpr, k.sp, BitVec.add_zero]) (by decide)
    restorable (fun q hq => in_fr hp (u₁.wr.trans k.wr) (by have := saved_in q hq; omega_using [hfr, this]))
    (by rw [u₁.mem]; exact k.saved)) fun u hr => ⟨fun r hr' h30 => ?_, by rw [hr.sp, u₁.sp, k.sp],
      by rw [hr.mem, u₁.mem]⟩
  refine hr.gpr_of ?_
  by_cases hm : r ∈ eSaved.map Prod.fst
  · exact .inl hm
  refine .inr ?_
  rw [u₁.other _ (by rintro rfl; exact absurd hr' (by decide))]
  have : r = .x27 ∨ r = .x28 := by revert hm h30 hr'; revert r; decide
  rcases this with rfl | rfl
  · exact k.x27
  · exact k.x28

/-- The frame's body. -/
theorem main_ok : WP isa (expandMain f) s₀ fun u => (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s₀.gpr r) ∧
    u.sp = s₀.sp ∧ u.mem.read (sA s₀ eFr) 8 = s₀.gpr .x30 ∧ ∀ prk, Keyd w s₀ prk →
      bytesAt u.mem (outA s₀) (outLen s₀) =
        (Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) ((outLen s₀ + w.H.D - 1) / w.H.D) [] 1).take (outLen s₀) := by
  have hD0 := w.ok.sizes.D0
  rw [main_eq]
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => ?_)
  have hd0 : done w s₀ 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  refine WP.seq (WP.mono (Q := fun (u : State) => ∃ K, EI w s₀ K u ∧ outLen s₀ ≤ K * w.H.D)
    (WP.ite _ (eval_ne h₁) (fun ht => ?_) (fun he => ?_)) fun t₂ ⟨K, h₂, hK⟩ => ?_)
  · exact loop_ok hp h₁ (of_decide_eq_true ht)
  · refine WP.block_nil ⟨0, h₁, ?_⟩
    have := of_decide_eq_false he
    rw [hd0, Nat.sub_zero] at this
    rw [Decidable.not_not.mp this]; exact Nat.zero_le _
  refine WP.mono (epi_ok hp h₂.er) fun u ⟨hcs, hsp, hm⟩ => ⟨hcs, hsp, ?_, fun prk hk => ?_⟩
  · rw [hm, h₂.er.frame.read (r := pushR s₀) (by simp [Region.Contains]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.p_f
      · exact hp.p_o
      · exact hp.p_b) (by decide)]
    exact hp.ret
  · have hdK : done w s₀ K = outLen s₀ := Nat.min_eq_right hK
    have ob := h₂.ob prk hk
    rw [hdK] at ob
    rw [hm, ob]
    have hN : outLen s₀ ≤ (outLen s₀ + w.H.D - 1) / w.H.D * w.H.D := by
      have e₁ := Nat.div_add_mod (outLen s₀ + w.H.D - 1) w.H.D
      have e₂ := Nat.mod_lt (outLen s₀ + w.H.D - 1) hD0
      rw [Nat.mul_comm] at e₁
      omega_using [e₁, e₂, hD0]
    have tk := fun a b (ha : outLen s₀ ≤ a * w.H.D) =>
      Proof.Hkdf.blocks_take w.ok.SH.H prk (infoOf s₀) (hash_length w) (a := a) ha b
    rcases Nat.le_total K ((outLen s₀ + w.H.D - 1) / w.H.D) with hl | hl
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
      rw [hj, tk K j hK]
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
      rw [hj, tk _ j hN]

end

/-- `vg_hkdf_expand` meets `expandR` and keeps the callee-saved registers
and the stack pointer. -/
theorem expand_correct {w : MdHash} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (expandR w f ns eStack).pre s) :
    WP isa (expand f) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (expandR w f ns eStack).post s s' := by
  have p := pre_alloc hw hp
  have hS := stackAt s eFr (by have := hp.1; rw [eStack] at this; exact this)
  have hfr := eFr_eq
  have hnw := hS.nw
  have so : Region.Disjoint ⟨base s eFr, eStack⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ := hp.2.2.2.2.2.2.2.2.1
  have si : Region.Disjoint ⟨base s eFr, eStack⟩ ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ := hp.2.2.2.2.2.2.2.1
  have sk : Region.Disjoint ⟨base s eFr, eStack⟩ ⟨s.gpr .x0, 384⟩ := hp.2.2.2.2.2.2.1
  have hol : (s.gpr .x4).toNat ≤ 255 * w.H.D := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold expand framed
  refine WP.frameAlloc (by have := hp.1; rw [eStack_eq] at this; omega_using [this]) (by decide) ?_
    (WP.mono (main_ok p) fun t ⟨hcs, htsp, hret, hP⟩ m u hm => ?_)
  · rw [hS.push, toNat_addN (by omega_using [hnw, hfr])]; omega_using []
  have hfs : (freed eFr t).sp = s.sp - 16 := by
    show t.sp + BitVec.ofNat 64 eFr = _
    rw [htsp, ← sA_push hS]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun prk hK => ?_⟩
  · show ((freed eFr t).write .x .x30 ((freed eFr t).mem.read (freed eFr t).sp 8)).gpr r = _
    rw [RegUpd.gpr_write]
    have hread : (freed eFr t).mem.read (freed eFr t).sp 8 = s.gpr .x30 := by
      have hfs' : t.sp + BitVec.ofNat 64 eFr = sA (entered eFr s) eFr := by rw [htsp]
      simp only [freed]
      rw [hfs']; exact hret
    by_cases h30 : r = .x30
    · subst h30; simp only [ite_true, hread, BitVec.setWidth_eq]
    · simp only [h30, ite_false]
      exact hcs r hr h30
  · show (freed eFr t).sp + 16 = s.sp
    rw [hfs, BitVec.sub_add_cancel]
  -- The frames' release loses their bytes, which lie apart from `out`.
  have hbl : below s.sp (eFr + 16) = ⟨base s eFr + BitVec.ofNat 64 16, eFr + 16⟩ := by
    show (⟨s.sp - BitVec.ofNat 64 (eFr + 16), eFr + 16⟩ : Region) = _
    rw [Offset.sub_ofNat_eq s.sp (show eFr + 16 ≤ eFr + 32 by omega_using []),
      show eFr + 32 - (eFr + 16) = 16 from by omega_using []]
  have e : bytesAt m (s.gpr .x3) (s.gpr .x4).toNat = bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => hm.bytes (R := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hbl]
        exact (so.sub_left (Offset.sub_base _ (by omega_using [eStack_eq, eFr_eq]))).symm)
      (Nat.le_of_lt (BitVec.isLt _)) hi
  show Spec.Hkdf.expand _ _ _ _ _ = some (bytesAt m (s.gpr .x3) (s.gpr .x4).toNat)
  rw [e]
  -- The push wrote apart from `key` and `info`.
  have pf := entered_frame s
  have hpk : ∀ (o n : Nat), o + n ≤ 384 → ∀ i < n,
      (entered eFr s).mem (s.gpr .x0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
        s.mem (s.gpr .x0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o n hon i hi' => pf.bytes (R := ⟨s.gpr .x0 + BitVec.ofNat 64 o, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (sk.symm.sub_left (Offset.sub_base _ hon)).sub_right (push_sub hS))
      (by show n ≤ 2 ^ 64; omega_using [hon]) hi'
  have hK' : Keyd w (entered eFr s) prk := by
    have hS192 := hw.hS
    refine ⟨repr_keep (fun i hi' => ?_) hK.1, repr_keep (fun i hi' => hpk 192 w.H.S (by omega_using [hS192]) i hi') hK.2⟩
    have := hpk 0 w.H.S (by omega_using [hS192]) i hi'
    rwa [BitVec.add_zero] at this
  have hinfo : infoOf (entered eFr s) = bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => pf.bytes (R := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact si.symm.sub_right (push_sub hS)) (Nat.le_of_lt (BitVec.isLt _)) hi
  have := hP prk hK'
  rw [hinfo] at this
  rw [show bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = _ from this]
  unfold Spec.Hkdf.expand
  rw [ite_eq_right (Nat.not_lt.mpr hol)]
  rfl

/-! ## Constant time -/

theorem rel_wp {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun _ _ => True)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The indirect call of the table's function `j`, whose address `a` both
runs load. -/
theorem tcall_rel {Φ₁ Φ₂ : State → Prop} {j : Nat} {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} {a : Addr} (hcl : Ck [.x24] (.block [.ldr .x .x16 .x24 (8 * j)]))
    (hag : ∀ s s', Φ₁ s → Φ₂ s' → s.sp = s'.sp ∧ ∀ r ∈ [Reg.x24], s.gpr r = s'.gpr r)
    (hld₁ : ∀ t, Φ₁ t → WP isa (.block [.ldr .x .x16 .x24 (8 * j)]) t fun u => Upd t u .x16 a)
    (hld₂ : ∀ t, Φ₂ t → WP isa (.block [.ldr .x .x16 .x24 (8 * j)]) t fun u => Upd t u .x16 a)
    (hf₁ : ∀ t, Φ₁ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hf₂ : ∀ t, Φ₂ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hcall : RelCT isa (fun u u' => (∃ t, Φ₁ t ∧ Upd t u .x16 a) ∧ (∃ t', Φ₂ t' ∧ Upd t' u' .x16 a))
      (.call n c) fun _ _ => True) :
    RelCT isa (fun t t' => Φ₁ t ∧ Φ₂ t') (tcall .x24 j ts) fun _ _ => True := by
  unfold tcall
  refine (rel_agree (P₁ := Φ₁) (P₂ := Φ₂) (G₁ := fun u => ∃ t, Φ₁ t ∧ Upd t u .x16 a)
    (G₂ := fun u => ∃ t, Φ₂ t ∧ Upd t u .x16 a) hag hcl
    (fun s h => WP.mono (hld₁ s h) fun u v => ⟨s, h, v⟩)
    (fun s h => WP.mono (hld₂ s h) fun u v => ⟨s, h, v⟩)).seq ?_
  cases ts with
  | nil => exact RelCT.of_false fun s _ h => by obtain ⟨t, ht, -⟩ := h.1; simp at hf₁; exact hf₁ t ht
  | cons q ts =>
    refine RelCT.icalls_of_call hcall ?_
    rintro u u' ⟨⟨t, h, v⟩, ⟨t', h', v'⟩⟩
    refine ⟨a, by simp only [AArch64.icall, v.gpr], by simp only [AArch64.icall, v'.gpr], ?_, ?_,
      by simp only [AArch64.addrs]⟩
    · show (q :: ts).find? (fun q => u.syms q.1 == a) = _
      rw [v.syms]; exact hf₁ t h
    · show (q :: ts).find? (fun q => u'.syms q.1 == a) = _
      rw [v'.syms]; exact hf₂ t' h'

/-- The registers that hold public values from the prologue on. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

/-- The registers the copy to `out` and the next block's registers need. -/
abbrev cpRegs : List Reg := [.x11, .x12, .x13, .x24]

/-- The taint checks of the pieces of `vg_hkdf_expand` between the calls. -/
structure EChecks : Prop where
  pro : Ck [.x0, .x1, .x2, .x3, .x4, .x5] (.block expandPro)
  tl1 : Ck [.x24] (.block [.ldr .x .x16 .x24 (8 * 1)])
  tl2 : Ck [.x24] (.block [.ldr .x .x16 .x24 (8 * 2)])
  cp : Ck pubRegs (.block copyW)
  uT : Ck pubRegs (.block updT)
  uI : Ck pubRegs (.block updI)
  uC : Ck pubRegs (.block updC)
  fT : Ck pubRegs (.block finT)
  oA : Ck pubRegs (.block outArgs)
  ou : Ck cpRegs (.seq Impl.Ecdsa.Rfc6979.AArch64.Cfg.cpLoop (.block nextBlock))
  nil : Ck [] (.block [])
  epi : Ck [] (.block expandEpi)

theorem echecks : EChecks :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : MdHash) (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5], s₀.gpr r = s₀'.gpr r
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.H.hmacFinN = s₀'.syms w.H.hmacFinN

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- The load of the table's word `j`, the address of one of its functions. -/
theorem ld_ok {t : State} (k : ER w s₀ t) {j : Nat} (hj : 8 * j % 8 = 0 ∧ 8 * j + 8 ≤ 48) {a : Addr}
    (ha : s₀.mem.readW (tabA s₀ + BitVec.ofNat 64 (8 * j)) 64 = a) :
    WP isa (.block [.ldr .x .x16 .x24 (8 * j)]) t fun u => Upd t u .x16 a :=
  tload hp k hj fun t' u => WP.block_nil (by rw [← ha]; exact u)

end

section
variable {w : MdHash} {f : Fns} {s₀ s₀' : State} (hp : Pre w f s₀) (hp' : Pre w f s₀')
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
theorem ol_eq : outLen s₀ = outLen s₀' := congrArg BitVec.toNat (hq.regs .x4 (by simp))

omit hp hp' in
/-- During the same block, the two runs agree on the public registers. -/
theorem agB {k : Nat} {t t' : State} (h : BR w s₀ k t) (h' : BR w s₀' k t') :
    t.sp = t'.sp ∧ ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  refine ⟨by rw [h.er.sp, h'.er.sp, hq.sp], fun r hr => ?_⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.er.x19, h'.er.x19]; exact hq.regs .x0 (by simp)
  · rw [h.er.x20, h'.er.x20]; exact hq.regs .x1 (by simp)
  · rw [h.er.x21, h'.er.x21]; exact hq.regs .x2 (by simp)
  · rw [h.x22, h'.x22, show outA s₀ = outA s₀' from hq.regs .x3 (by simp)]
  · rw [h.x23, h'.x23, ol_eq hq]
  · rw [h.er.x24, h'.er.x24]; exact hq.regs .x5 (by simp)
  · rw [h.x25, h'.x25]
  · rw [h.x26, h'.x26]

omit hp hp' in
theorem ag24 {k : Nat} {t t' : State} (h : BR w s₀ k t) (h' : BR w s₀' k t') :
    t.sp = t'.sp ∧ ∀ r ∈ [Reg.x24], t.gpr r = t'.gpr r :=
  ⟨(agB hq h h').1, fun r hr => (agB hq h h').2 r (by simp at hr; subst hr; simp)⟩

omit hp hp' in
theorem agE {k : Nat} {t t' : State} (h : EI w s₀ k t) (h' : EI w s₀' k t') :
    isa.eval (.nonzero .x .x23) t = isa.eval (.nonzero .x .x23) t' := by
  rw [eval_ne h, eval_ne h']; simp only [done, ol_eq hq]

/-- One block leaks the same trace in both runs. -/
theorem block_rel (j : Nat) :
    RelCT isa (fun t t' => (EI w s₀ j t ∧ outLen s₀ - done w s₀ j ≠ 0) ∧ (EI w s₀' j t' ∧ outLen s₀' - done w s₀' j ≠ 0))
      (block f) fun u u' => EI w s₀ (j + 1) u ∧ EI w s₀' (j + 1) u' := by
  have kc := echecks
  have e0 := hq.regs .x0 (by simp); have e1 := hq.regs .x1 (by simp); have e2 := hq.regs .x2 (by simp)
  have esp := hq.sp
  have il : infoLen s₀ = infoLen s₀' := congrArg BitVec.toNat e2
  rw [block_eq]
  have r1 := rel_agree (P₁ := fun t => EI w s₀ j t ∧ outLen s₀ - done w s₀ j ≠ 0)
    (P₂ := fun t => EI w s₀' j t ∧ outLen s₀' - done w s₀' j ≠ 0)
    (G₁ := fun u => BR w s₀ j u ∧ TB w s₀ j u ∧ WS w s₀ u (fun _ => []))
    (G₂ := fun u => BR w s₀' j u ∧ TB w s₀' j u ∧ WS w s₀' u (fun _ => []))
    (rs := pubRegs) (fun t t' h h' => agB hq (ei_br h.1 h.2).1 (ei_br h'.1 h'.2).1) kc.cp
    (fun t h => copy_ok hp (ei_br h.1 h.2).1 (ei_br h.1 h.2).2)
    (fun t h => copy_ok hp' (ei_br h.1 h.2).1 (ei_br h.1 h.2).2)
  have r2 := rel_agree (P₁ := fun u => BR w s₀ j u ∧ TB w s₀ j u ∧ WS w s₀ u (fun _ => []))
    (P₂ := fun u => BR w s₀' j u ∧ TB w s₀' j u ∧ WS w s₀' u (fun _ => []))
    (G₁ := AT w s₀ j (sA s₀ eT) (pl w j) 0 fun _ => []) (G₂ := AT w s₀' j (sA s₀' eT) (pl w j) 0 fun _ => [])
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uT
    (fun t h => argsT_ok hp h.1 h.2.1 h.2.2) (fun t h => argsT_ok hp' h.1 h.2.1 h.2.2)
  have ld1 : ∀ {s : State} {t : State}, Pre w f s → ER w s t →
      WP isa (.block [.ldr .x .x16 .x24 (8 * 1)]) t fun u => Upd t u .x16 (s.syms w.H.updN) :=
    fun hp k => ld_ok hp k ⟨by decide, by decide⟩ hp.tmem.2.1
  have ld2 : ∀ {s : State} {t : State}, Pre w f s → ER w s t →
      WP isa (.block [.ldr .x .x16 .x24 (8 * 2)]) t fun u => Upd t u .x16 (s.syms w.H.hmacFinN) :=
    fun hp k => ld_ok hp k ⟨by decide, by decide⟩ hp.tmem.2.2
  have r3 : RelCT isa (fun t t' => AT w s₀ j (sA s₀ eT) (pl w j) 0 (fun _ => []) t ∧
      AT w s₀' j (sA s₀' eT) (pl w j) 0 (fun _ => []) t') (tcall .x24 1 f.upd)
      fun u u' => PT w s₀ j u ∧ PT w s₀' j u' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag24 hq a.br a'.br)
      (fun t a => ld1 hp a.br.er) (fun t a => by rw [hq.up]; exact ld1 hp' a.br.er)
      (fun t a => by rw [a.br.er.sy]; exact hp.tok.u) (fun t a => by rw [a.br.er.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨upd_args hp a.br a.ua v,
        by have := upd_args hp' a'.br a'.ua v'; simp only [sA] at this ⊢; rwa [← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.x1, a'.x1],
        by rw [v.sp, v'.sp, a.br.er.sp, a'.br.er.sp, esp]⟩))
      (fun t a => callT_ok hp a) (fun t a => callT_ok hp' a)
  have r4 := rel_agree (P₁ := PT w s₀ j) (P₂ := PT w s₀' j)
    (G₁ := AT w s₀ j (infoA s₀) (infoLen s₀) (pl w j) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j)
    (G₂ := AT w s₀' j (infoA s₀') (infoLen s₀') (pl w j) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uI
    (fun t h => argsI_ok hp h.1 h.2.1 h.2.2) (fun t h => argsI_ok hp' h.1 h.2.1 h.2.2)
  have r5 : RelCT isa (fun t t' =>
      AT w s₀ j (infoA s₀) (infoLen s₀) (pl w j) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j) t ∧
      AT w s₀' j (infoA s₀') (infoLen s₀') (pl w j) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j) t')
      (tcall .x24 1 f.upd) fun u u' => PI w s₀ j u ∧ PI w s₀' j u' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag24 hq a.br a'.br)
      (fun t a => ld1 hp a.br.er) (fun t a => by rw [hq.up]; exact ld1 hp' a.br.er)
      (fun t a => by rw [a.br.er.sy]; exact hp.tok.u) (fun t a => by rw [a.br.er.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨upd_args hp a.br a.ua v,
        by have := upd_args hp' a'.br a'.ua v'; simp only [sA, infoA, infoLen] at this ⊢
           rwa [← esp, ← e1, ← e2] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.x1, a'.x1],
        by rw [v.sp, v'.sp, a.br.er.sp, a'.br.er.sp, esp]⟩))
      (fun t a => callI_ok hp a) (fun t a => callI_ok hp' a)
  have r6 := rel_agree (P₁ := PI w s₀ j) (P₂ := PI w s₀' j) (G₁ := AC w s₀ j) (G₂ := AC w s₀' j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uC
    (fun t h => argsC_ok hp h.1 h.2.1 h.2.2) (fun t h => argsC_ok hp' h.1 h.2.1 h.2.2)
  have r7 : RelCT isa (fun t t' => AC w s₀ j t ∧ AC w s₀' j t') (tcall .x24 1 f.upd)
      fun u u' => PC w s₀ j u ∧ PC w s₀' j u' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag24 hq a.1.br a'.1.br)
      (fun t a => ld1 hp a.1.br.er) (fun t a => by rw [hq.up]; exact ld1 hp' a.1.br.er)
      (fun t a => by rw [a.1.br.er.sy]; exact hp.tok.u) (fun t a => by rw [a.1.br.er.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨upd_args hp a.1.br a.1.ua v,
        by have := upd_args hp' a'.1.br a'.1.ua v'; simp only [sA] at this ⊢; rwa [← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.1.x1, a'.1.x1, il],
        by rw [v.sp, v'.sp, a.1.br.er.sp, a'.1.br.er.sp, esp]⟩))
      (fun t a => callC_ok hp a) (fun t a => callC_ok hp' a)
  have r8 := rel_agree (P₁ := PC w s₀ j) (P₂ := PC w s₀' j)
    (G₁ := fun u => BR w s₀ j u ∧ FA w s₀ j u ∧ WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j ++
      infoOf s₀ ++ [BitVec.ofNat 8 (j + 1)]))
    (G₂ := fun u => BR w s₀' j u ∧ FA w s₀' j u ∧ WS w s₀' u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j ++
      infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]))
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.fT
    (fun t h => argsF_ok hp h.1 h.2.2) (fun t h => argsF_ok hp' h.1 h.2.2)
  have r9 : RelCT isa (fun t t' =>
      (BR w s₀ j t ∧ FA w s₀ j t ∧ WS w s₀ t (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j ++
        infoOf s₀ ++ [BitVec.ofNat 8 (j + 1)])) ∧
      (BR w s₀' j t' ∧ FA w s₀' j t' ∧ WS w s₀' t' (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j ++
        infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]))) (tcall .x24 2 f.fin)
      fun u u' => (BR w s₀ j u ∧ TF w s₀ j u) ∧ (BR w s₀' j u' ∧ TF w s₀' j u') :=
    rel_wp (tcall_rel (a := s₀.syms w.H.hmacFinN) kc.tl2 (fun t t' a a' => ag24 hq a.1 a'.1)
      (fun t a => ld2 hp a.1.er) (fun t a => by rw [hq.hf]; exact ld2 hp' a.1.er)
      (fun t a => by rw [a.1.er.sy]; exact hp.tok.f) (fun t a => by rw [a.1.er.sy, hq.hf]; exact hp'.tok.f)
      (Proof.Pbkdf2.Md.AArch64.Pbk.hfin_rel w.ok (hF w) fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨fin_args hp a.1 a.2.1 v,
        by have := fin_args hp' a'.1 a'.2.1 v'; simp only [sA, keyA] at this ⊢; rwa [← esp, ← e0, ← il] at this,
        by rw [v.sp, v'.sp, a.1.er.sp, a'.1.er.sp, esp]⟩))
      (fun t a => callF_ok hp a.1 a.2.1 a.2.2) (fun t a => callF_ok hp' a.1 a.2.1 a.2.2)
  have rA := rel_agree (P₁ := fun u => BR w s₀ j u ∧ TF w s₀ j u) (P₂ := fun u => BR w s₀' j u ∧ TF w s₀' j u)
    (G₁ := OA w s₀ j) (G₂ := OA w s₀' j) (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.oA
    (fun t h => oA_ok hp h.1 h.2) (fun t h => oA_ok hp' h.1 h.2)
  have rC := rel_agree (P₁ := OA w s₀ j) (P₂ := OA w s₀' j)
    (G₁ := EI w s₀ (j + 1)) (G₂ := EI w s₀' (j + 1)) (rs := cpRegs)
    (fun t t' h h' => ⟨(agB hq h.br h'.br).1, fun r hr => by
      simp only [cpRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.x11, h'.x11]; simp only [sA, esp]
      · rw [h.x12, h'.x12, show outA s₀ = outA s₀' from hq.regs .x3 (by simp)]
      · rw [h.x13, h'.x13, show nb w s₀ j = nb w s₀' j by simp only [nb, ol_eq hq]]
      · exact (agB hq h.br h'.br).2 _ (by simp)⟩) kc.ou
    (fun t h => next_ok hp h) (fun t h => next_ok hp' h)
  exact r1.seq ((r2.seq r3).seq ((r4.seq r5).seq ((r6.seq r7).seq ((r8.seq r9).seq (rA.seq rC)))))

/-- The blocks leak the same trace in both runs. -/
theorem loop_rel {k : Nat} :
    RelCT isa (fun t t' => (EI w s₀ k t ∧ outLen s₀ - done w s₀ k ≠ 0) ∧ (EI w s₀' k t' ∧ outLen s₀' - done w s₀' k ≠ 0))
      (.loop (block f) (.nonzero .x .x23)) fun u u' => (∃ K, EI w s₀ K u) ∧ (∃ K, EI w s₀' K u') := by
  have hD0 := w.ok.sizes.D0
  refine (RelCT.loop (M := isa) (I := fun n (t t' : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧
      ((EI w s₀ j t ∧ outLen s₀ - done w s₀ j ≠ 0) ∧ (EI w s₀' j t' ∧ outLen s₀' - done w s₀' j ≠ 0)))
    (fun n => ?_) (outLen s₀ - k * w.H.D)).mono (fun t t' h => ⟨k, rfl, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hn : n = outLen s₀ - j * w.H.D
  · subst hn
    refine (block_rel hp hp' hq j).mono (fun t t' h => h.2) fun u u' ⟨hv, hv'⟩ => ?_
    have e := agE hq hv hv'
    refine ⟨e, fun _ => ⟨⟨_, hv⟩, ⟨_, hv'⟩⟩, fun hc => ?_⟩
    rw [eval_ne hv] at hc
    have hs : outLen s₀ - done w s₀ (j + 1) ≠ 0 := of_decide_eq_true (Option.some.inj hc)
    have hlt := (ei_br hv hs).1.lt
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    have hs' : outLen s₀' - done w s₀' (j + 1) ≠ 0 := by simp only [done, ← ol_eq hq]; exact hs
    exact ⟨outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, hsm, hD0], j + 1, rfl, ⟨hv, hs⟩, ⟨hv', hs'⟩⟩
  · exact RelCT.of_false fun _ _ h => hn h.1

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (expandMain f) fun _ _ => True := by
  have kc := echecks
  have esp := hq.sp
  rw [main_eq]
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := EI w s₀ 0) (G₂ := EI w s₀' 0)
    (rs := [.x0, .x1, .x2, .x3, .x4, .x5]) (fun s s' hs hs' => by subst hs hs'; exact ⟨hq.sp, hq.regs⟩) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => EI w s₀ 0 t ∧ EI w s₀' 0 t')
      (.ite (.nonzero .x .x23) (.loop (block f) (.nonzero .x .x23)) (.block []))
      fun u u' => (∃ K, EI w s₀ K u) ∧ (∃ K, EI w s₀' K u') := by
    refine RelCT.ite (fun t t' h => agE hq h.1 h.2) ?_ ?_
    · refine (loop_rel hp hp' hq (k := 0)).mono (fun t t' h => ?_) fun _ _ h => h
      obtain ⟨⟨h₁, h₂⟩, hc⟩ := h
      rw [eval_ne h₁] at hc
      have hs := of_decide_eq_true (Option.some.inj hc)
      exact ⟨⟨h₁, hs⟩, ⟨h₂, by simp only [done, ← ol_eq hq]; exact hs⟩⟩
    · exact (rel_agree (P₁ := EI w s₀ 0) (P₂ := EI w s₀' 0) (G₁ := fun u => ∃ K, EI w s₀ K u)
        (G₂ := fun u => ∃ K, EI w s₀' K u) (rs := [])
        (fun t t' h h' => ⟨by rw [h.er.sp, h'.er.sp, esp], by simp⟩)
        kc.nil (fun t h => WP.block_nil ⟨0, h⟩) (fun t h => WP.block_nil ⟨0, h⟩)).mono (fun t t' h => h.1)
        fun _ _ h => h
  have r3 := rel_agree (P₁ := fun u => ∃ K, EI w s₀ K u) (P₂ := fun u => ∃ K, EI w s₀' K u)
    (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [])
    (fun t t' ⟨_, k⟩ ⟨_, k'⟩ => ⟨by rw [k.er.sp, k'.er.sp, esp], by simp⟩) kc.epi
    (fun t ⟨_, k⟩ => WP.mono (epi_ok hp k.er) fun _ _ => trivial)
    (fun t ⟨_, k⟩ => WP.mono (epi_ok hp' k.er) fun _ _ => trivial)
  exact (r1.seq (r2.seq r3)).mono (fun _ _ h => h) fun _ _ _ => trivial

end

/-- `vg_hkdf_expand` is constant time: two runs whose public data agree
leak the same trace. -/
theorem expand_ct {w : MdHash} {f : Fns} {ns : List String} (hw : HOk w)
    (hns : ∀ n ∈ [w.H.updN, w.H.hmacFinN], n ∈ ns) :
    ConstantTime isa (expandR w f ns eStack).pre (expandR w f ns eStack).pub (expand f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc hw h; have hp' := pre_alloc hw h'
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, qn⟩ := hpub
  have hq : PubEq w (entered eFr e) (entered eFr e') :=
    ⟨show e.sp - 16 - BitVec.ofNat 64 eFr = e'.sp - 16 - BitVec.ofNat 64 eFr by rw [qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0, q1, q2, q3, q4, q5], qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (expand f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold expand framed
  refine RelCT.pushFrame (R := fun _ _ => True) (fun a b ⟨ha, hb⟩ => by rw [ha, hb, qsp]) ?_
  refine RelCT.alloc (R := fun _ _ => True) ((main_rel hp hp' hq).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨u', v', ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.AArch64.Expand
