module

public import VerifiedGarbage.Proof.Hkdf.X86_64.Extract
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Hkdf.X86_64

/-!
# HKDF on x86-64: `vg_hkdf_expand`, correct

The contract the proof is written against (`expandR`), for the table `hmac`
of one variant `w` (`MdHash`), whose functions an indirect call of `f`'s
reaches: `expand(key, info, info_len, out, out_len, hmac)` writes
HKDF-Expand's `out_len` bytes to `out`, for every pseudorandom key the
states at `key` are keyed with (`Spec.Hkdf.Keyed`). In its frame (`eFr`
bytes: the save area, which also holds `info` and its length, the working
state, `T(i)`, the counter's byte, then the working space), the prologue
saves our caller's registers and keeps `key`, `out`, the bytes of it left,
the table, the counter and the length of `T(i - 1)` in callee-saved
registers (`pro_ok`, from which on `ER` holds). Each block (`block_ok`)
makes the working state the inner state at `key` (a copy of its hash
value), absorbs `T(i - 1)`, `info` and the counter, finalizes with the outer
state at `key + 192` into `T(i)` in the frame, and copies its first
`min(D, rem)` bytes to `out`; before block `i + 1`, `out`'s first
`min(i D, L)` bytes are `T(1) ‖ … ‖ T(i)`'s (`EI`). The blocks run while
bytes of `out` are left (`loop_ok`), and the epilogue restores our caller's
registers.
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86_64.Expand

open VG.X86_64 VG.X86_64.Steps
open VG.Impl.Hkdf.X86_64
open VG.Impl.Mgf1.X86_64 (sp at_ ix byteLoop step)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (TabOK TabMem)
open VG.Proof.Hkdf.X86_64 (HOk ea_at ea_sp repr_keep)
open VG.Proof.Hkdf.X86_64.Extract (hF hFsp hFd blockKey_length)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame writeBytes_snoc)

/-- `expand(key, info, info_len, out, out_len, hmac)`, with `N` bytes of
stack, for the table `hmac` of `w`, whose functions an indirect call of `f`'s
reaches, with the addresses of the functions `ns` public. -/
def expandR (w : MdHash) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 384⟩
    let info : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let out : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let tab : Region := ⟨s.gpr .r9, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .rsp).toNat ∧ s.rd = [key, info, tab] ∧ s.wr = [out] ∧
      key.Disjoint out ∧ info.Disjoint out ∧ out.Disjoint tab ∧ ret.Disjoint out ∧
      stk.Disjoint key ∧ stk.Disjoint info ∧ stk.Disjoint out ∧ stk.Disjoint tab ∧
      (s.gpr .rdi).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat ≤ 255 * w.H.D ∧ TabMem w.H s.syms (s.gpr .r9) s.mem ∧
      s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B ∧ TabOK w.H f s.syms
  post s s' := ∀ prk, Spec.Hkdf.Keyed w.ok.SH s.mem (s.gpr .rdi) prk →
    Spec.Hkdf.expand w.ok.SH.H w.H.D prk (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (s.gpr .r8).toNat =
      some (bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_expand` uses: its frame, and below it the 32 bytes a
call of the table's functions uses. -/
def eStack : Nat := eFr + 32

theorem eFr_eq : eFr = 2200 := rfl
theorem eStack_eq : eStack = 2232 := rfl

section
variable (s₀ : State)

/-- An address in the frame, of the state on entry to the frame's body. -/
abbrev sA (o : Nat) : Addr := s₀.gpr .rsp + BitVec.ofNat 64 o

/-- The arguments, on entry to the frame's body. -/
abbrev key : Addr := s₀.gpr .rdi
abbrev info : Addr := s₀.gpr .rsi
abbrev infoLen : Nat := (s₀.gpr .rdx).toNat
abbrev out : Addr := s₀.gpr .rcx
abbrev outLen : Nat := (s₀.gpr .r8).toNat
abbrev tab : Addr := s₀.gpr .r9

abbrev frR : Region := ⟨s₀.gpr .rsp, eFr⟩
abbrev keyR : Region := ⟨key s₀, 384⟩
abbrev infoR : Region := ⟨info s₀, infoLen s₀⟩
abbrev outR : Region := ⟨out s₀, outLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩
abbrev retR : Region := ⟨sA s₀ eFr, 8⟩
/-- The stack below the frame that the calls use. -/
abbrev stk : Region := below (s₀.gpr .rsp) 32

/-- The regions the frame's body writes. -/
abbrev wrs : List Region := [frR s₀, outR s₀, stk s₀]

end

/-- The state the frame's body starts in. -/
structure Pre (w : MdHash) (f : Fns) (s₀ : State) : Prop where
  hw : HOk w
  rd : s₀.rd = [keyR s₀, infoR s₀, tabR s₀]
  wr : s₀.wr = [frR s₀, outR s₀]
  ol : outLen s₀ ≤ 255 * w.H.D
  k_o : (keyR s₀).Disjoint (outR s₀)
  i_o : (infoR s₀).Disjoint (outR s₀)
  o_t : (outR s₀).Disjoint (tabR s₀)
  r_o : (retR s₀).Disjoint (outR s₀)
  f_k : (frR s₀).Disjoint (keyR s₀)
  f_i : (frR s₀).Disjoint (infoR s₀)
  f_o : (frR s₀).Disjoint (outR s₀)
  f_t : (frR s₀).Disjoint (tabR s₀)
  b_k : (stk s₀).Disjoint (keyR s₀)
  b_i : (stk s₀).Disjoint (infoR s₀)
  b_o : (stk s₀).Disjoint (outR s₀)
  b_t : (stk s₀).Disjoint (tabR s₀)
  sp : 32 ≤ (s₀.gpr .rsp).toNat
  top : (s₀.gpr .rsp).toNat + eFr < 2 ^ 64
  nk : (key s₀).toNat + 384 ≤ 2 ^ 64
  ni : (info s₀).toNat + infoLen s₀ ≤ 2 ^ 64
  no : (out s₀).toNat + outLen s₀ ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w.H s₀.syms (tab s₀) s₀.mem
  tD : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B
  tok : TabOK w.H f s₀.syms

section
variable {w : MdHash} {f : Fns} {ns : List String}

theorem ret_eq (s : State) : sA (allocState eFr s) eFr = s.gpr .rsp := by
  rw [sA, allocState_rsp', BitVec.sub_add_cancel]

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hw : HOk w) (hp : (expandR w f ns eStack).pre s) : Pre w f (allocState eFr s) := by
  obtain ⟨hsp, hrd, hwr, ko, io, ot, ro, kk, ki, ko', kt, nk, ni, no, nt, hol, tm, td, tb, tok⟩ := hp
  have hspF : ((allocState eFr s).gpr .rsp).toNat = (s.gpr .rsp).toNat - eFr := by
    rw [allocState_rsp', BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat]; rw [eStack_eq] at hsp; rw [eFr_eq]; omega_using [hsp]),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [eFr_eq]; omega_using [])]
  obtain subF : Region.Sub (frR (allocState eFr s)) ⟨s.gpr .rsp - BitVec.ofNat 64 eStack, eStack⟩ := by
    rw [frR, allocState_rsp']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain subS : Region.Sub (stk (allocState eFr s)) ⟨s.gpr .rsp - BitVec.ofNat 64 eStack, eStack⟩ := by
    show Region.Sub ⟨(allocState eFr s).gpr .rsp - BitVec.ofNat 64 32, 32⟩ _
    rw [allocState_rsp', Offset.sub_sub_ofNat]
    exact Region.sub_prefix (by rw [eStack_eq]; omega_using [])
  have g : ∀ r, r ≠ .rsp → (allocState eFr s).gpr r = s.gpr r := fun r h => allocState_gpr' _ _ h
  have e0 := g .rdi (by decide); have e1 := g .rsi (by decide); have e2 := g .rdx (by decide)
  have e3 := g .rcx (by decide); have e4 := g .r8 (by decide); have e5 := g .r9 (by decide)
  rw [← ret_eq s] at ro
  refine ⟨hw, ?_, ?_, by simp only [outLen, e4]; exact hol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [keyR, infoR, outR, tabR, frR, stk, key, info, infoLen, out, outLen, tab, e0, e1, e2, e3, e4, e5]
  · show s.rd = _; rw [hrd]
  · show (_ : Region) :: s.wr = _; rw [hwr, allocState_rsp']
  · exact ko
  · exact io
  · exact ot
  · exact ro
  · exact kk.sub_left subF
  · exact ki.sub_left subF
  · exact ko'.sub_left subF
  · exact kt.sub_left subF
  · exact kk.sub_left subS
  · exact ki.sub_left subS
  · exact ko'.sub_left subS
  · exact kt.sub_left subS
  · rw [hspF]; rw [eStack_eq] at hsp; rw [eFr_eq]; omega_using [hsp]
  · rw [hspF]; rw [eStack_eq] at hsp; rw [eFr_eq]; have := (s.gpr .rsp).isLt; omega_using [hsp, this]
  · exact nk
  · exact ni
  · exact no
  · exact nt
  · exact tm
  · exact td
  · exact tb
  · exact tok

end

/-! ## What every piece keeps -/

/-- Where the prologue saves our caller's registers, `info` and its length. -/
def savedL : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40), (.rsi, 48), (.rdx, 56)]

/-- The registers the epilogue restores. -/
def restL : List (Reg × Nat) := [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

theorem saved_slots : Spill.Slots savedL := by decide

theorem saved_in : ∀ q ∈ savedL, q.2 + 8 ≤ 64 := by
  intro q hq
  simp only [savedL, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rest_sub : ∀ q ∈ restL, q ∈ savedL := by decide

/-- The registers and memory kept from the end of the prologue on. -/
structure ER (w : MdHash) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sy : t.syms = s₀.syms
  rsp : t.gpr .rsp = s₀.gpr .rsp
  rbx : t.gpr .rbx = key s₀
  r13 : t.gpr .r13 = tab s₀
  saved : Spill.Saved t.mem (s₀.gpr .rsp) s₀.gpr savedL
  frame : Frame (wrs s₀) s₀.mem t.mem

/-- A part of the frame after the save area, `out`, or the stack below the
frame that a call uses. -/
def Wk (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ Region.Sub r (outR s₀) ∨
    ∃ n, r = below (s₀.gpr .rsp) n ∧ n ≤ 32

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem Wk.ok {r : Region} (h : Wk s₀ r) :
    (∀ q ∈ savedL, Region.Disjoint ⟨Spill.slot (s₀.gpr .rsp) q.2, 8⟩ r) ∧ ∃ r' ∈ wrs s₀, Region.Sub r r' := by
  have hfr := eFr_eq
  have sv : ∀ q ∈ savedL, Region.Sub ⟨Spill.slot (s₀.gpr .rsp) q.2, 8⟩ (frR s₀) := fun q hq =>
    Offset.sub_base _ (by have := saved_in q hq; omega_using [hfr, this])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · refine ⟨fun q hq => Offset.disjoint _ (.inl (by have := saved_in q hq; omega_using [h₁, this]))
      (by have := saved_in q hq; omega_using [this]) (by omega_using [h₂, hfr]), _, by simp, Offset.sub_base _ h₂⟩
  · exact ⟨fun q hq => (hp.f_o.sub_left (sv q hq)).sub_right h, _, by simp, h⟩
  · have hb : Region.Sub (below (s₀.gpr .rsp) n) (stk s₀) := by
      show Region.Sub ⟨s₀.gpr .rsp - BitVec.ofNat 64 n, n⟩ ⟨s₀.gpr .rsp - BitVec.ofNat 64 32, 32⟩
      exact Offset.sub_below _ hn (by omega_using [hn])
    refine ⟨fun q hq => ?_, _, by simp, hb⟩
    exact Offset.disjoint_below (s₀.gpr .rsp) (n := n) (d := q.2) (k := 8)
      (by have := saved_in q hq; omega_using [this, hn])

theorem ER.keep {t t' : State} (h : ER w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsy : t'.syms = t.syms)
    (hg : ∀ r ∈ [Reg.rsp, .rbx, .r13], t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk s₀ r) : ER w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.sy, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r13, h.saved.frame hf fun q hq r hr => (Wk.ok hp (hw r hr)).1 q hq,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem ER.same {t t' : State} (h : ER w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsy : t'.syms = t.syms)
    (hg : ∀ r ∈ [Reg.rsp, .rbx, .r13], t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) : ER w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.sy, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r13, by rw [hm]; exact h.saved, by rw [hm]; exact h.frame⟩

omit hp in
theorem ER.upd {t t' : State} (h : ER w s₀ t) {d : Reg} (hd : d ∉ [Reg.rsp, .rbx, .r13]) {v : BitVec 64}
    (u : Upd t t' d v) : ER w s₀ t' :=
  h.same u.rd u.wr u.syms (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

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
    t.mem (key s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hs : Region.Sub ⟨key s₀ + BitVec.ofNat 64 o, n⟩ (keyR s₀) := Offset.sub_base _ hon
  exact hk.frame.bytes (R := ⟨key s₀ + BitVec.ofNat 64 o, n⟩) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_k.symm.sub_left hs
    · exact hp.k_o.sub_left hs
    · exact hp.b_k.symm.sub_left hs) (by show n ≤ 2 ^ 64; omega_using [hon]) hi

theorem ER.infoB {t : State} (hk : ER w s₀ t) :
    bytesAt t.mem (info s₀) (infoLen s₀) = bytesAt s₀.mem (info s₀) (infoLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_i.symm
    · exact hp.i_o
    · exact hp.b_i.symm) (Nat.le_of_lt (s₀.gpr .rdx).isLt)

/-- A word of the table is as on entry. -/
theorem ER.tabW {t : State} (hk : ER w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tabR s₀) (Offset.contains_base _ ho (by omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.f_t.symm
      · exact hp.o_t.symm
      · exact hp.b_t.symm) (by decide)

theorem tin {t : State} (hk : ER w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
  ⟨tabR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp), Offset.contains_base _ ho (by omega_using [ho])⟩

/-- An offset of the frame, as a number. -/
theorem sA_toNat {o : Nat} (ho : o ≤ eFr) : (sA s₀ o).toNat = (s₀.gpr .rsp).toNat + o := by
  have top := hp.top
  have hfr := eFr_eq
  rw [sA, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, hfr]),
    Nat.mod_eq_of_lt (by omega_using [ho, top, hfr])]

end


/-- `info` and its length, in the save area. -/
theorem ER.infoW {w : MdHash} {s₀ t : State} (hk : ER w s₀ t) : t.mem.readW (sA s₀ eInfo) 64 = info s₀ :=
  hk.saved (.rsi, 48) (by simp [savedL])

theorem ER.infoLenW {w : MdHash} {s₀ t : State} (hk : ER w s₀ t) :
    t.mem.readW (sA s₀ eInfoLen) 64 = s₀.gpr .rdx :=
  hk.saved (.rdx, 56) (by simp [savedL])

/-- The loads of the table's words. -/
theorem tload {w : MdHash} {f : Fns} {s₀ t : State} (hp : Pre w f s₀) (k : ER w s₀ t) {d : Reg} {o : Nat}
    (ho : o + 8 ≤ 48) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', Upd t t' d (s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64) → WP isa (.block is) t' Q) :
    WP isa (.block (.mov d (.mem (at_ .r13 o)) :: is)) t Q :=
  wp_movm (by rw [ea_at, k.r13]) (tin hp k ho) fun t' u => h t' (by rw [← k.tabW hp ho]; exact u)

/-! ## The loop's invariant -/

/-- The length of `T(k)`: none for `T(0)`, `D` after. -/
abbrev pl (w : MdHash) (k : Nat) : Nat := if k = 0 then 0 else w.H.D

/-- `info`. -/
abbrev infoOf (s₀ : State) : List Byte := bytesAt s₀.mem (info s₀) (infoLen s₀)

/-- The pseudorandom keys the states at `key` are keyed with. -/
abbrev Keyd (w : MdHash) (s₀ : State) (prk : List Byte) : Prop := Spec.Hkdf.Keyed w.ok.SH s₀.mem (key s₀) prk

/-- The bytes of `out` written after `k` blocks. -/
abbrev done (w : MdHash) (s₀ : State) (k : Nat) : Nat := min (k * w.H.D) (outLen s₀)

/-- Before block `k + 1`: the registers and memory kept, `out`'s first
`done` bytes, `T(k)` in the frame, the registers that count, and ZF set
when no bytes of `out` are left. -/
structure EI (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop where
  er : ER w s₀ t
  rbp : t.gpr .rbp = out s₀ + BitVec.ofNat 64 (done w s₀ k)
  r12 : t.gpr .r12 = BitVec.ofNat 64 (outLen s₀ - done w s₀ k)
  r15 : t.gpr .r15 = BitVec.ofNat 64 (pl w k)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (k + 1)
  zf : t.zf = some (BitVec.ofNat 64 (outLen s₀ - done w s₀ k) == 0)
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (out s₀) (done w s₀ k) =
    (Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) k [] 1).take (done w s₀ k)
  tb : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) (pl w k) = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k

/-! ## The prologue -/

theorem pro_eq : expandPro = Spill.saveCode .rsp savedL ++
    ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rcx), .mov .r12 (.reg .r8), .mov .r13 (.reg .r9),
      .mov32 .r14 (.imm 1), .mov32 .r15 (.imm 0), .alu .test .r12 (.reg .r12)] : List Instr) := rfl

theorem and_self_beq (x : BitVec 64) : (x &&& x == 0) = (x == 0) := by rw [BitVec.and_self]

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem pro_ok : WP isa (.block expandPro) s₀ (EI w s₀ 0) := by
  rw [pro_eq]
  have hfr := eFr_eq
  refine Spill.save_then .rsp savedL (fun q hq => in_frw hp rfl (by have := saved_in q hq; omega_using [hfr, this])) ?_
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ =>
    wp_mov32i fun t₅ u₅ => wp_mov32i fun t₆ u₆ => wp_test fun t₇ g₇ m₇ rd₇ wr₇ sy₇ zf₇ => WP.block_nil ?_
  have mm : t₇.mem = Spill.saveMem s₀.mem (s₀.gpr .rsp) s₀.gpr savedL := by
    rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hd0 : done w s₀ 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  have r12₆ : t₆.gpr .r12 = BitVec.ofNat 64 (outLen s₀) := by
    upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s₀.gpr .r8).isLt]
  have r12 : t₇.gpr .r12 = BitVec.ofNat 64 (outLen s₀) := by rw [g₇]; exact r12₆
  refine ⟨⟨by rw [rd₇, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [wr₇, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [sy₇, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₇]; upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; try rfl
  · rw [g₇]; upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; try rfl
  · rw [g₇]; upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; try rfl
  · rw [mm]; exact Spill.saveMem_saved _ _ _ savedL saved_slots
  · rw [mm]
    exact (Spill.saveMem_frame_base _ _ _ savedL saved_in (by decide)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨frR s₀, by simp, Region.sub_prefix (by omega_using [hfr])⟩
  · rw [g₇]; upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [hd0, BitVec.add_zero]; try rfl
  · rw [r12, hd0, Nat.sub_zero]
  · rw [g₇]; upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; try rfl
  · rw [g₇]; upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]; try rfl
  · rw [zf₇, r12₆, and_self_beq, hd0, Nat.sub_zero]
  · intro prk _; rw [hd0]; rfl
  · intro prk _; rfl

end

/-! ## A block -/

theorem hash_length (w : MdHash) (m : List Byte) : (w.ok.SH.H.hash m).length = w.H.D := by
  have := w.ok.hDN
  simp only [w.ok.hash, List.length_take, Proof.MdStream.Md.hash, w.ok.md.digest_length]
  omega_using [this]

theorem D_le (w : MdHash) : w.H.D ≤ 64 := by
  have h1 := w.ok.hDN; have h2 := w.ok.N_le; omega_using [h1, h2]

theorem B_le (w : MdHash) : w.H.P.B ≤ 128 := w.ok.B_le

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
  rbp : t.gpr .rbp = out s₀ + BitVec.ofNat 64 (k * w.H.D)
  r12 : t.gpr .r12 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D)
  r15 : t.gpr .r15 = BitVec.ofNat 64 (pl w k)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (k + 1)
  lt : k * w.H.D < outLen s₀
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (out s₀) (k * w.H.D) =
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
abbrev bregs : List Reg := [.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15]

theorem BR.keep {w : MdHash} {s₀ : State} {k : Nat} {t t' : State} (h : BR w s₀ k t) (he : ER w s₀ t')
    (hg : ∀ r ∈ bregs, t'.gpr r = t.gpr r)
    (hb : bytesAt t'.mem (out s₀) (k * w.H.D) = bytesAt t.mem (out s₀) (k * w.H.D)) : BR w s₀ k t' :=
  ⟨he, (hg _ (by simp)).trans h.rbp, (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r15,
    (hg _ (by simp)).trans h.r14, h.lt, fun prk hK => hb.trans (h.ob prk hK)⟩

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
theorem t_c : (tR w s₀).Disjoint (cR s₀) := by
  have hD := D_le w
  exact Offset.disjoint _ (.inl (by simp only [eT, eC]; omega_using [hD])) (by simp only [eT]; omega_using [hD])
    (by decide)

/-- The stack below the frame, apart from a part of the frame. -/
theorem stk_fr {o n : Nat} (h : o + n ≤ eFr + 8) : Region.Disjoint (stk s₀) ⟨sA s₀ o, n⟩ := by
  have top := hp.top
  have hfr := eFr_eq
  exact (Offset.disjoint_below (s₀.gpr .rsp) (n := 32) (d := o) (k := n) (by omega_using [h, top, hfr])).symm

omit hp in
/-- The stack a callee uses, within `stk`. -/
theorem below_stk {t : State} (ht : t.gpr .rsp = s₀.gpr .rsp) {n : Nat} (hn : n ≤ 32) :
    Region.Sub (below (t.gpr .rsp) n) (stk s₀) := by
  rw [ht]
  show Region.Sub ⟨s₀.gpr .rsp - BitVec.ofNat 64 n, n⟩ ⟨s₀.gpr .rsp - BitVec.ofNat 64 32, 32⟩
  exact Offset.sub_below _ hn (by omega_using [hn])

/-- `info` fits HMAC's count with a block of key, `T(i - 1)` and the counter. -/
theorem info_lt : w.H.P.B + w.H.D + infoLen s₀ + 1 < 2 ^ 64 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hp.f_i.symm hp.ni (by
    show (s₀.gpr .rsp).toNat + eFr ≤ 2 ^ 64; have := hp.top; omega_using [this])
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
    (hr' : (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ ∃ n, r = below (s₀.gpr .rsp) n ∧ n ≤ 32) :
    Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 o, n⟩ r := by
  have hs : Region.Sub ⟨out s₀ + BitVec.ofNat 64 o, n⟩ (outR s₀) := Offset.sub_base _ h
  rcases hr' with ⟨o', n', rfl, _, h₂⟩ | ⟨n', rfl, hn⟩
  · exact (hp.f_o.symm.sub_left hs).sub_right (Offset.sub_base _ h₂)
  · exact (hp.b_o.symm.sub_left hs).sub_right (below_stk (t := s₀) rfl hn)

/-- `out`'s first `k D` bytes, apart from `rs`, are kept. -/
theorem out_keep {k : Nat} (hk : k * w.H.D < outLen s₀) {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hw : ∀ r ∈ rs, (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ ∃ n, r = below (s₀.gpr .rsp) n ∧ n ≤ 32) :
    bytesAt m' (out s₀) (k * w.H.D) = bytesAt m (out s₀) (k * w.H.D) := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have := keep_fr hf (R := ⟨out s₀ + BitVec.ofNat 64 0, k * w.H.D⟩)
    (fun r hr => out_apart hp (by omega_using [hk]) (hw r hr)) (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
  simpa only [BitVec.add_zero] using this

end

/-! ## The copy of the inner state's hash value -/

theorem copyW_eq : copyW = (List.range 8).flatMap fun j =>
    [.mov .rax (.mem (at_ .rbx (8 * j))), .store (sp (eW + 8 * j)) .rax] := rfl

/-- After `j` words of the copy. -/
structure CW (s₀ t : State) (j : Nat) (u : State) : Prop where
  mem : u.mem = writeBytes t.mem (sA s₀ eW) (bytesAt t.mem (key s₀) (8 * j))
  gpr : ∀ r, r ≠ .rax → u.gpr r = t.gpr r
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  syms : u.syms = t.syms

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem copyW_step {t : State} (k : ER w s₀ t) {j : Nat} (hj : j < 8) {u : State} (hu : CW s₀ t j u) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (8 * j))), .store (sp (eW + 8 * j)) .rax]) u (CW s₀ t (j + 1)) := by
  have hfr := eFr_eq
  have hrbx : u.gpr .rbx = key s₀ := (hu.gpr _ (by decide)).trans k.rbx
  have hrsp : u.gpr .rsp = s₀.gpr .rsp := (hu.gpr _ (by decide)).trans k.rsp
  refine wp_movm (a := key s₀ + BitVec.ofNat 64 (8 * j)) (by rw [ea_at, hrbx])
    ⟨keyR s₀, List.mem_append_left _ (by rw [hu.rd, k.rd, hp.rd]; simp),
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩ fun u₁ v₁ => ?_
  refine wp_store (a := sA s₀ eW + BitVec.ofNat 64 (8 * j))
    (by rw [ea_sp, v₁.other _ (by decide), hrsp, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
    (by rw [v₁.wr, hu.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact in_frw hp k.wr (by simp only [eW]; omega_using [hj, hfr])) fun u₂ v₂ => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [v₂.rd, v₁.rd, hu.rd], by rw [v₂.wr, v₁.wr, hu.wr],
    by rw [v₂.syms, v₁.syms, hu.syms]⟩
  · have hsep : Mem.Sep (key s₀) (8 * j + 8) (sA s₀ eW) (8 * j + 8) :=
      Region.Disjoint.sep ((hp.f_k.sub_left (Offset.sub_base _ (by simp only [eW]; omega_using [hj, hfr]))).sub_right
        (Region.sub_prefix (by omega_using [hj]))).symm (Region.contains_self _ _) (Region.contains_self _ _)
    have := VG.Proof.Hmac.Common.copy_mem t.mem (key s₀) (sA s₀ eW) j 8 hsep (by omega_using [hj])
    rw [v₂.mem, v₁.gpr, v₁.mem, hu.mem, Nat.mul_succ]
    simp only [Nat.reduceMul] at this
    exact this
  · rw [v₂.gpr, v₁.other r hr, hu.gpr r hr]

theorem copyW_gen {t : State} (k : ER w s₀ t) : ∀ n ≤ 8,
    WP isa (.block ((List.range n).flatMap fun j =>
      [.mov .rax (.mem (at_ .rbx (8 * j))), .store (sp (eW + 8 * j)) .rax])) t (CW s₀ t n)
  | 0, _ => WP.block_nil ⟨by simp only [Nat.mul_zero]; rw [show bytesAt t.mem (key s₀) 0 = [] from rfl,
      writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyW_gen k n (by omega_using [hn])) fun u hu => copyW_step hp k (by omega_using [hn]) hu

omit hp in
/-- The working state, as the inner state at `key`, for each pseudorandom key. -/
theorem ws_of {t : State}
    (hc : ∀ i < 64, t.mem (sA s₀ eW + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 i)) :
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
  have ku : ER w s₀ u := h.er.keep hp hu.rd hu.wr hu.syms (fun r hr => hu.gpr r (by revert r; decide)) F
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwr')
  have hD := D_le w
  have hpl := pl_le w k
  refine ⟨h.keep ku hg (out_keep hp h.lt F fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨eW, 64, rfl, by decide, by simp only [eW]; omega_using [hfr]⟩),
    fun prk hK => ?_, ws_of fun i hi => ?_⟩
  · have hd : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ ⟨sA s₀ eW, 64⟩ :=
      Offset.disjoint _ (.inr (by simp only [eW, eT]; omega_using [])) (by simp only [eT]; omega_using [hpl, hD])
        (by simp only [eW]; omega_using [])
    have e := keep_fr F (R := ⟨sA s₀ eT, pl w k⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by show pl w k ≤ 2 ^ 64; omega_using [hpl, hD])
    exact e.trans (ht prk hK)
  · have hl : (bytesAt t.mem (key s₀) (8 * 8)).length = 64 := bytesAt_length _ _ _
    have e1 := VG.Proof.Hmac.Common.writeBytes_at t.mem (sA s₀ eW) (bytesAt t.mem (key s₀) (8 * 8)) (i := i)
      (by rw [hl]; exact hi) (by rw [hl]; decide)
    have e2 := VG.Proof.Hmac.Common.bytesAt_getD' t.mem (key s₀) (n := 8 * 8) (i := i) (by omega_using [hi])
    have e3 := ER.keyB hp h.er (o := 0) (n := 64) (by decide) i hi
    rw [BitVec.add_zero] at e3
    rw [hu.mem, e1, e2, e3]

end

/-! ## The calls of a block -/

theorem sxW : (BitVec.ofNat 32 eW).signExtend 64 = BitVec.ofNat 64 eW := by decide
theorem sxT : (BitVec.ofNat 32 eT).signExtend 64 = BitVec.ofNat 64 eT := by decide
theorem sxC : (BitVec.ofNat 32 eC).signExtend 64 = BitVec.ofNat 64 eC := by decide
theorem sxK : (BitVec.ofNat 32 eWork).signExtend 64 = BitVec.ofNat 64 eWork := by decide
theorem sx192 : (BitVec.ofNat 32 192).signExtend 64 = BitVec.ofNat 64 192 := by decide
theorem sx1 : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- What `update`'s arguments are, for `len` bytes at `dat`. -/
structure UA (w : MdHash) (s₀ : State) (dat : Addr) (len : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = sA s₀ eW
  rdx : t.gpr .rdx = dat
  rcx : (t.gpr .rcx).toNat = len
  r8 : t.gpr .r8 = sA s₀ eWork
  d_w : Region.Disjoint ⟨dat, len⟩ (wR w s₀)
  d_s : Region.Disjoint ⟨dat, len⟩ ⟨sA s₀ eWork, w.ok.stream.Wb⟩
  d_b : Region.Disjoint (stk s₀) ⟨dat, len⟩
  cov : Covers [⟨dat, len⟩] (t.rd ++ t.wr)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

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

theorem upd_args {k : Nat} {t t' : State} (h : BR w s₀ k t) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    {v : Addr} (u : Upd t t' .r11 v) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs w.ok.stream t' (sA s₀ eW) dat (sA s₀ eWork) len := by
  have g : ∀ r, r ≠ .r11 → t'.gpr r = t.gpr r := u.other
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide), h.er.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 16) (stk s₀) := below_stk sp' (by decide)
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  have hfr := eFr_eq
  have hSS : w.H.stream.S = w.H.S := rfl
  exact
    { rdi := by rw [g _ (by decide), ha.rdi]
      rdx := by rw [g _ (by decide), ha.rdx]
      rcx := by rw [g _ (by decide), ha.rcx]
      r8 := by rw [g _ (by decide), ha.r8]
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
      stk_st := (stk_fr hp (by simp only [eW]; omega_using [hSS, hS, hfr])).sub_left hb
      stk_d := ha.d_b.sub_left hb
      stk_sc := (stk_fr hp (by simp only [eWork]; omega_using [hWb, hfr])).sub_left hb }

/-- `update` with `len` bytes at `dat`, once the load of its address wrote
`r11`: the working state absorbs them, and `BR` and `T(k)` are kept. -/
theorem upd_step {k : Nat} {t t' : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) {m : List Byte → List Byte}
    (hw : WS w s₀ t m) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    (hc : t.gpr .rsi = BitVec.ofNat 64 (w.H.P.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) {v : Addr} (u : Upd t t' .r11 v) :
    WP isa (.call w.H.updN w.H.updC) t' fun u' => BR w s₀ k u' ∧ TB w s₀ k u' ∧
      WS w s₀ u' (fun prk => m prk ++ bytesAt t.mem dat len) := by
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  have hfr := eFr_eq
  have hSS : w.H.stream.S = w.H.S := rfl
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [u.other _ (by decide), h.er.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 16) (stk s₀) := below_stk sp' (by decide)
  have hlen : len ≤ 2 ^ 64 := by rw [← ha.rcx]; exact Nat.le_of_lt (t.gpr .rcx).isLt
  refine WP.of_syms <| Proof.Pbkdf2.Md.X86_64.Calls.upd_call w.ok.stream (upd_args hp h ha u) hlen
    fun s' a hu sy' => ?_
  have hW : ∀ r ∈ ([⟨sA s₀ eW, w.H.stream.S⟩, ⟨sA s₀ eWork, w.ok.stream.Wb⟩] ++ [below (t'.gpr .rsp) 16] :
      List Region), (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ ∃ n, r = below (s₀.gpr .rsp) n ∧ n ≤ 32 :=
    fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl ⟨eW, _, rfl, by decide, by simp only [eW]; omega_using [hSS, hS, hfr]⟩
      · exact .inl ⟨eWork, _, rfl, by decide, by simp only [eWork]; omega_using [hWb, hfr]⟩
      · exact .inr ⟨16, by rw [sp'], by decide⟩
  have k' : ER w s₀ s' := (h.er.upd (by decide) u).keep hp a.rd a.wr sy' (fun r hr => a.cs r (by revert r; decide))
    a.frame fun r hr => (hW r hr).elim .inl fun h' => .inr (.inr h')
  have hm : t'.mem = t.mem := u.mem
  have apart : ∀ {R : Region}, R.Disjoint (wR w s₀) → R.Disjoint ⟨sA s₀ eWork, w.ok.stream.Wb⟩ →
      R.Disjoint (stk s₀) → R.len ≤ 2 ^ 64 → bytesAt s'.mem R.base R.len = bytesAt t.mem R.base R.len :=
    fun h₁ h₂ h₃ hl => (keep_fr a.frame (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃.sub_right hb) hl).trans (by rw [hm])
  have hD := D_le w
  have hpl := pl_le w k
  refine ⟨h.keep k' (fun r hr => (a.cs r (by revert r; decide)).trans (u.other r (by revert r; decide)))
      ((out_keep hp h.lt a.frame hW).trans (by rw [hm])), fun prk hK => ?_, fun prk hK => ?_⟩
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
    (hc : t.gpr .rsi = BitVec.ofNat 64 (w.H.P.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) :
    WP isa (tcall .r13 1 f.upd) t fun u' => BR w s₀ k u' ∧ TB w s₀ k u' ∧
      WS w s₀ u' (fun prk => m prk ++ bytesAt t.mem dat len) := by
  unfold tcall
  refine WP.seq (tload hp h.er (d := .r11) (o := 8 * 1) (by decide) fun t' u => WP.block_nil ?_)
  have hr11 : t'.gpr .r11 = s₀.syms w.H.updN := by rw [u.gpr]; exact hp.tmem.2.1
  refine WP.icalls_of_call (a := t'.gpr .r11) (n := w.H.updN) (c := w.H.updC) rfl ?_ (upd_step hp h ht hw ha hc hml u)
  show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .r11) = _
  rw [hr11, u.syms, h.er.sy]; exact hp.tok.u

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
  rsi : t.gpr .rsi = BitVec.ofNat 64 (w.H.P.B + n)

theorem updT_eq : updT = [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 eW)),
    .mov .rsi (.mem (at_ .r13 40)), .mov .rdx (.reg .rsp), .alu .add .rdx (.imm (BitVec.ofNat 32 eT)),
    .mov .rcx (.reg .r15), .mov .r8 (.reg .rsp), .alu .add .r8 (.imm (BitVec.ofNat 32 eWork))] := rfl

theorem updI_eq : updI = [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 eW)),
    .mov .rsi (.mem (at_ .r13 40)), .alu .add .rsi (.reg .r15), .mov .rdx (.mem (sp eInfo)),
    .mov .rcx (.mem (sp eInfoLen)), .mov .r8 (.reg .rsp), .alu .add .r8 (.imm (BitVec.ofNat 32 eWork))] := rfl

theorem updC_eq : updC = [.store8 (sp eC) .r14, .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 eW)),
    .mov .rsi (.mem (at_ .r13 40)), .alu .add .rsi (.reg .r15), .alu .add .rsi (.mem (sp eInfoLen)),
    .mov .rdx (.reg .rsp), .alu .add .rdx (.imm (BitVec.ofNat 32 eC)), .mov32 .rcx (.imm 1), .mov .r8 (.reg .rsp),
    .alu .add .r8 (.imm (BitVec.ofNat 32 eWork))] := rfl

theorem finT_eq : finT = [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 eW)),
    .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 192)), .mov .rdx (.mem (at_ .r13 40)),
    .alu .add .rdx (.reg .r15), .alu .add .rdx (.mem (sp eInfoLen)), .alu .add .rdx (.imm 1),
    .mov .rcx (.reg .rsp), .alu .add .rcx (.imm (BitVec.ofNat 32 eT)), .mov .r8 (.reg .rsp),
    .alu .add .r8 (.imm (BitVec.ofNat 32 eWork))] := rfl

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `update`'s arguments for `T(k)`. -/
theorem argsT_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) (hw : WS w s₀ t fun _ => []) :
    WP isa (.block updT) t (AT w s₀ k (sA s₀ eT) (pl w k) 0 fun _ => []) := by
  have hfr := eFr_eq
  have hD := D_le w
  have hpl := pl_le w k
  have hS := hp.hw.hS
  rw [updT_eq]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => ?_
  have k₂ : ER w s₀ t₂ := (h.er.upd (by decide) u₁).upd (by decide) u₂
  refine tload hp k₂ (by decide) fun t₃ u₃ => wp_mov fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_mov fun t₆ u₆ =>
    wp_mov fun t₇ u₇ => wp_addi fun t₈ u₈ => WP.block_nil ?_
  have k₈ : ER w s₀ t₈ := (((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd
    (by decide) u₇).upd (by decide) u₈
  have m₈ : t₈.mem = t.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g : ∀ r ∈ bregs, t₈.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  have h₈ : BR w s₀ k t₈ := h.keep k₈ g (by rw [m₈])
  obtain ⟨dw, ds, db, cov⟩ := fr_ua hp k₈ (o := eT) (n := pl w k) (by simp only [eW, eT]; omega_using [hS])
    (by simp only [eT, eWork]; omega_using [hpl, hD])
  have ua : UA w s₀ (sA s₀ eT) (pl w k) t₈ :=
    ⟨by upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.gpr, h.er.rsp, sxW],
      by upd_simp [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, u₁.other, h.er.rsp, sxT],
      by upd_simp [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r15]
         rw [BitVec.toNat_ofNat]; omega_using [hpl, hD],
      by upd_simp [u₈.gpr, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.er.rsp, sxK],
      dw, ds, db, cov⟩
  exact ⟨h₈, fun prk hK => by rw [m₈]; exact ht prk hK, fun prk hK => by rw [m₈]; exact hw prk hK, ua,
    by upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr]; rw [hp.tB, Nat.add_zero]⟩

/-- What `update` with `T(k)` gives. -/
abbrev PT (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k)

theorem callT_ok {k : Nat} {t : State} (a : AT w s₀ k (sA s₀ eT) (pl w k) 0 (fun _ => []) t) :
    WP isa (tcall .r13 1 f.upd) t (PT w s₀ k) :=
  WP.mono (upd_stage hp a.br a.tb a.ws a.ua a.rsi (fun _ => rfl))
    fun _ ⟨hv, htv, hwv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [List.nil_append, a.tb prk hK] at this⟩

/-- `update` with `T(k)`. -/
theorem stageT_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) (hw : WS w s₀ t fun _ => []) :
    WP isa (.seq (.block updT) (tcall .r13 1 f.upd)) t (PT w s₀ k) :=
  WP.seq (WP.mono (argsT_ok hp h ht hw) fun _ a => callT_ok hp a)

/-- `update`'s arguments for `info`. -/
theorem argsI_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) :
    WP isa (.block updI) t
      (AT w s₀ k (info s₀) (infoLen s₀) (pl w k) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) := by
  have hfr := eFr_eq
  have hD := D_le w
  have hpl := pl_le w k
  have hB := B_le w
  rw [updI_eq]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => ?_
  have k₂ : ER w s₀ t₂ := (h.er.upd (by decide) u₁).upd (by decide) u₂
  refine tload hp k₂ (by decide) fun t₃ u₃ => wp_add fun t₄ u₄ => ?_
  have k₄ : ER w s₀ t₄ := (k₂.upd (by decide) u₃).upd (by decide) u₄
  have sp₄ : t₄.gpr .rsp = s₀.gpr .rsp := k₄.rsp
  refine wp_movm (a := sA s₀ eInfo) (by rw [ea_sp, sp₄]) (in_fr hp k₄.wr (by simp only [eInfo]; omega_using [hfr]))
    fun t₅ u₅ => ?_
  have k₅ : ER w s₀ t₅ := k₄.upd (by decide) u₅
  refine wp_movm (a := sA s₀ eInfoLen) (by rw [ea_sp, k₅.rsp]) (in_fr hp k₅.wr (by simp only [eInfoLen]; omega_using [hfr]))
    fun t₆ u₆ => wp_mov fun t₇ u₇ => wp_addi fun t₈ u₈ => WP.block_nil ?_
  have k₈ : ER w s₀ t₈ := (((k₅.upd (by decide) u₆).upd (by decide) u₇).upd (by decide) u₈)
  have m₈ : t₈.mem = t.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₅ : t₅.mem = t.mem := by rw [u₅.mem, m₄]
  have g : ∀ r ∈ bregs, t₈.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  have h₈ : BR w s₀ k t₈ := h.keep k₈ g (by rw [m₈])
  have ua : UA w s₀ (info s₀) (infoLen s₀) t₈ :=
    ⟨by upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.gpr, h.er.rsp, sxW],
      by upd_simp [u₈.other, u₇.other, u₆.other, u₅.gpr]; rw [m₄]; exact h.er.infoW,
      by upd_simp [u₈.other, u₇.other, u₆.gpr]; rw [m₅, h.er.infoLenW],
      by upd_simp [u₈.gpr, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.er.rsp, sxK],
      hp.f_i.symm.sub_right (wR_sub hp), hp.f_i.symm.sub_right (workR hp.hw.hWb), hp.b_i,
      VG.Covers.one ⟨infoR s₀, List.mem_append_left _ (by rw [k₈.rd, hp.rd]; simp), Region.contains_self _ _⟩⟩
  refine ⟨h₈, fun prk hK => by rw [m₈]; exact ht prk hK, fun prk hK => by rw [m₈]; exact hw prk hK, ua, ?_⟩
  upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₃.other, u₂.other, u₁.other, h.r15]
  rw [hp.tB, add_ofNat]

end

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- What `update` with `info` gives. -/
abbrev PI (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀)

theorem callI_ok {k : Nat} {t : State}
    (a : AT w s₀ k (info s₀) (infoLen s₀) (pl w k) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) t) :
    WP isa (tcall .r13 1 f.upd) t (PI w s₀ k) :=
  WP.mono (upd_stage hp a.br a.tb a.ws a.ua (by rw [a.rsi, tBlock_len]) (fun prk => by rw [tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.br.er.infoB hp] at this⟩

/-- `update` with `info`. -/
theorem stageI_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) :
    WP isa (.seq (.block updI) (tcall .r13 1 f.upd)) t (PI w s₀ k) :=
  WP.seq (WP.mono (argsI_ok hp h ht hw) fun _ a => callI_ok hp a)

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
  rw [updC_eq]
  refine wp_store8 (a := sA s₀ eC) (by rw [ea_sp, h.er.rsp]) (in_frw hp h.er.wr (by simp only [eC]; omega_using [hfr]))
    fun t₁ m₁ => ?_
  have F : Frame [cR s₀] t.mem t₁.mem := by
    rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hwc : Wk s₀ (cR s₀) := .inl ⟨eC, 1, rfl, by decide, by simp only [eC]; omega_using [hfr]⟩
  have k₁ : ER w s₀ t₁ := h.er.keep hp m₁.rd m₁.wr m₁.syms (fun r _ => by rw [m₁.gpr]) F
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwc)
  refine wp_mov fun t₂ u₂ => wp_addi fun t₃ u₃ => ?_
  have k₃ : ER w s₀ t₃ := (k₁.upd (by decide) u₂).upd (by decide) u₃
  refine tload hp k₃ (by decide) fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  have k₅ : ER w s₀ t₅ := (k₃.upd (by decide) u₄).upd (by decide) u₅
  refine wp_addm (a := sA s₀ eInfoLen) (by rw [ea_sp, k₅.rsp]) (in_fr hp k₅.wr (by simp only [eInfoLen]; omega_using [hfr]))
    fun t₆ u₆ => wp_mov fun t₇ u₇ => wp_addi fun t₈ u₈ => wp_mov32i fun t₉ u₉ => wp_mov fun t₁₀ u₁₀ =>
    wp_addi fun t₁₁ u₁₁ => WP.block_nil ?_
  have k₁₁ : ER w s₀ t₁₁ := (((((k₅.upd (by decide) u₆).upd (by decide) u₇).upd (by decide) u₈).upd (by decide)
    u₉).upd (by decide) u₁₀).upd (by decide) u₁₁
  have m₁₁ : t₁₁.mem = t₁.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have m₅ : t₅.mem = t₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r ∈ bregs, t₁₁.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
        u₂.other, m₁.gpr]
  have apart : ∀ {R : Region}, R.Disjoint (cR s₀) → R.len ≤ 2 ^ 64 →
      bytesAt t₁₁.mem R.base R.len = bytesAt t.mem R.base R.len := fun hd hl => by
    rw [m₁₁]; exact keep_fr F (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have h₁₁ : BR w s₀ k t₁₁ := h.keep k₁₁ g (by
    rw [m₁₁]
    exact out_keep hp hk F fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨eC, 1, rfl, by decide, by simp only [eC]; omega_using [hfr]⟩)
  have tb : TB w s₀ k t₁₁ := fun prk hK => by
    have d : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (cR s₀) :=
      Offset.disjoint _ (.inl (by simp only [eT, eC]; omega_using [hpl, hD])) (by simp only [eT]; omega_using [hpl, hD])
        (by decide)
    exact (apart d (by show pl w k ≤ 2 ^ 64; omega_using [hpl, hD])).trans (ht prk hK)
  have ws : WS w s₀ t₁₁ fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ := fun prk hK => by
    rw [m₁₁]
    exact repr_keep (w := w) (m := t.mem) (fun i hi => F.bytes (R := wR w s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_c hp) (by show w.H.S ≤ 2 ^ 64; omega_using [hS]) hi)
      (hw prk hK)
  obtain ⟨dw, ds, db, cov⟩ := fr_ua hp k₁₁ (o := eC) (n := 1) (by simp only [eW, eC]; omega_using [hS])
    (by decide)
  have ua : UA w s₀ (sA s₀ eC) 1 t₁₁ :=
    ⟨by upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.gpr,
        m₁.gpr, h.er.rsp, sxW],
      by upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
        m₁.gpr, h.er.rsp, sxC],
      by upd_simp [u₁₁.other, u₁₀.other, u₉.gpr]; rfl,
      by upd_simp [u₁₁.gpr, u₁₀.gpr, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
        m₁.gpr, h.er.rsp, sxK],
      dw, ds, db, cov⟩
  have hbyte : bytesAt t₁₁.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)] := by
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
    rw [m₁₁, m₁.mem, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, h.r14]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  refine ⟨⟨h₁₁, tb, ws, ua, ?_⟩, hbyte⟩
  upd_simp [u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.gpr, u₄.gpr, u₅.other, u₄.other,
    u₃.other, u₂.other, m₁.gpr, h.r15, m₅]
  rw [m₁.mem]
  have e : (t.mem.writeW (sA s₀ eC) ((t.gpr .r14).setWidth 8)).readW (sA s₀ eInfoLen) 64 = s₀.gpr .rdx := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact h.er.infoLenW
  rw [e, hp.tB, add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (s₀.gpr .rdx).toNat < 2 ^ 64 := (s₀.gpr .rdx).isLt
  have hil' : infoLen s₀ = (s₀.gpr .rdx).toNat := rfl
  omega_using [hB, hpl, hD, hil, hil', this]

/-- `update`'s arguments for the counter. -/
abbrev AC (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop :=
  AT w s₀ k (sA s₀ eC) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++
    infoOf s₀) u ∧ bytesAt u.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)]

/-- What `update` with the counter gives. -/
abbrev PC (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])

theorem callC_ok {k : Nat} {t : State} (a : AC w s₀ k t) : WP isa (tcall .r13 1 f.upd) t (PC w s₀ k) :=
  WP.mono (upd_stage hp a.1.br a.1.tb a.1.ws a.1.ua
      (by rw [a.1.rsi, List.length_append, tBlock_len, bytesAt_length])
      (fun prk => by rw [List.length_append, List.length_append, tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.2] at this⟩

/-- `update` with the counter's byte, stored in the frame first. -/
theorem stageC_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.seq (.block updC) (tcall .r13 1 f.upd)) t (PC w s₀ k) :=
  WP.seq (WP.mono (argsC_ok hp h ht hw) fun _ a => callC_ok hp a)

/-- `finalize`'s arguments. -/
structure FA (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = sA s₀ eW
  rsi : t.gpr .rsi = key s₀ + BitVec.ofNat 64 192
  rdx : t.gpr .rdx = BitVec.ofNat 64 (w.H.P.B + (pl w k + infoLen s₀ + 1))
  rcx : t.gpr .rcx = sA s₀ eT
  r8 : t.gpr .r8 = sA s₀ eWork

/-- The outer state's region, within `key`. -/
abbrev ouR (w : MdHash) (s₀ : State) : Region := ⟨key s₀ + BitVec.ofNat 64 192, w.H.S⟩

theorem ou_sub : Region.Sub (ouR w s₀) (keyR s₀) :=
  Offset.sub_base _ (by have hS := hp.hw.hS; omega_using [hS])

theorem fin_args {k : Nat} {t t' : State} (h : BR w s₀ k t) (ha : FA w s₀ k t) {v : Addr}
    (u : Upd t t' .r11 v) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := w.H) t' (sA s₀ eW) (key s₀ + BitVec.ofNat 64 192)
      (BitVec.ofNat 64 (w.H.P.B + (pl w k + infoLen s₀ + 1))) (sA s₀ eT) (sA s₀ eWork) := by
  have g : ∀ r, r ≠ .r11 → t'.gpr r = t.gpr r := u.other
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide), h.er.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 24) (stk s₀) := below_stk sp' (by decide)
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hD := D_le w
  have hfr := eFr_eq
  exact
    { rdi := by rw [g _ (by decide), ha.rdi]
      rsi := by rw [g _ (by decide), ha.rsi]
      rdx := by rw [g _ (by decide), ha.rdx]
      rcx := by rw [g _ (by decide), ha.rcx]
      r8 := by rw [g _ (by decide), ha.r8]
      cr := by
        rw [u.rd, u.wr, h.er.rd, h.er.wr, hp.rd, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨keyR s₀, by simp, 192, rfl, by dsimp only; omega_using [hS]⟩
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
      stk_i := (stk_fr hp (by simp only [eW]; omega_using [hS, hfr])).sub_left hb
      stk_u := (hp.b_k.sub_left hb).sub_right (ou_sub hp)
      stk_o := (stk_fr hp (by simp only [eT]; omega_using [hD, hfr])).sub_left hb
      stk_s := (stk_fr hp (by simp only [eWork]; omega_using [hW, hfr])).sub_left hb
      scnw := by
        rw [sA_toNat hp (by simp only [eWork]; omega_using [hfr])]
        have := hp.top; simp only [eWork]; omega_using [hW, hfr, this] }

/-- `T(k + 1)` in the frame, for each pseudorandom key. -/
abbrev TF (w : MdHash) (s₀ : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) w.H.D = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) (k + 1)

/-- `finalize`, once the load of its address wrote `r11`: `T(k + 1)`. -/
theorem fin_step {k : Nat} {t t' : State} (h : BR w s₀ k t) (ha : FA w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
    {v : Addr} (u : Upd t t' .r11 v) :
    WP isa (.call w.H.hmacFinN w.H.hmacFin) t' fun u' => BR w s₀ k u' ∧ TF w s₀ k u' := by
  have hfr := eFr_eq
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hD := D_le w
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [u.other _ (by decide), h.er.rsp]
  refine WP.of_syms <| Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call w.ok (hF w) (hFsp w) (hFd w) (fin_args hp h ha u)
    fun s' hrd hwr hcs hf hpost sy' => ?_
  have hW' : ∀ r ∈ ([⟨sA s₀ eW, w.H.S⟩, ⟨sA s₀ eT, w.H.D⟩, ⟨sA s₀ eWork, 8 * w.H.W⟩] ++
      [below (t'.gpr .rsp) 24] : List Region),
      (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 64 ≤ o ∧ o + n ≤ eFr) ∨ ∃ n, r = below (s₀.gpr .rsp) n ∧ n ≤ 32 := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨eW, _, rfl, by decide, by simp only [eW]; omega_using [hS, hfr]⟩
    · exact .inl ⟨eT, _, rfl, by decide, by simp only [eT]; omega_using [hD, hfr]⟩
    · exact .inl ⟨eWork, _, rfl, by decide, by simp only [eWork]; omega_using [hW, hfr]⟩
    · exact .inr ⟨24, by rw [sp'], by decide⟩
  have k' : ER w s₀ s' := (h.er.upd (by decide) u).keep hp hrd hwr sy' (fun r hr => hcs r (by revert r; decide))
    hf fun r hr => (hW' r hr).elim .inl fun h' => .inr (.inr h')
  have hm : t'.mem = t.mem := u.mem
  have hk := h.lt
  have hpl := pl_le w k
  have hil := info_lt hp
  refine ⟨h.keep k' (fun r hr => (hcs r (by revert r; decide)).trans (u.other r (by revert r; decide)))
    ((out_keep hp hk hf hW').trans (by rw [hm])), fun prk hK => ?_⟩
  have hl : (k0 w prk).length = w.H.P.B := blockKey_length w prk
  have hou : w.ok.SH.Repr t.mem (key s₀ + BitVec.ofNat 64 192) (xorPad (k0 w prk) opad) :=
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
  have hfr := eFr_eq
  have hD := D_le w
  have hpl := pl_le w k
  have hB := B_le w
  have hil := info_lt hp
  rw [finT_eq]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_addi fun t₄ u₄ => ?_
  have k₄ : ER w s₀ t₄ := (((h.er.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  refine tload hp k₄ (by decide) fun t₅ u₅ => wp_add fun t₆ u₆ => ?_
  have k₆ : ER w s₀ t₆ := (k₄.upd (by decide) u₅).upd (by decide) u₆
  refine wp_addm (a := sA s₀ eInfoLen) (by rw [ea_sp, k₆.rsp]) (in_fr hp k₆.wr (by simp only [eInfoLen]; omega_using [hfr]))
    fun t₇ u₇ => wp_addi fun t₈ u₈ => wp_mov fun t₉ u₉ => wp_addi fun t₁₀ u₁₀ => wp_mov fun t₁₁ u₁₁ =>
    wp_addi fun t₁₂ u₁₂ => WP.block_nil ?_
  have k₁₂ : ER w s₀ t₁₂ := ((((((k₆.upd (by decide) u₇).upd (by decide) u₈).upd (by decide) u₉).upd (by decide)
    u₁₀).upd (by decide) u₁₁).upd (by decide) u₁₂)
  have m₁₂ : t₁₂.mem = t.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g : ∀ r ∈ bregs, t₁₂.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other,
        u₃.other, u₂.other, u₁.other]
  refine ⟨h.keep k₁₂ g (by rw [m₁₂]), ⟨?_, ?_, ?_, ?_, ?_⟩, fun prk hK => by rw [m₁₂]; exact hw prk hK⟩
  · upd_simp [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other,
      u₃.other, u₂.gpr, u₁.gpr, h.er.rsp, sxW]
  · upd_simp [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.gpr,
      u₂.other, u₁.other, h.er.rbx, sx192]
  · upd_simp [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₈.other, u₇.other,
      u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r15, m₆, sx1]
    rw [h.er.infoLenW, hp.tB, add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (s₀.gpr .rdx).toNat < 2 ^ 64 := (s₀.gpr .rdx).isLt
    have hil' : infoLen s₀ = (s₀.gpr .rdx).toNat := rfl
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]
    omega_using [hB, hpl, hD, hil, hil', this]
  · upd_simp [u₁₂.other, u₁₁.other, u₁₀.gpr, u₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
      u₂.other, u₁.other, h.er.rsp, sxT]
  · upd_simp [u₁₂.gpr, u₁₁.gpr, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
      u₂.other, u₁.other, h.er.rsp, sxK]

/-- `finalize` through the table. -/
theorem callF_ok {k : Nat} {t : State} (h : BR w s₀ k t) (fa : FA w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (tcall .r13 2 f.fin) t fun u => BR w s₀ k u ∧ TF w s₀ k u := by
  unfold tcall
  refine WP.seq (tload hp h.er (d := .r11) (o := 8 * 2) (by decide) fun t' u => WP.block_nil ?_)
  have hr11 : t'.gpr .r11 = s₀.syms w.H.hmacFinN := by rw [u.gpr]; exact hp.tmem.2.2
  refine WP.icalls_of_call (a := t'.gpr .r11) (n := w.H.hmacFinN) (c := w.H.hmacFin) rfl ?_ (fin_step hp h fa hw u)
  show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .r11) = _
  rw [hr11, u.syms, h.er.sy]; exact hp.tok.f

/-- `finalize`'s arguments, then `finalize` through the table. -/
theorem stageF_ok {k : Nat} {t : State} (h : BR w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.seq (.block finT) (tcall .r13 2 f.fin)) t fun u => BR w s₀ k u ∧ TF w s₀ k u :=
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

theorem ea_ix1 (s : State) (b i : Reg) (d : Nat) : s.ea (ix b i d) = s.gpr b + s.gpr i + BitVec.ofNat 64 d := by
  simp only [State.ea, ix, BitVec.ofInt_natCast, BitVec.mul_one]

theorem ofNat_sub {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [hb, ha]

theorem setWidth_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega_using [this]

/-- What the copy leaves, from `t`: `nb` bytes of `T` at `O`. -/
structure OC (t : State) (O T : Addr) (j : Nat) (v : State) : Prop where
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  gpr : ∀ r, r ≠ .r8 → r ≠ .rdx → v.gpr r = t.gpr r
  mem : v.mem = writeBytes t.mem O (bytesAt t.mem T j)
  rd : v.rd = t.rd
  wr : v.wr = t.wr
  syms : v.syms = t.syms

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `min(D, rem)` into `rax`. -/
theorem outLen_ok {k : Nat} {t : State} (h : BR w s₀ k t) :
    WP isa Impl.Hkdf.X86_64.outLen t fun u => u.gpr .rax = BitVec.ofNat 64 (nb w s₀ k) ∧ (∀ r, r ≠ .rax → u.gpr r = t.gpr r) ∧
      u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.syms = t.syms := by
  have hD := D_le w
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  unfold Impl.Hkdf.X86_64.outLen
  refine WP.seq (tload hp h.er (by decide) fun t₁ u₁ => wp_cmp fun t₂ g₂ m₂ rd₂ wr₂ sy₂ cf₂ _ => WP.block_nil ?_)
  have hax : t₁.gpr .rax = BitVec.ofNat 64 w.H.D := by rw [u₁.gpr, hp.tD]
  have h12 : t₁.gpr .r12 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D) := by rw [u₁.other _ (by decide), h.r12]
  have hlt : decide ((t₁.gpr .r12).toNat < (t₁.gpr .rax).toNat) = decide (outLen s₀ - k * w.H.D < w.H.D) := by
    rw [hax, h12, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol]),
      Nat.mod_eq_of_lt (by omega_using [hD])]
  refine WP.ite (decide (outLen s₀ - k * w.H.D < w.H.D)) (by simp only [eval, cf₂, hlt]) (fun hb => ?_) (fun hb => ?_)
  · refine wp_mov fun t₃ u₃ => WP.block_nil ⟨?_, fun r hr => ?_, by rw [u₃.mem, m₂, u₁.mem], by rw [u₃.rd, rd₂, u₁.rd],
      by rw [u₃.wr, wr₂, u₁.wr], by rw [u₃.syms, sy₂, u₁.syms]⟩
    · rw [u₃.gpr, g₂, h12]
      congr 1; unfold nb; have := of_decide_eq_true hb; omega_using [this]
    · rw [u₃.other r hr, g₂, u₁.other r hr]
  · refine WP.block_nil ⟨?_, fun r hr => ?_, by rw [m₂, u₁.mem], by rw [rd₂, u₁.rd], by rw [wr₂, u₁.wr],
      by rw [sy₂, u₁.syms]⟩
    · rw [g₂, hax]
      congr 1; unfold nb; have := of_decide_eq_false hb; omega_using [this]
    · rw [g₂, u₁.other r hr]

/-- `nb` bytes of `T(k + 1)` to `out`, after `k D` of its bytes. -/
theorem outCopy_ok {k : Nat} {t : State} (h : BR w s₀ k t) (hax : t.gpr .rax = BitVec.ofNat 64 (nb w s₀ k)) :
    WP isa outCopy t (OC t (out s₀ + BitVec.ofNat 64 (k * w.H.D)) (sA s₀ eT) (nb w s₀ k)) := by
  have hfr := eFr_eq
  have hD := D_le w
  have hD0 := w.ok.hD0
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have hn0 : 0 < nb w s₀ k := by unfold nb; omega_using [hD0, hk]
  have hnD : nb w s₀ k ≤ w.H.D := Nat.min_le_left _ _
  have hnR : k * w.H.D + nb w s₀ k ≤ outLen s₀ := by unfold nb; omega_using [hk]
  have dTO : Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ ⟨sA s₀ eT, nb w s₀ k⟩ :=
    out_apart hp hnR (.inl ⟨eT, _, rfl, by decide, by simp only [eT]; omega_using [hnD, hD, hfr]⟩)
  unfold outCopy byteLoop
  refine WP.seq (wp_mov32i fun t₁ u₁ => WP.block_nil ?_)
  refine Proof.Bignum.X86_64.wp_upto (a := 0) (N := nb w s₀ k) hn0 (OC t (out s₀ + BitVec.ofNat 64 (k * w.H.D)) (sA s₀ eT)) ?_
    (fun _ h => h) ⟨by rw [u₁.gpr]; rfl, fun r hr _ => u₁.other r hr, by
      rw [u₁.mem, show bytesAt t.mem (sA s₀ eT) 0 = [] from rfl, writeBytes_nil], u₁.rd, u₁.wr, u₁.syms⟩
  intro j _ hj v I
  have hsp : v.gpr .rsp = s₀.gpr .rsp := (I.gpr _ (by decide) (by decide)).trans h.er.rsp
  have hbp : v.gpr .rbp = out s₀ + BitVec.ofNat 64 (k * w.H.D) := (I.gpr _ (by decide) (by decide)).trans h.rbp
  have hvx : v.gpr .rax = BitVec.ofNat 64 (nb w s₀ k) := (I.gpr _ (by decide) (by decide)).trans hax
  have hT : sA s₀ eT + BitVec.ofNat 64 j = sA s₀ (eT + j) := by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have ht : v.mem (sA s₀ eT + BitVec.ofNat 64 j) = t.mem (sA s₀ eT + BitVec.ofNat 64 j) := by
    rw [I.mem]
    refine VG.Proof.Hmac.Common.writeBytes_other _ _ _ fun hc => ?_
    rw [bytesAt_length] at hc
    have hs := Region.Disjoint.sep dTO (Region.contains_self _ _) (Region.contains_self _ _)
    exact hs (sA s₀ eT + BitVec.ofNat 64 j) (by omega_using [hc, hj])
      (by rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; omega_using [hj, hnD, hD])
  simp only [step, List.cons_append, List.nil_append]
  refine wp_movzx8 (a := sA s₀ eT + BitVec.ofNat 64 j)
    (by rw [ea_ix1, hsp, I.r8, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), ← BitVec.add_assoc])
    (by rw [I.rd, I.wr, hT]; exact in_fr hp h.er.wr (by simp only [eT]; omega_using [hj, hnD, hD, hfr]))
    fun v₁ u₁ => ?_
  refine wp_store8 (a := out s₀ + BitVec.ofNat 64 (k * w.H.D) + BitVec.ofNat 64 j)
    (by rw [ea_ix1, u₁.other _ (by decide), u₁.other _ (by decide), hbp, I.r8, BitVec.add_zero])
    (by rw [u₁.wr, I.wr, h.er.wr, hp.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact ⟨outR s₀, by simp, Offset.contains_base _ (by omega_using [hj, hnR]) (by omega_using [hj, hnR, hol])⟩)
    fun v₂ m₂ => wp_addi fun v₃ u₃ => wp_cmp fun v₄ g₄ mm₄ rd₄ wr₄ sy₄ _ zf₄ => WP.block_nil ?_
  have h8 : v₃.gpr .r8 = BitVec.ofNat 64 (j + 1) := by
    rw [u₃.gpr, m₂.gpr, u₁.other _ (by decide), I.r8, sx1]; exact Proof.Bignum.X86_64.ofNat_add_one j
  have hax₃ : v₃.gpr .rax = BitVec.ofNat 64 (nb w s₀ k) := by
    rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hvx]
  refine ⟨?_, ⟨by rw [g₄, h8], fun r h1 h2 => ?_, ?_, by rw [rd₄, u₃.rd, m₂.rd, u₁.rd, I.rd],
    by rw [wr₄, u₃.wr, m₂.wr, u₁.wr, I.wr], by rw [sy₄, u₃.syms, m₂.syms, u₁.syms, I.syms]⟩⟩
  · rw [zf₄, h8, hax₃, Proof.Bignum.X86_64.ofNat_sub_beq (by omega_using [hj, hnD, hD]) (by omega_using [hnD, hD])]
  · rw [g₄, u₃.other r h1, m₂.gpr, u₁.other r h2, I.gpr r h1 h2]
  · have h1 : bytesAt t.mem (sA s₀ eT + BitVec.ofNat 64 j) 1 = [t.mem (sA s₀ eT + BitVec.ofNat 64 j)] := by
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
    rw [mm₄, u₃.mem, m₂.mem, u₁.gpr, u₁.mem, ht, setWidth_byte, I.mem, VG.Proof.Hmac.Common.bytesAt_add, h1,
      writeBytes_snoc _ _ _ _ (by rw [bytesAt_length]; omega_using [hj, hnD, hD]), bytesAt_length]

/-- The copy of `nb` bytes of `T(k + 1)` to `out`, then the registers for
block `k + 2`. -/
theorem next_ok {k : Nat} {t₁ : State} (h₁ : BR w s₀ k t₁) (hT : TF w s₀ k t₁)
    (hax : t₁.gpr .rax = BitVec.ofNat 64 (nb w s₀ k)) :
    WP isa (.seq outCopy (.block nextBlock)) t₁ (EI w s₀ (k + 1)) := by
  have hfr := eFr_eq
  have hD := D_le w
  have hD0 := w.ok.hD0
  have hk := h₁.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have hn0 : 0 < nb w s₀ k := by unfold nb; omega_using [hD0, hk]
  have hnD : nb w s₀ k ≤ w.H.D := Nat.min_le_left _ _
  have hnR : k * w.H.D + nb w s₀ k ≤ outLen s₀ := by unfold nb; omega_using [hk]
  have k₁ := h₁.er
  refine WP.seq (WP.mono (outCopy_ok hp h₁ hax) fun t₂ I => ?_)
  have F : Frame [⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩] t₁.mem t₂.mem := by
    rw [I.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have k₂ : ER w s₀ t₂ := k₁.keep hp I.rd I.wr I.syms (fun r hr => I.gpr r (by revert r; decide) (by revert r; decide)) F
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub_base _ hnR)))
  unfold nextBlock
  refine wp_add fun t₃ u₃ => wp_sub fun t₄ u₄ => tload hp ((k₂.upd (by decide) u₃).upd (by decide) u₄) (by decide)
    fun t₅ u₅ => wp_addi fun t₆ u₆ => wp_test fun t₇ g₇ m₇ rd₇ wr₇ sy₇ zf₇ => WP.block_nil ?_
  have k₇ : ER w s₀ t₇ := ((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).same
    rd₇ wr₇ sy₇ (fun r _ => by rw [g₇]) m₇
  have m₇' : t₇.mem = t₂.mem := by rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hds := done_succ (w := w) (s₀ := s₀) hk
  have hpl : pl w (k + 1) = w.H.D := by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
  have h12 : t₇.gpr .r12 = BitVec.ofNat 64 (outLen s₀ - done w s₀ (k + 1)) := by
    have e₁ : t₃.gpr .r12 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D) := by
      rw [u₃.other _ (by decide), I.gpr _ (by decide) (by decide), h₁.r12]
    have e₂ : t₃.gpr .rax = BitVec.ofNat 64 (nb w s₀ k) := by
      rw [u₃.other _ (by decide), I.gpr _ (by decide) (by decide), hax]
    rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, e₁, e₂, hds,
      ofNat_sub (by omega_using [hnR, hk]) (by omega_using [hol])]
    congr 1; omega_using [hnR]
  have dK : Mem.Sep (out s₀) (k * w.H.D) (out s₀ + BitVec.ofNat 64 (k * w.H.D)) (nb w s₀ k) := by
    have := Offset.sep (out s₀) (d := 0) (n := k * w.H.D) (e := k * w.H.D) (k := nb w s₀ k) (.inl (by omega_using []))
      (by omega_using [hnR, hol]) (by omega_using [hnR, hol])
    rwa [BitVec.add_zero] at this
  have dTO : Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ ⟨sA s₀ eT, w.H.D⟩ :=
    out_apart hp hnR (.inl ⟨eT, _, rfl, by decide, by simp only [eT]; omega_using [hD, hfr]⟩)
  refine ⟨k₇, ?_, h12, ?_, ?_, ?_, fun prk hK => ?_, fun prk hK => ?_⟩
  · rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      I.gpr _ (by decide) (by decide), I.gpr _ (by decide) (by decide), h₁.rbp, hax, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, hds]
  · rw [g₇, u₆.other _ (by decide), u₅.gpr, hp.tD, hpl]
  · rw [g₇, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      I.gpr _ (by decide) (by decide), h₁.r14, sx1, Proof.Bignum.X86_64.ofNat_add_one]
  · rw [zf₇, ← g₇, h12, and_self_beq]
  · have hbl := Proof.Hkdf.blocks_length w.ok.SH.H prk (infoOf s₀) (hash_length w) k
    rw [hds, Proof.Hkdf.blocks_succ, List.take_append, List.take_of_length_le (by omega_using [hbl]),
      hbl, Nat.add_sub_cancel_left, VG.Proof.Hmac.Common.bytesAt_add, m₇', I.mem,
      VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ (by rw [bytesAt_length]; exact dK) (by omega_using [hnR, hol]),
      ← h₁.ob prk hK]
    congr 1
    have hl : (bytesAt t₁.mem (sA s₀ eT) (nb w s₀ k)).length = nb w s₀ k := bytesAt_length _ _ _
    have e := VG.Proof.Hmac.Common.bytesAt_writeBytes_self t₁.mem (out s₀ + BitVec.ofNat 64 (k * w.H.D))
      (bytesAt t₁.mem (sA s₀ eT) (nb w s₀ k)) (by rw [hl]; omega_using [hnD, hD])
    rw [hl] at e
    rw [e, bytesAt_take _ _ hnD, hT prk hK]
  · rw [hpl, m₇', I.mem]
    have hs := Region.Disjoint.sep dTO.symm (Region.contains_self _ _) (Region.contains_self _ _)
    rw [VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ (by rw [bytesAt_length]; exact hs) (by omega_using [hD])]
    exact hT prk hK

/-- After the copy, the registers for block `k + 2`. -/
theorem out_ok {k : Nat} {t : State} (h : BR w s₀ k t) (hT : TF w s₀ k t) :
    WP isa (.seq Impl.Hkdf.X86_64.outLen (.seq outCopy (.block nextBlock))) t (EI w s₀ (k + 1)) := by
  refine WP.seq (WP.mono (outLen_ok hp h) fun t₁ ⟨hax, g₁, m₁, rd₁, wr₁, sy₁⟩ => ?_)
  have k₁ : ER w s₀ t₁ := h.er.same rd₁ wr₁ sy₁ (fun r hr => g₁ r (by revert r; decide)) m₁
  exact next_ok hp (h.keep k₁ (fun r hr => g₁ r (by revert r; decide)) (by rw [m₁])) (fun prk hK => by
    rw [m₁]; exact hT prk hK) hax

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
  refine ⟨⟨h.er, by rw [h.rbp, hd], by rw [h.r12, hd], h.r15, h.r14, hlt, fun prk hK => ?_⟩, h.tb⟩
  have := h.ob prk hK
  rw [hd] at this
  rw [this, List.take_of_length_le (by
    rw [Proof.Hkdf.blocks_length w.ok.SH.H prk (infoOf s₀) (hash_length w) k])]

omit hp in
theorem block_eq (f : Fns) : block f = .seq (.block copyW) (.seq (.seq (.block updT) (tcall .r13 1 f.upd))
    (.seq (.seq (.block updI) (tcall .r13 1 f.upd)) (.seq (.seq (.block updC) (tcall .r13 1 f.upd))
    (.seq (.seq (.block finT) (tcall .r13 2 f.fin)) (.seq Impl.Hkdf.X86_64.outLen (.seq outCopy
    (.block nextBlock))))))) := rfl

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
theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
  · intro e; rw [e]; rfl

omit hp in
/-- Whether bytes of `out` are left, as the loop's condition reads it. -/
theorem eval_ne {k : Nat} {t : State} (h : EI w s₀ k t) :
    eval .ne t = some (decide (outLen s₀ - done w s₀ k ≠ 0)) := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  simp only [eval, h.zf, Option.map_some]
  congr 1
  rw [ofNat_beq_zero (by omega_using [hol])]
  simp only [decide_not]

/-- The blocks, while bytes of `out` are left. -/
theorem loop_ok {k : Nat} {t : State} (h : EI w s₀ k t) (hs : outLen s₀ - done w s₀ k ≠ 0) :
    WP isa (.loop (block f) .ne) t fun u => ∃ K, EI w s₀ K u ∧ outLen s₀ ≤ K * w.H.D := by
  have hD0 := w.ok.hD0
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧ EI w s₀ j u ∧
    outLen s₀ - done w s₀ j ≠ 0) ?_ _ t ⟨k, rfl, h, hs⟩
  rintro n u ⟨j, rfl, hj, hu⟩
  have hlt := (ei_br hj hu).1.lt
  refine WP.mono (block_ok hp hj hu) fun v hv => ?_
  rw [show isa.eval .ne v = _ from eval_ne hv]
  by_cases e : outLen s₀ ≤ (j + 1) * w.H.D
  · refine .inl ⟨?_, j + 1, hv, e⟩
    rw [show done w s₀ (j + 1) = outLen s₀ from Nat.min_eq_right e, Nat.sub_self]; rfl
  · have hd : done w s₀ (j + 1) = (j + 1) * w.H.D := Nat.min_eq_left (by omega_using [e])
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    refine .inr ⟨?_, outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, e, hD0, hsm], j + 1, rfl, hv, ?_⟩
    · rw [hd, decide_eq_true (by omega_using [e] : outLen s₀ - (j + 1) * w.H.D ≠ 0)]
    · rw [hd]; omega_using [e]

omit hp in
theorem epi_eq : expandEpi = Spill.restoreCode .rsp restL := rfl

omit hp in
theorem main_eq (f : Fns) : expandMain f = .seq (.block expandPro)
    (.seq (.ite .ne (.loop (block f) .ne) (.block [])) (.block expandEpi)) := rfl

/-- The frame's body. -/
theorem main_ok : WP isa (expandMain f) s₀ fun u => (∀ r ∈ calleeSaved, u.gpr r = s₀.gpr r) ∧
      u.wr = s₀.wr ∧ u.mem.readW (sA s₀ eFr) 64 = s₀.mem.readW (sA s₀ eFr) 64 ∧ ∀ prk, Keyd w s₀ prk →
        bytesAt u.mem (out s₀) (outLen s₀) =
          (Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) ((outLen s₀ + w.H.D - 1) / w.H.D) [] 1).take (outLen s₀) := by
  have hfr := eFr_eq
  have hD0 := w.ok.hD0
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
  have k₂ := h₂.er
  rw [epi_eq]
  refine WP.mono (Spill.restore_ok .rsp restL s₀.gpr t₂ (by decide)
    (fun q hq => by rw [k₂.rsp]; exact in_fr hp k₂.wr (by have := saved_in q (rest_sub q hq); omega_using [hfr, this]))
    (by rw [k₂.rsp]; exact fun q hq => k₂.saved q (rest_sub q hq))) fun u ⟨r₁, r₂, hm, _, hwr⟩ =>
      ⟨fun r hr => ?_, by rw [hwr, k₂.wr], ?_, fun prk hk => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₁ _ (by decide)
    · exact r₁ _ (by decide)
    · rw [r₂ _ (by decide), k₂.rsp]
    · exact r₁ _ (by decide)
    · exact r₁ _ (by decide)
    · exact r₁ _ (by decide)
    · exact r₁ _ (by decide)
  · rw [hm]
    refine k₂.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hfr])
    · exact hp.r_o
    · exact (stk_fr hp (o := eFr) (n := 8) (by omega_using [hfr])).symm
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

/-- `vg_hkdf_expand`, in its frame. -/
theorem expand_correct {w : MdHash} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (expandR w f ns eStack).pre s) :
    WP isa (expand f) s fun s' => gprPreserved s s' ∧ (expandR w f ns eStack).post s s' := by
  have hsp : eStack ≤ (s.gpr .rsp).toNat := hp.1
  have p := pre_alloc hw hp
  unfold expand
  refine alloc_frame_ok (by decide) (by rw [eStack_eq] at hsp; rw [eFr_eq]; omega_using [hsp])
    (WP.mono (main_ok p) fun v ⟨hcs, hvwr, hret, hP⟩ => ⟨hcs _ (by decide), hvwr, fun m u hm => ?_⟩)
  have hfrm : ∀ {R : Region}, Region.Disjoint R (frR (allocState eFr s)) → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, m (R.base + BitVec.ofNat 64 i) = v.mem (R.base + BitVec.ofNat 64 i) := by
    intro R hR hl i hi
    refine hm.bytes (R := R) (fun r hr => ?_) hl hi
    simp only [List.mem_singleton] at hr; subst hr
    rw [← allocState_rsp']; exact hR
  have hfr := eFr_eq
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun prk hK => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; exact freeState_rsp (hcs _ (by decide))
    · show (v.setReg .rsp (v.gpr .rsp + BitVec.ofNat 64 eFr)).gpr r = _
      rw [RegUpd.gpr_setReg_of_ne _ _ hr', hcs r hr, allocState_gpr' _ _ hr']
  · show m.readW (s.gpr .rsp) 64 = _
    rw [← ret_eq s]
    refine (hm.readW (r := retR (allocState eFr s)) (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans hret
    simp only [List.mem_singleton] at hr; subst hr
    rw [← allocState_rsp']
    exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hfr])
  · have e3 : (allocState eFr s).gpr .rcx = s.gpr .rcx := allocState_gpr' _ _ (by decide)
    have e4 : (allocState eFr s).gpr .r8 = s.gpr .r8 := allocState_gpr' _ _ (by decide)
    have e : bytesAt m (s.gpr .rcx) (s.gpr .r8).toNat = bytesAt v.mem (s.gpr .rcx) (s.gpr .r8).toNat :=
      Proof.Sha256.Stream.bytesAt_congr fun i hi => by
        have := hfrm (R := outR (allocState eFr s)) p.f_o.symm (by
          show outLen _ ≤ 2 ^ 64; exact Nat.le_of_lt (BitVec.isLt _)) i (by simp only [outLen, e4]; exact hi)
        simpa only [outR, out, e3] using this
    rw [e]
    have hK' : Keyd w (allocState eFr s) prk := by
      show Spec.Hkdf.Keyed _ _ ((allocState eFr s).gpr .rdi) _
      rw [allocState_gpr' _ _ (by decide)]; exact hK
    have hol : (s.gpr .r8).toNat ≤ 255 * w.H.D := by have := p.ol; simpa only [outLen, e4] using this
    have := hP prk hK'
    simp only [out, outLen, infoOf, info, infoLen, e3, e4, allocState_gpr' _ _ (show Reg.rsi ≠ .rsp by decide),
      allocState_gpr' _ _ (show Reg.rdx ≠ .rsp by decide)] at this
    rw [this]
    unfold Spec.Hkdf.expand
    rw [ite_eq_right (Nat.not_lt.mpr hol)]
    rfl

/-! ## Constant time -/

open VG.Proof.Hkdf.X86_64 (Ck rel_agree)
open VG.Proof.Hkdf.X86_64.Extract (rel_wp tcall_rel)

/-- The registers that hold public values from the prologue on. -/
abbrev pubRegs : List Reg := [.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The first block of `outLen`: `D` into `rax`, compared with what is left. -/
abbrev oLA : List Instr := [.mov .rax (.mem (at_ .r13 32)), .alu .cmp .r12 (.reg .rax)]

theorem outLen_eq : Impl.Hkdf.X86_64.outLen = .seq (.block oLA) (.ite .b (.block [.mov .rax (.reg .r12)]) (.block [])) :=
  rfl

/-- The taint checks of the pieces of `vg_hkdf_expand` between the calls. -/
structure EChecks : Prop where
  pro : Ck [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (.block expandPro)
  tl1 : Ck [.r13] (.block [.mov .r11 (.mem (at_ .r13 (8 * 1)))])
  tl2 : Ck [.r13] (.block [.mov .r11 (.mem (at_ .r13 (8 * 2)))])
  cp : Ck pubRegs (.block copyW)
  uT : Ck pubRegs (.block updT)
  uI : Ck pubRegs (.block updI)
  uC : Ck pubRegs (.block updC)
  fT : Ck pubRegs (.block finT)
  oA : Ck pubRegs (.block oLA)
  oT : Ck pubRegs (.block [.mov .rax (.reg .r12)])
  nil : Ck [] (.block [])
  ou : Ck (.rax :: pubRegs) (.seq outCopy (.block nextBlock))
  epi : Ck [.rsp] (.block expandEpi)

theorem echecks : EChecks :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- What `outLen` leaves: `min(D, rem)` in `rax`. -/
abbrev OL (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop :=
  BR w s₀ k u ∧ TF w s₀ k u ∧ u.gpr .rax = BitVec.ofNat 64 (nb w s₀ k)

/-- What the first block of `outLen` leaves. -/
abbrev OA (w : MdHash) (s₀ : State) (k : Nat) (u : State) : Prop :=
  BR w s₀ k u ∧ TF w s₀ k u ∧ u.gpr .rax = BitVec.ofNat 64 w.H.D ∧
    u.cf = some (decide (outLen s₀ - k * w.H.D < w.H.D))

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem oA_ok {k : Nat} {t : State} (h : BR w s₀ k t) (hT : TF w s₀ k t) : WP isa (.block oLA) t (OA w s₀ k) := by
  have hD := D_le w
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  refine tload hp h.er (by decide) fun t₁ u₁ => wp_cmp fun t₂ g₂ m₂ rd₂ wr₂ sy₂ cf₂ _ => WP.block_nil ?_
  have hax : t₁.gpr .rax = BitVec.ofNat 64 w.H.D := by rw [u₁.gpr, hp.tD]
  have h12 : t₁.gpr .r12 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D) := by rw [u₁.other _ (by decide), h.r12]
  have k₂ : ER w s₀ t₂ := (h.er.upd (by decide) u₁).same rd₂ wr₂ sy₂ (fun r _ => by rw [g₂]) m₂
  have m : t₂.mem = t.mem := by rw [m₂, u₁.mem]
  refine ⟨h.keep k₂ (fun r hr => by rw [g₂, u₁.other r (by revert r; decide)]) (by rw [m]), fun prk hK => by
    rw [m]; exact hT prk hK, by rw [g₂, hax], ?_⟩
  rw [cf₂, hax, h12, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol]),
    Nat.mod_eq_of_lt (by omega_using [hD])]

omit hp in
theorem oT_ok {k : Nat} {u : State} (h : OA w s₀ k u) (hc : u.cf = some true) :
    WP isa (.block [.mov .rax (.reg .r12)]) u (OL w s₀ k) := by
  obtain ⟨hb, ht, _, hcf⟩ := h
  have hlt : outLen s₀ - k * w.H.D < w.H.D := by rw [hc] at hcf; exact of_decide_eq_true (Option.some.inj hcf).symm
  refine wp_mov fun v u₁ => WP.block_nil ⟨hb.keep (hb.er.upd (by decide) u₁)
    (fun r hr => u₁.other r (by revert r; decide)) (by rw [u₁.mem]), fun prk hK => by rw [u₁.mem]; exact ht prk hK, ?_⟩
  rw [u₁.gpr, hb.r12]; congr 1; unfold nb; omega_using [hlt]

omit hp in
theorem oE_ok {k : Nat} {u : State} (h : OA w s₀ k u) (hc : u.cf = some false) : WP isa (.block []) u (OL w s₀ k) := by
  obtain ⟨hb, ht, hax, hcf⟩ := h
  have hle : ¬ outLen s₀ - k * w.H.D < w.H.D := by rw [hc] at hcf; exact of_decide_eq_false (Option.some.inj hcf).symm
  refine WP.block_nil ⟨hb, ht, ?_⟩
  rw [hax]; congr 1; unfold nb; omega_using [hle]

end

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : MdHash) (s₀ s₀' : State) : Prop where
  regs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.H.hmacFinN = s₀'.syms w.H.hmacFinN

section
variable {w : MdHash} {f : Fns} {s₀ s₀' : State} (hp : Pre w f s₀) (hp' : Pre w f s₀')
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
theorem ol_eq : outLen s₀ = outLen s₀' := congrArg BitVec.toNat (hq.regs .r8 (by simp))

omit hp hp' in
/-- During the same block, the two runs agree on the public registers. -/
theorem agB {k : Nat} {t t' : State} (h : BR w s₀ k t) (h' : BR w s₀' k t') : ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.er.rsp, h'.er.rsp]; exact hq.regs .rsp (by simp)
  · rw [h.er.rbx, h'.er.rbx]; exact hq.regs .rdi (by simp)
  · rw [h.rbp, h'.rbp, show out s₀ = out s₀' from hq.regs .rcx (by simp)]
  · rw [h.r12, h'.r12, ol_eq hq]
  · rw [h.er.r13, h'.er.r13]; exact hq.regs .r9 (by simp)
  · rw [h.r14, h'.r14]
  · rw [h.r15, h'.r15]

omit hp hp' in
theorem ag13 {k : Nat} {t t' : State} (h : BR w s₀ k t) (h' : BR w s₀' k t') : ∀ r ∈ [Reg.r13], t.gpr r = t'.gpr r :=
  fun r hr => agB hq h h' r (by simp at hr; subst hr; simp)

omit hp hp' in
theorem agE {k : Nat} {t t' : State} (h : EI w s₀ k t) (h' : EI w s₀' k t') : eval .ne t = eval .ne t' := by
  rw [eval_ne h, eval_ne h']; simp only [done, ol_eq hq]

/-- One block leaks the same trace in both runs. -/
theorem block_rel (j : Nat) :
    RelCT isa (fun t t' => (EI w s₀ j t ∧ outLen s₀ - done w s₀ j ≠ 0) ∧ (EI w s₀' j t' ∧ outLen s₀' - done w s₀' j ≠ 0))
      (block f) fun u u' => EI w s₀ (j + 1) u ∧ EI w s₀' (j + 1) u' := by
  have kc := echecks
  have e0 := hq.regs .rdi (by simp); have e1 := hq.regs .rsi (by simp); have e2 := hq.regs .rdx (by simp)
  have esp := hq.regs .rsp (by simp)
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
      WP isa (.block [.mov .r11 (.mem (at_ .r13 (8 * 1)))]) t fun u => Upd t u .r11 (s.syms w.H.updN) :=
    fun hp k => tload hp k (by decide) fun t' u => WP.block_nil (by rwa [show _ = _ from hp.tmem.2.1] at u)
  have ld2 : ∀ {s : State} {t : State}, Pre w f s → ER w s t →
      WP isa (.block [.mov .r11 (.mem (at_ .r13 (8 * 2)))]) t fun u => Upd t u .r11 (s.syms w.H.hmacFinN) :=
    fun hp k => tload hp k (by decide) fun t' u => WP.block_nil (by rwa [show _ = _ from hp.tmem.2.2] at u)
  have r3 : RelCT isa (fun t t' => AT w s₀ j (sA s₀ eT) (pl w j) 0 (fun _ => []) t ∧
      AT w s₀' j (sA s₀' eT) (pl w j) 0 (fun _ => []) t') (tcall .r13 1 f.upd)
      fun u u' => PT w s₀ j u ∧ PT w s₀' j u' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag13 hq a.br a'.br)
      (fun t a => ld1 hp a.br.er) (fun t a => by rw [hq.up]; exact ld1 hp' a.br.er)
      (fun t a => by rw [a.br.er.sy]; exact hp.tok.u) (fun t a => by rw [a.br.er.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.X86_64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨upd_args hp a.br a.ua v,
        by have := upd_args hp' a'.br a'.ua v'; simp only [sA] at this ⊢; rwa [← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.rsi, a'.rsi],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.br.er.rsp, a'.br.er.rsp, esp]⟩))
      (fun t a => callT_ok hp a) (fun t a => callT_ok hp' a)
  have r4 := rel_agree (P₁ := PT w s₀ j) (P₂ := PT w s₀' j)
    (G₁ := AT w s₀ j (info s₀) (infoLen s₀) (pl w j) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j)
    (G₂ := AT w s₀' j (info s₀') (infoLen s₀') (pl w j) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uI
    (fun t h => argsI_ok hp h.1 h.2.1 h.2.2) (fun t h => argsI_ok hp' h.1 h.2.1 h.2.2)
  have r5 : RelCT isa (fun t t' =>
      AT w s₀ j (info s₀) (infoLen s₀) (pl w j) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j) t ∧
      AT w s₀' j (info s₀') (infoLen s₀') (pl w j) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j) t')
      (tcall .r13 1 f.upd) fun u u' => PI w s₀ j u ∧ PI w s₀' j u' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag13 hq a.br a'.br)
      (fun t a => ld1 hp a.br.er) (fun t a => by rw [hq.up]; exact ld1 hp' a.br.er)
      (fun t a => by rw [a.br.er.sy]; exact hp.tok.u) (fun t a => by rw [a.br.er.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.X86_64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨upd_args hp a.br a.ua v,
        by have := upd_args hp' a'.br a'.ua v'; simp only [sA, info, infoLen] at this ⊢
           rwa [← esp, ← e1, ← e2] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.rsi, a'.rsi],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.br.er.rsp, a'.br.er.rsp, esp]⟩))
      (fun t a => callI_ok hp a) (fun t a => callI_ok hp' a)
  have r6 := rel_agree (P₁ := PI w s₀ j) (P₂ := PI w s₀' j) (G₁ := AC w s₀ j) (G₂ := AC w s₀' j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uC
    (fun t h => argsC_ok hp h.1 h.2.1 h.2.2) (fun t h => argsC_ok hp' h.1 h.2.1 h.2.2)
  have r7 : RelCT isa (fun t t' => AC w s₀ j t ∧ AC w s₀' j t') (tcall .r13 1 f.upd)
      fun u u' => PC w s₀ j u ∧ PC w s₀' j u' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag13 hq a.1.br a'.1.br)
      (fun t a => ld1 hp a.1.br.er) (fun t a => by rw [hq.up]; exact ld1 hp' a.1.br.er)
      (fun t a => by rw [a.1.br.er.sy]; exact hp.tok.u) (fun t a => by rw [a.1.br.er.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.X86_64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨upd_args hp a.1.br a.1.ua v,
        by have := upd_args hp' a'.1.br a'.1.ua v'; simp only [sA] at this ⊢; rwa [← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.1.rsi, a'.1.rsi, il],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.1.br.er.rsp, a'.1.br.er.rsp, esp]⟩))
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
        infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]))) (tcall .r13 2 f.fin)
      fun u u' => (BR w s₀ j u ∧ TF w s₀ j u) ∧ (BR w s₀' j u' ∧ TF w s₀' j u') :=
    rel_wp (tcall_rel (a := s₀.syms w.H.hmacFinN) kc.tl2 (fun t t' a a' => ag13 hq a.1 a'.1)
      (fun t a => ld2 hp a.1.er) (fun t a => by rw [hq.hf]; exact ld2 hp' a.1.er)
      (fun t a => by rw [a.1.er.sy]; exact hp.tok.f) (fun t a => by rw [a.1.er.sy, hq.hf]; exact hp'.tok.f)
      (Proof.Pbkdf2.Md.X86_64.Pbk.hfin_rel w.ok (hF w) fun u u' ⟨⟨t, a, v⟩, ⟨t', a', v'⟩⟩ =>
        ⟨fin_args hp a.1 a.2.1 v,
        by have := fin_args hp' a'.1 a'.2.1 v'; simp only [sA, key] at this ⊢; rwa [← esp, ← e0, ← il] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), a.1.er.rsp, a'.1.er.rsp, esp]⟩))
      (fun t a => callF_ok hp a.1 a.2.1 a.2.2) (fun t a => callF_ok hp' a.1 a.2.1 a.2.2)
  have rA := rel_agree (P₁ := fun u => BR w s₀ j u ∧ TF w s₀ j u) (P₂ := fun u => BR w s₀' j u ∧ TF w s₀' j u)
    (G₁ := OA w s₀ j) (G₂ := OA w s₀' j) (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.oA
    (fun t h => oA_ok hp h.1 h.2) (fun t h => oA_ok hp' h.1 h.2)
  have rB : RelCT isa (fun u u' => OA w s₀ j u ∧ OA w s₀' j u')
      (.ite .b (.block [.mov .rax (.reg .r12)]) (.block [])) fun u u' => OL w s₀ j u ∧ OL w s₀' j u' := by
    refine RelCT.ite (fun u u' h => by
      show u.cf = u'.cf; rw [h.1.2.2.2, h.2.2.2.2, ol_eq hq]) ?_ ?_
    · exact (rel_agree (P₁ := fun u => OA w s₀ j u ∧ u.cf = some true) (P₂ := fun u => OA w s₀' j u ∧ u.cf = some true)
        (G₁ := OL w s₀ j) (G₂ := OL w s₀' j) (rs := pubRegs) (fun t t' h h' => agB hq h.1.1 h'.1.1) kc.oT
        (fun t h => oT_ok h.1 h.2) (fun t h => oT_ok h.1 h.2)).mono
        (fun u u' ⟨⟨h, h'⟩, hc⟩ => ⟨⟨h, hc⟩, ⟨h', by
          have : u.cf = u'.cf := by rw [h.2.2.2, h'.2.2.2, ol_eq hq]
          rw [← this]; exact hc⟩⟩) fun _ _ h => h
    · exact (rel_agree (P₁ := fun u => OA w s₀ j u ∧ u.cf = some false) (P₂ := fun u => OA w s₀' j u ∧ u.cf = some false)
        (G₁ := OL w s₀ j) (G₂ := OL w s₀' j) (rs := []) (fun _ _ _ _ => by simp) kc.nil
        (fun t h => oE_ok h.1 h.2) (fun t h => oE_ok h.1 h.2)).mono
        (fun u u' ⟨⟨h, h'⟩, hc⟩ => ⟨⟨h, hc⟩, ⟨h', by
          have : u.cf = u'.cf := by rw [h.2.2.2, h'.2.2.2, ol_eq hq]
          rw [← this]; exact hc⟩⟩) fun _ _ h => h
  have rC := rel_agree (P₁ := OL w s₀ j) (P₂ := OL w s₀' j)
    (G₁ := EI w s₀ (j + 1)) (G₂ := EI w s₀' (j + 1)) (rs := .rax :: pubRegs)
    (fun t t' h h' r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.2, h'.2.2, show nb w s₀ j = nb w s₀' j by simp only [nb, ol_eq hq]]
      · exact agB hq h.1 h'.1 r hr) kc.ou
    (fun t h => next_ok hp h.1 h.2.1 h.2.2) (fun t h => next_ok hp' h.1 h.2.1 h.2.2)
  rw [outLen_eq]
  exact r1.seq ((r2.seq r3).seq ((r4.seq r5).seq ((r6.seq r7).seq ((r8.seq r9).seq ((rA.seq rB).seq rC)))))

/-- The blocks leak the same trace in both runs. -/
theorem loop_rel {k : Nat} :
    RelCT isa (fun t t' => (EI w s₀ k t ∧ outLen s₀ - done w s₀ k ≠ 0) ∧ (EI w s₀' k t' ∧ outLen s₀' - done w s₀' k ≠ 0))
      (.loop (block f) .ne) fun u u' => (∃ K, EI w s₀ K u) ∧ (∃ K, EI w s₀' K u') := by
  have hD0 := w.ok.hD0
  refine (RelCT.loop (M := isa) (I := fun n (t t' : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧
      ((EI w s₀ j t ∧ outLen s₀ - done w s₀ j ≠ 0) ∧ (EI w s₀' j t' ∧ outLen s₀' - done w s₀' j ≠ 0)))
    (fun n => ?_) (outLen s₀ - k * w.H.D)).mono (fun t t' h => ⟨k, rfl, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hn : n = outLen s₀ - j * w.H.D
  · subst hn
    refine (block_rel hp hp' hq j).mono (fun t t' h => h.2) fun u u' ⟨hv, hv'⟩ => ?_
    have e := agE hq hv hv'
    refine ⟨e, fun _ => ⟨⟨_, hv⟩, ⟨_, hv'⟩⟩, fun hc => ?_⟩
    rw [show isa.eval .ne u = _ from eval_ne hv] at hc
    have hs : outLen s₀ - done w s₀ (j + 1) ≠ 0 := of_decide_eq_true (Option.some.inj hc)
    have hlt := (ei_br hv hs).1.lt
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    have hs' : outLen s₀' - done w s₀' (j + 1) ≠ 0 := by simp only [done, ← ol_eq hq]; exact hs
    exact ⟨outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, hsm, hD0], j + 1, rfl, ⟨hv, hs⟩, ⟨hv', hs'⟩⟩
  · exact RelCT.of_false fun _ _ h => hn h.1

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (expandMain f) fun _ _ => True := by
  have kc := echecks
  have esp := hq.regs .rsp (by simp)
  have hfr := eFr_eq
  rw [main_eq]
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := EI w s₀ 0) (G₂ := EI w s₀' 0)
    (rs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun s s' hs hs' => by subst hs hs'; exact hq.regs) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => EI w s₀ 0 t ∧ EI w s₀' 0 t')
      (.ite .ne (.loop (block f) .ne) (.block [])) fun u u' => (∃ K, EI w s₀ K u) ∧ (∃ K, EI w s₀' K u') := by
    refine RelCT.ite (fun t t' h => agE hq h.1 h.2) ?_ ?_
    · refine (loop_rel hp hp' hq (k := 0)).mono (fun t t' h => ?_) fun _ _ h => h
      obtain ⟨⟨h₁, h₂⟩, hc⟩ := h
      rw [show isa.eval .ne t = _ from eval_ne h₁] at hc
      have hs := of_decide_eq_true (Option.some.inj hc)
      exact ⟨⟨h₁, hs⟩, ⟨h₂, by simp only [done, ← ol_eq hq]; exact hs⟩⟩
    · exact (rel_agree (P₁ := EI w s₀ 0) (P₂ := EI w s₀' 0) (G₁ := fun u => ∃ K, EI w s₀ K u)
        (G₂ := fun u => ∃ K, EI w s₀' K u) (rs := []) (fun _ _ _ _ => by simp)
        kc.nil (fun t h => WP.block_nil ⟨0, h⟩) (fun t h => WP.block_nil ⟨0, h⟩)).mono (fun t t' h => h.1)
        fun _ _ h => h
  have r3 := rel_agree (P₁ := fun u => ∃ K, EI w s₀ K u) (P₂ := fun u => ∃ K, EI w s₀' K u)
    (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [.rsp])
    (fun t t' ⟨_, k⟩ ⟨_, k'⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [k.er.rsp, k'.er.rsp, esp]) kc.epi
    (fun t ⟨_, k⟩ => by
      rw [epi_eq]
      exact WP.mono (Spill.restore_ok .rsp restL s₀.gpr t (by decide)
        (fun q hq => by rw [k.er.rsp]; exact in_fr hp k.er.wr (by have := saved_in q (rest_sub q hq); omega_using [hfr, this]))
        (by rw [k.er.rsp]; exact fun q hq => k.er.saved q (rest_sub q hq))) fun _ _ => trivial)
    (fun t ⟨_, k⟩ => by
      rw [epi_eq]
      exact WP.mono (Spill.restore_ok .rsp restL s₀'.gpr t (by decide)
        (fun q hq => by rw [k.er.rsp]; exact in_fr hp' k.er.wr (by have := saved_in q (rest_sub q hq); omega_using [hfr, this]))
        (by rw [k.er.rsp]; exact fun q hq => k.er.saved q (rest_sub q hq))) fun _ _ => trivial)
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
  have hq : PubEq w (allocState eFr e) (allocState eFr e') :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q0]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q1]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q2]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q3]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q4]
      · rw [allocState_gpr' _ _ (by decide), allocState_gpr' _ _ (by decide), q5]
      · rw [allocState_rsp', allocState_rsp', qsp],
      qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (expand f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold expand
  refine RelCT.alloc (R := fun _ _ => True) ((main_rel hp hp' hq).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.X86_64.Expand
