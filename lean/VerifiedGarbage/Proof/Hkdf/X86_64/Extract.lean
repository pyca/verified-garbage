module

public import VerifiedGarbage.Proof.Hkdf.X86_64.Key
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkLoop
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Framework.X86_64.Steps
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Hkdf.X86_64

/-!
# HKDF on x86-64: `vg_hkdf_extract`, correct

The contract the proof is written against (`extractR`), for the table
`hmac` of one variant `w` (`MdHash`), whose functions an indirect call of
`f`'s reaches: `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`,
the table the argument on the stack, writes `HMAC(salt, IKM)` to `prk`,
which is `D` bytes long. In its frame (`xFr` bytes: the save area, HMAC's
inner and outer states, then the working space), the prologue saves our
caller's registers and keeps the arguments it needs after the calls in
callee-saved registers (`pro_ok`, from which on `XR` holds); then `init`
with the salt as the key, `update` with the input keying material and
`finalize` into `prk`, each through the table (`init_ok`, `upd_ok`,
`fin_ok`); and the epilogue restores our caller's registers.
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86_64.Extract

open VG.X86_64 VG.X86_64.Steps
open VG.Impl.Hkdf.X86_64
open VG.Impl.Mgf1.X86_64 (sp at_)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (TabOK TabMem)
open VG.Proof.Hkdf.X86_64 (HOk ea_at ea_sp repr_keep)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## What the variants give of `finalize` -/

theorem hF (w : MdHash) :
    Verified X86_64.target w.H.hmacFin (Proof.Pbkdf2.Md.X86_64.Calls.finG w.ok.SH w.H.W) :=
  Proof.Pbkdf2.Md.X86_64.hmacFin_ok w.ok w.C w.K (by rw [w.hSH]; exact w.hmacFin.2.2)

theorem hFsp (w : MdHash) : NoSp w.H.hmacFin :=
  Proof.Pbkdf2.Md.X86_64.nosp_of (Proof.Pbkdf2.Md.X86_64.core_hmacFin w.K.cNs w.C.hfinNs)

theorem hFd (w : MdHash) : w.H.hmacFin.depth ≤ 2 :=
  Proof.Pbkdf2.Md.X86_64.core_hmacFin_depth w.K.cD w.C.hfinD

/-- HMAC's key, its block size. -/
theorem blockKey_length (w : MdHash) (k : List Byte) : (blockKey w.ok.SH.H k).length = w.H.P.B := by
  have hB := w.ok.hB
  have hDB : w.H.D ≤ w.H.P.B := by have h1 := w.ok.hDN; have h2 := w.ok.hNL; omega_using [h1, h2]
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · have : (w.ok.SH.H.hash k).length ≤ w.H.D := by rw [w.ok.hash]; exact List.length_take_le _ _
    omega_using [this, hDB]
  · omega_arith

/-! ## The contract -/

/-- `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`, with `N`
bytes of stack, for the table `hmac` (the argument on the stack) of `w`,
whose functions an indirect call of `f`'s reaches, with the addresses of the
functions `ns` public. -/
def extractR (w : MdHash) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let salt : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ikm : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let prk : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let tab : Region := ⟨stackArg s 0, 48⟩
    let arg : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [salt, ikm, tab, arg] ∧ s.wr = [prk] ∧
      salt.Disjoint prk ∧ ikm.Disjoint prk ∧ prk.Disjoint tab ∧ ret.Disjoint prk ∧
      stk.Disjoint salt ∧ stk.Disjoint ikm ∧ stk.Disjoint prk ∧ stk.Disjoint tab ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat = w.H.D ∧ TabMem w.H s.syms (stackArg s 0) s.mem ∧
      s.mem.readW (stackArg s 0 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B ∧ TabOK w.H f s.syms
  post s s' := bytesAt s'.mem (s.gpr .r8) w.H.D =
    Spec.Hkdf.extract w.ok.SH.H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_extract` uses: its frame, and below it the 32 bytes
the call of `init` takes to be apart from its buffers. -/
def xStack : Nat := xFr + 32

theorem xFr_eq : xFr = 3520 := rfl
theorem xStack_eq : xStack = 3552 := rfl

section
variable (s₀ : State)

/-- An address in the frame, of the state on entry to the frame's body. -/
abbrev sA (o : Nat) : Addr := s₀.gpr .rsp + BitVec.ofNat 64 o

/-- The arguments, on entry to the frame's body. -/
abbrev salt : Addr := s₀.gpr .rdi
abbrev saltLen : Nat := (s₀.gpr .rsi).toNat
abbrev ikm : Addr := s₀.gpr .rdx
abbrev ikmLen : Nat := (s₀.gpr .rcx).toNat
abbrev prk : Addr := s₀.gpr .r8
/-- The table, the argument on the stack. -/
abbrev tab : Addr := s₀.mem.readW (sA s₀ (xFr + 8)) 64

abbrev frR : Region := ⟨s₀.gpr .rsp, xFr⟩
abbrev saltR : Region := ⟨salt s₀, saltLen s₀⟩
abbrev ikmR : Region := ⟨ikm s₀, ikmLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩
abbrev argR : Region := ⟨sA s₀ (xFr + 8), 8⟩
abbrev retR : Region := ⟨sA s₀ xFr, 8⟩
/-- The stack below the frame that the calls use. -/
abbrev stk : Region := below (s₀.gpr .rsp) 32

end

/-- The regions the frame's body writes. -/
abbrev prkR (w : MdHash) (s₀ : State) : Region := ⟨prk s₀, w.H.D⟩
abbrev wrs (w : MdHash) (s₀ : State) : List Region := [frR s₀, prkR w s₀, stk s₀]

/-- The state the frame's body starts in. -/
structure Pre (w : MdHash) (f : Fns) (s₀ : State) : Prop where
  hw : HOk w
  rd : s₀.rd = [saltR s₀, ikmR s₀, tabR s₀, argR s₀]
  wr : s₀.wr = [frR s₀, prkR w s₀]
  pl : (s₀.gpr .r9).toNat = w.H.D
  s_p : (saltR s₀).Disjoint (prkR w s₀)
  i_p : (ikmR s₀).Disjoint (prkR w s₀)
  p_t : (prkR w s₀).Disjoint (tabR s₀)
  r_p : (retR s₀).Disjoint (prkR w s₀)
  f_s : (frR s₀).Disjoint (saltR s₀)
  f_i : (frR s₀).Disjoint (ikmR s₀)
  f_p : (frR s₀).Disjoint (prkR w s₀)
  f_t : (frR s₀).Disjoint (tabR s₀)
  b_s : (stk s₀).Disjoint (saltR s₀)
  b_i : (stk s₀).Disjoint (ikmR s₀)
  b_p : (stk s₀).Disjoint (prkR w s₀)
  b_t : (stk s₀).Disjoint (tabR s₀)
  sp : 32 ≤ (s₀.gpr .rsp).toNat
  top : (s₀.gpr .rsp).toNat + xFr + 16 ≤ 2 ^ 64
  ns : (salt s₀).toNat + saltLen s₀ ≤ 2 ^ 64
  ni : (ikm s₀).toNat + ikmLen s₀ ≤ 2 ^ 64
  np : (prk s₀).toNat + w.H.D ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w.H s₀.syms (tab s₀) s₀.mem
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B
  tok : TabOK w.H f s₀.syms

section
variable {w : MdHash} {f : Fns} {ns : List String}

theorem arg_eq (s : State) :
    stackArgAddr s 0 = sA (allocState xFr s) (xFr + 8) := by
  rw [sA, allocState_rsp', BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]; rfl

theorem ret_eq (s : State) : sA (allocState xFr s) xFr = s.gpr .rsp := by
  rw [sA, allocState_rsp', BitVec.sub_add_cancel]

theorem tab_alloc (s : State) : tab (allocState xFr s) = stackArg s 0 := by
  simp only [tab, stackArg]; rw [arg_eq]; rfl

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hw : HOk w) (hp : (extractR w f ns xStack).pre s) : Pre w f (allocState xFr s) := by
  obtain ⟨hsp, htop, hrd, hwr, sp', ip, pt, rp, ks, ki, kp, kt, ns', ni, np, nt, hpl, tm, tb, tok⟩ := hp
  have ha := arg_eq s
  have hr := ret_eq s
  have hT : stackArg s 0 = tab (allocState xFr s) := by
    simp only [tab, stackArg]; rw [ha]; rfl
  have hspF : ((allocState xFr s).gpr .rsp).toNat = (s.gpr .rsp).toNat - xFr := by
    rw [allocState_rsp', BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat]; rw [xStack_eq] at hsp; rw [xFr_eq]; omega_using [hsp]),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [xFr_eq]; omega_using [])]
  obtain subF : Region.Sub (frR (allocState xFr s)) ⟨s.gpr .rsp - BitVec.ofNat 64 xStack, xStack⟩ := by
    rw [frR, allocState_rsp']
    exact Offset.sub_below _ (by decide) (by decide)
  obtain subS : Region.Sub (stk (allocState xFr s)) ⟨s.gpr .rsp - BitVec.ofNat 64 xStack, xStack⟩ := by
    show Region.Sub ⟨(allocState xFr s).gpr .rsp - BitVec.ofNat 64 32, 32⟩ _
    rw [allocState_rsp', Offset.sub_sub_ofNat]
    exact Region.sub_prefix (by rw [xStack_eq]; omega_using [])
  have g : ∀ r, r ≠ .rsp → (allocState xFr s).gpr r = s.gpr r := fun r h => allocState_gpr' _ _ h
  have e8 := g .r8 (by decide); have e9 := g .r9 (by decide)
  have e0 := g .rdi (by decide); have e1 := g .rsi (by decide)
  have e2 := g .rdx (by decide); have e3 := g .rcx (by decide)
  have hprk : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region) = prkR w (allocState xFr s) := by
    simp only [prkR, prk, e8, hpl]
  rw [hT] at pt kt nt tm tb
  rw [hprk] at sp' ip pt rp kp hwr
  rw [← hr] at rp
  refine ⟨hw, ?_, ?_, by rw [e9]; exact hpl, ?_, ?_, pt, rp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by simp only [salt, saltLen, e0, e1]; exact ns', by simp only [ikm, ikmLen, e2, e3]; exact ni,
    by simp only [prk, e8, ← hpl]; exact np, nt, tm, tb, tok⟩
  · show s.rd = _; rw [hrd, hT, ha]; simp only [saltR, ikmR, salt, saltLen, ikm, ikmLen, e0, e1, e2, e3]
  · show (_ : Region) :: s.wr = _; rw [hwr]; simp only [frR, allocState_rsp']
  · simp only [saltR, salt, saltLen, e0, e1]; exact sp'
  · simp only [ikmR, ikm, ikmLen, e2, e3]; exact ip
  · simp only [saltR, salt, saltLen, e0, e1]; exact ks.sub_left subF
  · simp only [ikmR, ikm, ikmLen, e2, e3]; exact ki.sub_left subF
  · exact kp.sub_left subF
  · exact kt.sub_left subF
  · simp only [saltR, salt, saltLen, e0, e1]; exact ks.sub_left subS
  · simp only [ikmR, ikm, ikmLen, e2, e3]; exact ki.sub_left subS
  · exact kp.sub_left subS
  · exact kt.sub_left subS
  · rw [hspF]; rw [xStack_eq] at hsp; rw [xFr_eq]; omega_using [hsp]
  · rw [hspF]; rw [xStack_eq] at hsp; rw [xFr_eq]; omega_using [hsp, htop]

end

/-! ## What every piece keeps -/

/-- Where the prologue saves our caller's registers. -/
def savedL : List (Reg × Nat) := [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24)]

theorem saved_slots : Spill.Slots savedL := by decide

theorem saved_in : ∀ q ∈ savedL, q.2 + 8 ≤ 32 := by
  intro q hq
  simp only [savedL, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- The registers and memory kept from the end of the prologue on. -/
structure XR (w : MdHash) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sy : t.syms = s₀.syms
  rsp : t.gpr .rsp = s₀.gpr .rsp
  rbx : t.gpr .rbx = ikm s₀
  rbp : t.gpr .rbp = s₀.gpr .rcx
  r12 : t.gpr .r12 = prk s₀
  r13 : t.gpr .r13 = tab s₀
  r14 : t.gpr .r14 = s₀.gpr .r14
  r15 : t.gpr .r15 = s₀.gpr .r15
  saved : Spill.Saved t.mem (s₀.gpr .rsp) s₀.gpr savedL
  frame : Frame (wrs w s₀) s₀.mem t.mem

/-- A part of the frame after the save area, `prk`, or the stack below the
frame that a call uses. -/
def Wk (w : MdHash) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 32 ≤ o ∧ o + n ≤ xFr) ∨ Region.Sub r (prkR w s₀) ∨
    ∃ n, r = below (s₀.gpr .rsp) n ∧ n ≤ 32

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem Wk.ok {r : Region} (h : Wk w s₀ r) :
    (∀ q ∈ savedL, Region.Disjoint ⟨Spill.slot (s₀.gpr .rsp) q.2, 8⟩ r) ∧ ∃ r' ∈ wrs w s₀, Region.Sub r r' := by
  have top := hp.top
  have hfr := xFr_eq
  have sv : ∀ q ∈ savedL, Region.Sub ⟨Spill.slot (s₀.gpr .rsp) q.2, 8⟩ (frR s₀) := fun q hq =>
    Offset.sub_base _ (by have := saved_in q hq; omega_using [hfr, this])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · refine ⟨fun q hq => Offset.disjoint _ (.inl (by have := saved_in q hq; omega_using [h₁, this]))
      (by have := saved_in q hq; omega_using [this]) (by omega_using [h₂, hfr]), _, by simp, Offset.sub_base _ h₂⟩
  · exact ⟨fun q hq => (hp.f_p.sub_left (sv q hq)).sub_right h, _, by simp, h⟩
  · have hb : Region.Sub (below (s₀.gpr .rsp) n) (stk s₀) := by
      show Region.Sub ⟨s₀.gpr .rsp - BitVec.ofNat 64 n, n⟩ ⟨s₀.gpr .rsp - BitVec.ofNat 64 32, 32⟩
      exact Offset.sub_below _ hn (by omega_using [hn])
    refine ⟨fun q hq => ?_, _, by simp, hb⟩
    have := Offset.disjoint_below (s₀.gpr .rsp) (n := n) (d := q.2) (k := 8)
      (by have := saved_in q hq; omega_using [this, hn])
    exact this

theorem XR.keep {t t' : State} (h : XR w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsy : t'.syms = t.syms)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk w s₀ r) : XR w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.sy, (hg _ (by decide)).trans h.rsp, (hg _ (by decide)).trans h.rbx,
    (hg _ (by decide)).trans h.rbp, (hg _ (by decide)).trans h.r12, (hg _ (by decide)).trans h.r13,
    (hg _ (by decide)).trans h.r14, (hg _ (by decide)).trans h.r15,
    h.saved.frame hf fun q hq r hr => (Wk.ok hp (hw r hr)).1 q hq,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem XR.upd {t t' : State} (h : XR w s₀ t) {d : Reg} (hd : d ∉ calleeSaved) {v : BitVec 64}
    (u : Upd t t' d v) : XR w s₀ t' := by
  have g : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r := fun r hr => u.other r fun e => hd (e ▸ hr)
  exact ⟨u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.sy, (g _ (by decide)).trans h.rsp,
    (g _ (by decide)).trans h.rbx, (g _ (by decide)).trans h.rbp, (g _ (by decide)).trans h.r12,
    (g _ (by decide)).trans h.r13, (g _ (by decide)).trans h.r14, (g _ (by decide)).trans h.r15,
    by rw [u.mem]; exact h.saved, by rw [u.mem]; exact h.frame⟩

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem XR.bytes {t : State} (hk : XR w s₀ t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs w s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem XR.saltB {t : State} (hk : XR w s₀ t) :
    bytesAt t.mem (salt s₀) (saltLen s₀) = bytesAt s₀.mem (salt s₀) (saltLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_s.symm
    · exact hp.s_p
    · exact hp.b_s.symm) (Nat.le_of_lt (s₀.gpr .rsi).isLt)

theorem XR.ikmB {t : State} (hk : XR w s₀ t) :
    bytesAt t.mem (ikm s₀) (ikmLen s₀) = bytesAt s₀.mem (ikm s₀) (ikmLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_i.symm
    · exact hp.i_p
    · exact hp.b_i.symm) (Nat.le_of_lt (s₀.gpr .rcx).isLt)

/-- A word of the table is as on entry. -/
theorem XR.tabW {t : State} (hk : XR w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tabR s₀) (Offset.contains_base _ ho (by omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.f_t.symm
      · exact hp.p_t.symm
      · exact hp.b_t.symm) (by decide)

/-- The table's word at `o`, readable. -/
theorem tin {t : State} (hk : XR w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
  ⟨tabR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp), Offset.contains_base _ ho (by omega_using [ho])⟩

/-- A part of the frame is in the writable regions. -/
theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ xFr) :
    InRegions (t.rd ++ t.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (by rw [hwr, hp.wr]; exact List.mem_cons_self),
    Offset.contains_base _ h (by have := xFr_eq; omega_using [h, this])⟩

theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ xFr) : InRegions t.wr (sA s₀ o) n :=
  ⟨_, by rw [hwr, hp.wr]; exact List.mem_cons_self, Offset.contains_base _ h (by have := xFr_eq; omega_using [h, this])⟩

/-- An offset of the frame, as a number. -/
theorem sA_toNat {o : Nat} (ho : o ≤ xFr + 8) : (sA s₀ o).toNat = (s₀.gpr .rsp).toNat + o := by
  have top := hp.top
  have hfr := xFr_eq
  rw [sA, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, hfr]),
    Nat.mod_eq_of_lt (by omega_using [ho, top, hfr])]

end

/-- The loads of the table's functions' addresses. -/
theorem tload {w : MdHash} {f : Fns} {s₀ t : State} (hp : Pre w f s₀) (k : XR w s₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.mov .r11 (.mem (at_ .r13 (8 * j)))]) t fun u =>
      Upd t u .r11 (s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * j)) 64) := by
  refine wp_movm (by rw [ea_at, k.r13]) (tin hp k hj) fun u v => WP.block_nil ?_
  rw [← k.tabW hp hj]; exact v

/-! ## The prologue -/

theorem sx32 : (BitVec.ofNat 32 xIn).signExtend 64 = BitVec.ofNat 64 xIn := by decide
theorem sx224 : (BitVec.ofNat 32 xOut).signExtend 64 = BitVec.ofNat 64 xOut := by decide
theorem sx416 : (BitVec.ofNat 32 xWork).signExtend 64 = BitVec.ofNat 64 xWork := by decide

theorem pro_eq : extractPro = Spill.saveCode .rsp savedL ++
    ([.mov .rbx (.reg .rdx), .mov .rbp (.reg .rcx), .mov .r12 (.reg .r8), .mov .r13 (.mem (sp (xFr + 8))),
      .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi), .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 xIn)),
      .mov .rsi (.reg .rsp), .alu .add .rsi (.imm (BitVec.ofNat 32 xOut)), .mov .r8 (.reg .rsp),
      .alu .add .r8 (.imm (BitVec.ofNat 32 xWork))] : List Instr) := rfl

/-- After the prologue: `XR`, and `init`'s arguments. -/
def XA (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ t.gpr .rdi = sA s₀ xIn ∧ t.gpr .rsi = sA s₀ xOut ∧ t.gpr .rdx = salt s₀ ∧
    t.gpr .rcx = s₀.gpr .rsi ∧ t.gpr .r8 = sA s₀ xWork

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem pro_ok : WP isa (.block extractPro) s₀ (XA w s₀) := by
  rw [pro_eq]
  have hfr := xFr_eq
  refine Spill.save_then .rsp savedL (fun q hq => in_frw hp rfl (by have := saved_in q hq; omega_using [hfr, this])) ?_
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => ?_
  have sp₃ : t₃.gpr .rsp = s₀.gpr .rsp := by upd_simp [u₃.other, u₂.other, u₁.other]
  have rd₃ : t₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  refine wp_movm (a := sA s₀ (xFr + 8)) (by rw [ea_sp, sp₃])
    ⟨argR s₀, List.mem_append_left _ (by rw [rd₃, hp.rd]; simp), Region.contains_self _ _⟩
    fun t₄ u₄ => ?_
  refine wp_mov fun t₅ u₅ => wp_mov fun t₆ u₆ => wp_mov fun t₇ u₇ => wp_addi fun t₈ u₈ =>
    wp_mov fun t₉ u₉ => wp_addi fun t₁₀ u₁₀ => wp_mov fun t₁₁ u₁₁ => wp_addi fun t₁₂ u₁₂ => WP.block_nil ?_
  have mm : t₁₂.mem = Spill.saveMem s₀.mem (s₀.gpr .rsp) s₀.gpr savedL := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₃ : t₃.mem = Spill.saveMem s₀.mem (s₀.gpr .rsp) s₀.gpr savedL := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hT : t₃.mem.readW (sA s₀ (xFr + 8)) 64 = tab s₀ := by
    rw [m₃]
    exact Spill.saveMem_readW_sep _ _ _ (by decide) _ fun q hq => ⟨by have := saved_in q hq; omega_using [this],
      .inr (by have := saved_in q hq; omega_using [this, hfr])⟩
  refine ⟨⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃],
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₁₂.syms, u₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms,
      u₁.syms], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other, hT]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · rw [mm]; exact Spill.saveMem_saved _ _ _ savedL saved_slots
  · rw [mm]
    exact (Spill.saveMem_frame_base _ _ _ savedL saved_in (by decide)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨frR s₀, by simp, Region.sub_prefix (by omega_using [hfr])⟩
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other, sx32]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other, sx224]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other, sx416]

end

/-! ## The calls -/

/-- The key `K₀` the salt makes. -/
abbrev k0Of (w : MdHash) (s₀ : State) : List Byte := blockKey w.ok.SH.H (bytesAt s₀.mem (salt s₀) (saltLen s₀))

/-- The input keying material. -/
abbrev ikmOf (s₀ : State) : List Byte := bytesAt s₀.mem (ikm s₀) (ikmLen s₀)

/-- After `init`: the states of `K₀`. -/
def XI (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ w.ok.SH.Repr t.mem (sA s₀ xIn) (xorPad (k0Of w s₀) ipad) ∧
    w.ok.SH.Repr t.mem (sA s₀ xOut) (xorPad (k0Of w s₀) opad)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem inR : Region.Sub ⟨sA s₀ xIn, w.H.S⟩ (frR s₀) :=
  Offset.sub_base _ (by have hS := hp.hw.hS; have hfr := xFr_eq; simp only [xIn]; omega_using [hS, hfr])

theorem outR : Region.Sub ⟨sA s₀ xOut, w.H.S⟩ (frR s₀) :=
  Offset.sub_base _ (by have hS := hp.hw.hS; have hfr := xFr_eq; simp only [xOut]; omega_using [hS, hfr])

omit hp in
theorem workR {n : Nat} (hn : n ≤ work) : Region.Sub ⟨sA s₀ xWork, n⟩ (frR s₀) :=
  Offset.sub_base _ (by have hfr := xFr_eq; have hwk : work = 3104 := rfl; simp only [xWork]; omega_using [hn, hfr, hwk])

theorem in_out : Region.Disjoint ⟨sA s₀ xIn, w.H.S⟩ ⟨sA s₀ xOut, w.H.S⟩ := by
  have hS := hp.hw.hS
  exact Offset.disjoint _ (.inl (by simp only [xIn, xOut]; omega_using [hS])) (by simp only [xIn]; omega_using [hS])
    (by simp only [xOut]; omega_using [hS])

theorem in_work {n : Nat} (hn : n ≤ work) : Region.Disjoint ⟨sA s₀ xIn, w.H.S⟩ ⟨sA s₀ xWork, n⟩ := by
  have hS := hp.hw.hS; have hwk : work = 3104 := rfl
  exact Offset.disjoint _ (.inl (by simp only [xIn, xWork]; omega_using [hS])) (by simp only [xIn]; omega_using [hS])
    (by simp only [xWork]; omega_using [hn, hwk])

theorem out_work {n : Nat} (hn : n ≤ work) : Region.Disjoint ⟨sA s₀ xOut, w.H.S⟩ ⟨sA s₀ xWork, n⟩ := by
  have hS := hp.hw.hS; have hwk : work = 3104 := rfl
  exact Offset.disjoint _ (.inl (by simp only [xOut, xWork]; omega_using [hS])) (by simp only [xOut]; omega_using [hS])
    (by simp only [xWork]; omega_using [hn, hwk])

/-- The stack below the frame, apart from a part of the frame. -/
theorem stk_fr {o n : Nat} (h : o + n ≤ xFr + 16) : Region.Disjoint (stk s₀) ⟨sA s₀ o, n⟩ := by
  have top := hp.top
  have hfr := xFr_eq
  exact (Offset.disjoint_below (s₀.gpr .rsp) (n := 32) (d := o) (k := n) (by omega_using [h, top, hfr])).symm

omit hp in
/-- The stack a callee uses, within `stk`. -/
theorem below_stk {t : State} (ht : t.gpr .rsp = s₀.gpr .rsp) {n : Nat} (hn : n ≤ 32) :
    Region.Sub (below (t.gpr .rsp) n) (stk s₀) := by
  rw [ht]
  show Region.Sub ⟨s₀.gpr .rsp - BitVec.ofNat 64 n, n⟩ ⟨s₀.gpr .rsp - BitVec.ofNat 64 32, 32⟩
  exact Offset.sub_below _ hn (by omega_using [hn])

/-- The input keying material fits HMAC's count with a block of key. -/
theorem ikm_lt : w.H.P.B + ikmLen s₀ < 2 ^ 64 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hp.f_i.symm hp.ni (by
    show (s₀.gpr .rsp).toNat + xFr ≤ 2 ^ 64; have := hp.top; omega_using [this])
  have hB : w.H.P.B ≤ 128 := w.ok.B_le
  have : xFr = 3520 := rfl
  have h' : ikmLen s₀ + xFr ≤ 2 ^ 64 := h
  omega_using [h', hB, this]

/-- `init`'s arguments, after the load of its address. -/
theorem init_args {t t' : State} (h : XA w s₀ t) {v : Addr} (u : Upd t t' .r11 v) :
    Proof.Pbkdf2.Md.X86_64.Any.AnyArgs (H := w.H) t' (sA s₀ xIn) (sA s₀ xOut) (salt s₀) (sA s₀ xWork)
      (saltLen s₀) := by
  obtain ⟨k, a0, a1, a2, a3, a8⟩ := h
  have hA := hp.hw.hA
  have g : ∀ r, r ≠ .r11 → t'.gpr r = t.gpr r := u.other
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide), k.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 32) (stk s₀) := below_stk sp' (Nat.le_refl _)
  have hS := hp.hw.hS
  have hfr := xFr_eq
  have hwk : work = 3104 := rfl
  refine ⟨by rw [g _ (by decide), a0], by rw [g _ (by decide), a1], by rw [g _ (by decide), a2],
    by rw [g _ (by decide), a3], by rw [g _ (by decide), a8], ?_, ?_, in_out hp, in_work hp hA, out_work hp hA,
    hp.f_s.symm.sub_right (inR hp), hp.f_s.symm.sub_right (outR hp), hp.f_s.symm.sub_right (workR hA),
    (stk_fr hp (by simp only [xIn]; omega_using [hS, hfr])).sub_left hb,
    (stk_fr hp (by simp only [xOut]; omega_using [hS, hfr])).sub_left hb, hp.b_s.sub_left hb,
    (stk_fr hp (by simp only [xWork]; omega_using [hA, hfr, hwk])).sub_left hb, ?_⟩
  · exact VG.Covers.left (by rw [u.rd, k.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
  · rw [u.wr, k.wr, hp.wr]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨frR s₀, by simp, xIn, rfl, by dsimp only; simp only [xIn]; omega_using [hS, hfr]⟩
    · exact ⟨frR s₀, by simp, xOut, rfl, by dsimp only; simp only [xOut]; omega_using [hS, hfr]⟩
    · exact ⟨frR s₀, by simp, xWork, rfl, by dsimp only; simp only [xWork]; omega_using [hA, hfr, hwk]⟩
  · rw [sA_toNat hp (by simp only [xWork]; omega_using [hfr])]
    have := hp.top; simp only [xWork]; omega_using [hA, hfr, hwk, this]

theorem init_ok {t : State} (h : XA w s₀ t) : WP isa (tcall .r13 0 f.init) t (XI w s₀) := by
  have k := h.1
  unfold tcall
  refine WP.seq (WP.mono (tload hp k (j := 0) (by decide)) fun t' u => ?_)
  have h0 : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * 0)) 64 = s₀.syms w.H.hmacInitAnyN := hp.tmem.1
  have hr11 : t'.gpr .r11 = s₀.syms w.H.hmacInitAnyN := by rw [u.gpr, h0]
  refine WP.icalls_of_call (a := t'.gpr .r11) (n := w.H.hmacInitAnyN) (c := w.H.hmacInitAny) rfl ?_ (WP.of_syms ?_)
  · show f.init.find? (fun q => t'.syms q.1 == t'.gpr .r11) = _
    rw [hr11, u.syms, k.sy]; exact hp.tok.i
  refine Proof.Pbkdf2.Md.X86_64.Any.any_call (n := w.H.hmacInitAnyN) w.ok w.hmacAny w.hmacAnyNs w.hmacAnyD
    (init_args hp h u) (s₀.gpr .rsi).isLt fun s' hrd hwr hcs hfr hi ho hsy => ?_
  have hA := hp.hw.hA
  have hS := hp.hw.hS
  have hfr' := xFr_eq
  have hwk : work = 3104 := rfl
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [u.other _ (by decide), k.rsp]
  have k' : XR w s₀ s' := (k.upd (by decide) u).keep hp hrd hwr hsy hcs hfr fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨xIn, w.H.S, rfl, by decide, by simp only [xIn]; omega_using [hS, hfr']⟩
    · exact .inl ⟨xOut, w.H.S, rfl, by decide, by simp only [xOut]; omega_using [hS, hfr']⟩
    · exact .inl ⟨xWork, _, rfl, by decide, by simp only [xWork]; omega_using [hA, hfr', hwk]⟩
    · exact .inr (.inr ⟨24, by rw [sp'], by decide⟩)
  have hs : bytesAt t'.mem (salt s₀) (saltLen s₀) = bytesAt s₀.mem (salt s₀) (saltLen s₀) :=
    (k.upd (by decide) u).saltB hp
  rw [hs] at hi ho
  exact ⟨k', hi, ho⟩

end

/-! ## `update` -/

/-- After `update`'s arguments. -/
def XUA (w : MdHash) (s₀ t : State) : Prop :=
  XI w s₀ t ∧ t.gpr .rdi = sA s₀ xIn ∧ t.gpr .rsi = BitVec.ofNat 64 w.H.P.B ∧ t.gpr .rdx = ikm s₀ ∧
    t.gpr .rcx = s₀.gpr .rcx ∧ t.gpr .r8 = sA s₀ xWork

/-- After `update`: the inner state holds the input keying material too. -/
def XU (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ w.ok.SH.Repr t.mem (sA s₀ xIn) (xorPad (k0Of w s₀) ipad ++ ikmOf s₀) ∧
    w.ok.SH.Repr t.mem (sA s₀ xOut) (xorPad (k0Of w s₀) opad)

theorem upd_eq : extractUpd = [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 xIn)),
    .mov .rsi (.mem (at_ .r13 40)), .mov .rdx (.reg .rbx), .mov .rcx (.reg .rbp), .mov .r8 (.reg .rsp),
    .alu .add .r8 (.imm (BitVec.ofNat 32 xWork))] := rfl

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem updArgs_ok {t : State} (h : XI w s₀ t) : WP isa (.block extractUpd) t (XUA w s₀) := by
  obtain ⟨k, hI, hO⟩ := h
  rw [upd_eq]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => ?_
  have k₂ : XR w s₀ t₂ := (k.upd (by decide) u₁).upd (by decide) u₂
  have r13 : t₂.gpr .r13 = tab s₀ := k₂.r13
  refine wp_movm (a := tab s₀ + BitVec.ofNat 64 40) (by rw [ea_at, r13]) (tin hp k₂ (by decide)) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_mov fun t₅ u₅ => wp_mov fun t₆ u₆ => wp_addi fun t₇ u₇ => WP.block_nil ?_
  have k₇ : XR w s₀ t₇ :=
    ((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  have m₇ : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨k₇, by rw [m₇]; exact hI, by rw [m₇]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.gpr, k.rsp, sx32]
  · upd_simp [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, m₂]
    rw [k.tabW hp (by decide)]; exact hp.tB
  · upd_simp [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, k.rbx]
  · upd_simp [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, k.rbp]
  · upd_simp [u₇.gpr, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, k.rsp, sx416]

/-- `update`'s arguments, after the load of its address. -/
theorem upd_args {t t' : State} (h : XUA w s₀ t) {v : Addr} (u : Upd t t' .r11 v) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs w.ok.stream t' (sA s₀ xIn) (ikm s₀) (sA s₀ xWork) (ikmLen s₀) := by
  obtain ⟨⟨k, -, -⟩, a0, -, a2, a3, a8⟩ := h
  have g : ∀ r, r ≠ .r11 → t'.gpr r = t.gpr r := u.other
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide), k.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 16) (stk s₀) := below_stk sp' (by decide)
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  have hfr := xFr_eq
  have hwk : work = 3104 := rfl
  have hWw : w.ok.stream.Wb ≤ work := by omega_using [hWb, hwk]
  have hSS : w.H.stream.S = w.H.S := rfl
  exact
    { rdi := by rw [g _ (by decide), a0]
      rdx := by rw [g _ (by decide), a2]
      rcx := by rw [g _ (by decide), a3]
      r8 := by rw [g _ (by decide), a8]
      cd := VG.Covers.left (by rw [u.rd, k.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
      cw := by
        rw [u.wr, k.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨frR s₀, by simp, xIn, rfl, by dsimp only; simp only [xIn]; omega_using [hSS, hS, hfr]⟩
        · exact ⟨frR s₀, by simp, xWork, rfl, by dsimp only; simp only [xWork]; omega_using [hWw, hfr, hwk]⟩
      st_sc := in_work hp hWw
      d_st := hp.f_i.symm.sub_right (inR hp)
      d_sc := hp.f_i.symm.sub_right (workR hWw)
      stk_st := (stk_fr hp (by simp only [xIn]; omega_using [hSS, hS, hfr])).sub_left hb
      stk_d := hp.b_i.sub_left hb
      stk_sc := (stk_fr hp (by simp only [xWork]; omega_using [hWw, hfr, hwk])).sub_left hb }

theorem upd_ok {t : State} (h : XUA w s₀ t) : WP isa (tcall .r13 1 f.upd) t (XU w s₀) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload hp k (j := 1) (by decide)) fun t' u => ?_)
  have hr11 : t'.gpr .r11 = s₀.syms w.H.updN := by rw [u.gpr]; exact hp.tmem.2.1
  refine WP.icalls_of_call (a := t'.gpr .r11) (n := w.H.updN) (c := w.H.updC) rfl ?_ (WP.of_syms ?_)
  · show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .r11) = _
    rw [hr11, u.syms, k.sy]; exact hp.tok.u
  have hI := h.1.2.1
  have hO := h.1.2.2
  have a1 := h.2.2.1
  have hWb := hp.hw.hWb
  have hS := hp.hw.hS
  have hfr' := xFr_eq
  have hwk : work = 3104 := rfl
  have hWw : w.ok.stream.Wb ≤ work := by omega_using [hWb, hwk]
  have hSS : w.H.stream.S = w.H.S := rfl
  refine Proof.Pbkdf2.Md.X86_64.Calls.upd_call w.ok.stream (upd_args hp h u) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
    fun s' a hr hsy => ?_
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [u.other _ (by decide), k.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 16) (stk s₀) := below_stk sp' (by decide)
  have k' : XR w s₀ s' := (k.upd (by decide) u).keep hp a.rd a.wr hsy a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨xIn, _, rfl, by decide, by simp only [xIn]; omega_using [hSS, hS, hfr']⟩
    · exact .inl ⟨xWork, _, rfl, by decide, by simp only [xWork]; omega_using [hWw, hfr', hwk]⟩
    · exact .inr (.inr ⟨16, by rw [sp'], by decide⟩)
  have hm : t'.mem = t.mem := u.mem
  have hl : (xorPad (k0Of w s₀) ipad).length = w.H.P.B := by
    rw [VG.Proof.Hmac.Common.xorPad_length, blockKey_length]
  refine ⟨k', ?_, ?_⟩
  · have := hr _ (by rw [hm]; exact hI) (by rw [u.other _ (by decide), a1, hl])
    rwa [show bytesAt t'.mem (ikm s₀) (ikmLen s₀) = ikmOf s₀ from (k.upd (by decide) u).ikmB hp] at this
  · refine repr_keep (w := w) (m := t'.mem) (fun i hi => ?_) (by rw [hm]; exact hO)
    refine (a.frame.bytes (R := ⟨sA s₀ xOut, w.H.S⟩) (fun r hr => ?_) (by show w.H.S ≤ 2 ^ 64; omega_using [hS]) hi)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (in_out hp).symm
    · exact out_work hp hWw
    · exact ((stk_fr hp (by simp only [xOut]; omega_using [hSS, hS, hfr'])).sub_left hb).symm

end

/-! ## `finalize` -/

/-- After `finalize`'s arguments. -/
def XFA (w : MdHash) (s₀ t : State) : Prop :=
  XU w s₀ t ∧ t.gpr .rdi = sA s₀ xIn ∧ t.gpr .rsi = sA s₀ xOut ∧
    t.gpr .rdx = BitVec.ofNat 64 w.H.P.B + s₀.gpr .rcx ∧ t.gpr .rcx = prk s₀ ∧ t.gpr .r8 = sA s₀ xWork

/-- After `finalize`: `PRK`. -/
def XF (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ bytesAt t.mem (prk s₀) w.H.D = hmacBlockKey w.ok.SH.H (k0Of w s₀) (ikmOf s₀)

theorem fin_eq : extractFin = [.mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 xIn)),
    .mov .rsi (.reg .rsp), .alu .add .rsi (.imm (BitVec.ofNat 32 xOut)), .mov .rdx (.mem (at_ .r13 40)),
    .alu .add .rdx (.reg .rbp), .mov .rcx (.reg .r12), .mov .r8 (.reg .rsp),
    .alu .add .r8 (.imm (BitVec.ofNat 32 xWork))] := rfl

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem finArgs_ok {t : State} (h : XU w s₀ t) : WP isa (.block extractFin) t (XFA w s₀) := by
  obtain ⟨k, hI, hO⟩ := h
  rw [fin_eq]
  refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_addi fun t₄ u₄ => ?_
  have k₄ : XR w s₀ t₄ := (((k.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  refine wp_movm (a := tab s₀ + BitVec.ofNat 64 40) (by rw [ea_at, k₄.r13]) (tin hp k₄ (by decide)) fun t₅ u₅ => ?_
  refine wp_add fun t₆ u₆ => wp_mov fun t₇ u₇ => wp_mov fun t₈ u₈ => wp_addi fun t₉ u₉ => WP.block_nil ?_
  have k₉ : XR w s₀ t₉ :=
    (((((k₄.upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇).upd (by decide) u₈).upd (by decide) u₉)
  have m₉ : t₉.mem = t.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨k₉, by rw [m₉]; exact hI, by rw [m₉]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.gpr, k.rsp, sx32]
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.gpr, u₂.other, u₁.other, k.rsp, sx224]
  · upd_simp [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.gpr, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other,
      k.rbp, m₄]
    rw [k.tabW hp (by decide), hp.tB]
  · upd_simp [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, k.r12]
  · upd_simp [u₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, k.rsp, sx416]

/-- `finalize`'s arguments, after the load of its address. -/
theorem fin_args {t t' : State} (h : XFA w s₀ t) {v : Addr} (u : Upd t t' .r11 v) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := w.H) t' (sA s₀ xIn) (sA s₀ xOut)
      (BitVec.ofNat 64 w.H.P.B + s₀.gpr .rcx) (prk s₀) (sA s₀ xWork) := by
  obtain ⟨⟨k, -, -⟩, a0, a1, a2, a3, a8⟩ := h
  have g : ∀ r, r ≠ .r11 → t'.gpr r = t.gpr r := u.other
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide), k.rsp]
  have hb : Region.Sub (below (t'.gpr .rsp) 24) (stk s₀) := below_stk sp' (by decide)
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hfr := xFr_eq
  have hwk : work = 3104 := rfl
  have hWw : 8 * w.H.W ≤ work := by omega_using [hW, hwk]
  exact
    { rdi := by rw [g _ (by decide), a0]
      rsi := by rw [g _ (by decide), a1]
      rdx := by rw [g _ (by decide), a2]
      rcx := by rw [g _ (by decide), a3]
      r8 := by rw [g _ (by decide), a8]
      cr := by
        rw [u.rd, u.wr, k.rd, k.wr, hp.rd, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨frR s₀, by simp, xOut, rfl, by dsimp only; simp only [xOut]; omega_using [hS, hfr]⟩
      cw := by
        rw [u.wr, k.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨frR s₀, by simp, xIn, rfl, by dsimp only; simp only [xIn]; omega_using [hS, hfr]⟩
        · exact ⟨prkR w s₀, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; omega_using []⟩
        · exact ⟨frR s₀, by simp, xWork, rfl, by dsimp only; simp only [xWork]; omega_using [hWw, hfr, hwk]⟩
      i_u := in_out hp
      i_o := hp.f_p.sub_left (inR hp)
      i_s := in_work hp hWw
      u_o := hp.f_p.sub_left (outR hp)
      u_s := out_work hp hWw
      o_s := (hp.f_p.sub_left (workR hWw)).symm
      stk_i := (stk_fr hp (by simp only [xIn]; omega_using [hS, hfr])).sub_left hb
      stk_u := (stk_fr hp (by simp only [xOut]; omega_using [hS, hfr])).sub_left hb
      stk_o := hp.b_p.sub_left hb
      stk_s := (stk_fr hp (by simp only [xWork]; omega_using [hWw, hfr, hwk])).sub_left hb
      scnw := by
        rw [sA_toNat hp (by simp only [xWork]; omega_using [hfr])]
        have := hp.top; simp only [xWork]; omega_using [hWw, hfr, hwk, this] }

theorem fin_ok {t : State} (h : XFA w s₀ t) : WP isa (tcall .r13 2 f.fin) t (XF w s₀) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload hp k (j := 2) (by decide)) fun t' u => ?_)
  have hr11 : t'.gpr .r11 = s₀.syms w.H.hmacFinN := by rw [u.gpr]; exact hp.tmem.2.2
  refine WP.icalls_of_call (a := t'.gpr .r11) (n := w.H.hmacFinN) (c := w.H.hmacFin) rfl ?_ (WP.of_syms ?_)
  · show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .r11) = _
    rw [hr11, u.syms, k.sy]; exact hp.tok.f
  have hI := h.1.2.1
  have hO := h.1.2.2
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hfr' := xFr_eq
  have hwk : work = 3104 := rfl
  have hWw : 8 * w.H.W ≤ work := by omega_using [hW, hwk]
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call w.ok (hF w) (hFsp w) (hFd w) (fin_args hp h u)
    fun s' hrd hwr hcs hf hpost hsy => ?_
  have sp' : t'.gpr .rsp = s₀.gpr .rsp := by rw [u.other _ (by decide), k.rsp]
  have k' : XR w s₀ s' := (k.upd (by decide) u).keep hp hrd hwr hsy hcs hf fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨xIn, _, rfl, by decide, by simp only [xIn]; omega_using [hS, hfr']⟩
    · exact .inr (.inl fun _ h => h)
    · exact .inl ⟨xWork, _, rfl, by decide, by simp only [xWork]; omega_using [hWw, hfr', hwk]⟩
    · exact .inr (.inr ⟨24, by rw [sp'], by decide⟩)
  have hm : t'.mem = t.mem := u.mem
  have hl : (k0Of w s₀).length = w.H.P.B := blockKey_length w _
  have hil : (ikmOf s₀).length = ikmLen s₀ := VG.Proof.Hmac.Common.bytesAt_length _ _ _
  have hlt := ikm_lt hp
  refine ⟨k', hpost _ _ hl (by rw [hl, hil]; exact hlt) (by rw [hm]; exact hI) ?_ (by rw [hm]; exact hO)⟩
  rw [hil]
  apply BitVec.eq_of_toNat_eq
  have hd := (s₀.gpr .rcx).isLt
  have he : ikmLen s₀ = (s₀.gpr .rcx).toNat := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hlt, hd, he]

end

/-! ## The epilogue, and the function -/

theorem epi_eq : extractEpi = Spill.restoreCode .rsp savedL := rfl

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- The frame's body: our caller's registers restored, and `PRK`. -/
theorem main_ok : WP isa (extractMain f) s₀ fun u => (∀ r ∈ calleeSaved, u.gpr r = s₀.gpr r) ∧
      u.wr = s₀.wr ∧ u.mem.readW (sA s₀ xFr) 64 = s₀.mem.readW (sA s₀ xFr) 64 ∧
      bytesAt u.mem (prk s₀) w.H.D = hmacBlockKey w.ok.SH.H (k0Of w s₀) (ikmOf s₀) := by
  have hfr := xFr_eq
  unfold extractMain
  simp only [Impl.Mgf1.X86_64.seqs]
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => WP.seq (WP.mono (init_ok hp h₁) fun t₂ h₂ =>
    WP.seq (WP.mono (updArgs_ok hp h₂) fun t₃ h₃ => WP.seq (WP.mono (upd_ok hp h₃) fun t₄ h₄ =>
    WP.seq (WP.mono (finArgs_ok hp h₄) fun t₅ h₅ => WP.seq (WP.mono (fin_ok hp h₅) fun t₆ ⟨k₆, hP⟩ => ?_))))))
  rw [epi_eq]
  refine WP.mono (Spill.restore_ok .rsp savedL s₀.gpr t₆ (by decide)
    (fun q hq => by rw [k₆.rsp]; exact in_fr hp k₆.wr (by have := saved_in q hq; omega_using [hfr, this]))
    (by rw [k₆.rsp]; exact k₆.saved)) fun u ⟨h₁, h₂, hm, _, hwr⟩ => ⟨fun r hr => ?_, by rw [hwr, k₆.wr], ?_,
      by rw [hm]; exact hP⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h₁ _ (by decide)
    · exact h₁ _ (by decide)
    · rw [h₂ _ (by decide), k₆.rsp]
    · exact h₁ _ (by decide)
    · exact h₁ _ (by decide)
    · rw [h₂ _ (by decide), k₆.r14]
    · rw [h₂ _ (by decide), k₆.r15]
  · rw [hm]
    refine k₆.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    have top := hp.top
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [top])
    · exact hp.r_p
    · exact (stk_fr hp (o := xFr) (n := 8) (by omega_using [hfr])).symm

end

/-- `vg_hkdf_extract`, in its frame. -/
theorem extract_correct {w : MdHash} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (extractR w f ns xStack).pre s) :
    WP isa (extract f) s fun s' => gprPreserved s s' ∧ (extractR w f ns xStack).post s s' := by
  have hsp : xStack ≤ (s.gpr .rsp).toNat := hp.1
  have p := pre_alloc hw hp
  unfold extract
  refine alloc_frame_ok (by decide) (by rw [xStack_eq] at hsp; rw [xFr_eq]; omega_using [hsp])
    (WP.mono (main_ok p) fun v ⟨hcs, hvwr, hret, hP⟩ => ⟨hcs _ (by decide), hvwr, fun m u hm => ?_⟩)
  have hfrm : ∀ {R : Region}, Region.Disjoint R (frR (allocState xFr s)) → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, m (R.base + BitVec.ofNat 64 i) = v.mem (R.base + BitVec.ofNat 64 i) := by
    intro R hR hl i hi
    refine hm.bytes (R := R) (fun r hr => ?_) hl hi
    simp only [List.mem_singleton] at hr; subst hr
    rw [← allocState_rsp']; exact hR
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; exact freeState_rsp (hcs _ (by decide))
    · show (v.setReg .rsp (v.gpr .rsp + BitVec.ofNat 64 xFr)).gpr r = _
      rw [RegUpd.gpr_setReg_of_ne _ _ hr', hcs r hr, allocState_gpr' _ _ hr']
  · show m.readW (s.gpr .rsp) 64 = _
    rw [← ret_eq s]
    have top := p.top
    refine (hm.readW (r := retR (allocState xFr s)) (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans hret
    simp only [List.mem_singleton] at hr; subst hr
    rw [← allocState_rsp']
    exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [top])
  · show bytesAt m (s.gpr .r8) w.H.D = Spec.Hmac.hmac _ _ _
    have e8 : (allocState xFr s).gpr .r8 = s.gpr .r8 := allocState_gpr' _ _ (by decide)
    have e : bytesAt m (s.gpr .r8) w.H.D = bytesAt v.mem (s.gpr .r8) w.H.D :=
      Proof.Sha256.Stream.bytesAt_congr fun i hi => by
        have := hfrm (R := prkR w (allocState xFr s)) p.f_p.symm (by show w.H.D ≤ 2 ^ 64; have := p.np; omega_using [this]) i hi
        rwa [prkR, prk, e8] at this
    rw [e, ← e8]
    exact hP

/-! ## Constant time -/

open VG.Proof.Hkdf.X86_64 (Ck rel_agree)

/-- Code that leaks the same trace in both runs, with what each run gives. -/
theorem rel_wp {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun _ _ => True)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The indirect call of the table's function `j`, whose address `a` both
runs load. -/
theorem tcall_rel {Φ₁ Φ₂ : State → Prop} {j : Nat} {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} {a : Addr} (hcl : Ck [.r13] (.block [.mov .r11 (.mem (at_ .r13 (8 * j)))]))
    (hag : ∀ s s', Φ₁ s → Φ₂ s' → ∀ r ∈ [Reg.r13], s.gpr r = s'.gpr r)
    (hld₁ : ∀ t, Φ₁ t → WP isa (.block [.mov .r11 (.mem (at_ .r13 (8 * j)))]) t fun u => Upd t u .r11 a)
    (hld₂ : ∀ t, Φ₂ t → WP isa (.block [.mov .r11 (.mem (at_ .r13 (8 * j)))]) t fun u => Upd t u .r11 a)
    (hf₁ : ∀ t, Φ₁ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hf₂ : ∀ t, Φ₂ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hcall : RelCT isa (fun u u' => (∃ t, Φ₁ t ∧ Upd t u .r11 a) ∧ (∃ t', Φ₂ t' ∧ Upd t' u' .r11 a))
      (.call n c) fun _ _ => True) :
    RelCT isa (fun t t' => Φ₁ t ∧ Φ₂ t') (tcall .r13 j ts) fun _ _ => True := by
  unfold tcall
  refine (rel_agree (P₁ := Φ₁) (P₂ := Φ₂) (G₁ := fun u => ∃ t, Φ₁ t ∧ Upd t u .r11 a)
    (G₂ := fun u => ∃ t, Φ₂ t ∧ Upd t u .r11 a) hag hcl
    (fun s h => WP.mono (hld₁ s h) fun u v => ⟨s, h, v⟩)
    (fun s h => WP.mono (hld₂ s h) fun u v => ⟨s, h, v⟩)).seq ?_
  cases ts with
  | nil => exact RelCT.of_false fun s _ h => by obtain ⟨t, ht, -⟩ := h.1; simp at hf₁; exact hf₁ t ht
  | cons q ts =>
    refine RelCT.icalls_of_call hcall ?_
    rintro u u' ⟨⟨t, h, v⟩, ⟨t', h', v'⟩⟩
    refine ⟨a, by simp only [X86_64.icall, v.gpr], by simp only [X86_64.icall, v'.gpr], ?_, ?_, by simp only [X86_64.addrs]⟩
    · show (q :: ts).find? (fun q => u.syms q.1 == a) = _
      rw [v.syms]; exact hf₁ t h
    · show (q :: ts).find? (fun q => u'.syms q.1 == a) = _
      rw [v'.syms]; exact hf₂ t' h'

/-- The registers `XR` fixes that hold the pointers and lengths. -/
abbrev pubRegs : List Reg := [.rsp, .rbx, .rbp, .r12, .r13]

/-- The taint checks of the pieces of `vg_hkdf_extract` between the calls. -/
structure XChecks : Prop where
  pro : Ck [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (.block extractPro)
  tl0 : Ck [.r13] (.block [.mov .r11 (.mem (at_ .r13 (8 * 0)))])
  tl1 : Ck [.r13] (.block [.mov .r11 (.mem (at_ .r13 (8 * 1)))])
  tl2 : Ck [.r13] (.block [.mov .r11 (.mem (at_ .r13 (8 * 2)))])
  ua : Ck pubRegs (.block extractUpd)
  fa : Ck pubRegs (.block extractFin)
  epi : Ck [.rsp] (.block extractEpi)

theorem xchecks : XChecks :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : MdHash) (s₀ s₀' : State) : Prop where
  regs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r
  tab : tab s₀ = tab s₀'
  hi : s₀.syms w.H.hmacInitAnyN = s₀'.syms w.H.hmacInitAnyN
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.H.hmacFinN = s₀'.syms w.H.hmacFinN

section
variable {w : MdHash} {f : Fns} {s₀ s₀' : State} (hp : Pre w f s₀) (hp' : Pre w f s₀')
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
theorem ag {t t' : State} (k : XR w s₀ t) (k' : XR w s₀' t') : ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [k.rsp, k'.rsp]; exact hq.regs .rsp (by simp)
  · rw [k.rbx, k'.rbx]; exact hq.regs .rdx (by simp)
  · rw [k.rbp, k'.rbp]; exact hq.regs .rcx (by simp)
  · rw [k.r12, k'.r12]; exact hq.regs .r8 (by simp)
  · rw [k.r13, k'.r13, hq.tab]

omit hp hp' in
theorem ag13 {t t' : State} (k : XR w s₀ t) (k' : XR w s₀' t') : ∀ r ∈ [Reg.r13], t.gpr r = t'.gpr r :=
  fun r hr => ag hq k k' r (by simp at hr; subst hr; simp)

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (extractMain f) fun _ _ => True := by
  have kc := xchecks
  have e0 := hq.regs .rdi (by simp); have e1 := hq.regs .rsi (by simp); have e2 := hq.regs .rdx (by simp)
  have e3 := hq.regs .rcx (by simp); have e4 := hq.regs .r8 (by simp)
  have esp := hq.regs .rsp (by simp)
  unfold extractMain
  simp only [Impl.Mgf1.X86_64.seqs]
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := XA w s₀) (G₂ := XA w s₀')
    (rs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun s s' hs hs' => by subst hs hs'; exact hq.regs) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => XA w s₀ t ∧ XA w s₀' t') (tcall .r13 0 f.init)
      fun t t' => XI w s₀ t ∧ XI w s₀' t' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.hmacInitAnyN) kc.tl0 (fun t t' k k' => ag13 hq k.1 k'.1)
      (fun t k => WP.mono (tload hp k.1 (j := 0) (by decide)) fun u v => by rwa [show _ = _ from hp.tmem.1] at v)
      (fun t k => WP.mono (tload hp' k.1 (j := 0) (by decide)) fun u v => by
        rwa [show _ = _ from hp'.tmem.1, ← hq.hi] at v)
      (fun t k => by rw [k.1.sy]; exact hp.tok.i) (fun t k => by rw [k.1.sy, hq.hi]; exact hp'.tok.i)
      (Proof.Pbkdf2.Md.X86_64.Any.any_rel (n := w.H.hmacInitAnyN) w.ok w.hmacAny
        fun u u' ⟨⟨t, k, v⟩, ⟨t', k', v'⟩⟩ => ⟨init_args hp k v,
          by have := init_args hp' k' v'; simp only [sA, salt, saltLen] at this ⊢; rwa [← e0, ← e1, ← esp] at this,
          by rw [v.other _ (by decide), v'.other _ (by decide), k.1.rsp, k'.1.rsp, esp]⟩))
      (fun t k => init_ok hp k) (fun t k => init_ok hp' k)
  have r3 := rel_agree (P₁ := XI w s₀) (P₂ := XI w s₀') (G₁ := XUA w s₀) (G₂ := XUA w s₀') (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.ua (fun t k => updArgs_ok hp k) (fun t k => updArgs_ok hp' k)
  have r4 : RelCT isa (fun t t' => XUA w s₀ t ∧ XUA w s₀' t') (tcall .r13 1 f.upd)
      fun t t' => XU w s₀ t ∧ XU w s₀' t' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' k k' => ag13 hq k.1.1 k'.1.1)
      (fun t k => WP.mono (tload hp k.1.1 (j := 1) (by decide)) fun u v => by rwa [show _ = _ from hp.tmem.2.1] at v)
      (fun t k => WP.mono (tload hp' k.1.1 (j := 1) (by decide)) fun u v => by
        rwa [show _ = _ from hp'.tmem.2.1, ← hq.up] at v)
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.u) (fun t k => by rw [k.1.1.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.X86_64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, k, v⟩, ⟨t', k', v'⟩⟩ => ⟨upd_args hp k v,
        by have := upd_args hp' k' v'; simp only [sA, ikm, ikmLen] at this ⊢; rwa [← e2, ← e3, ← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), k.2.2.1, k'.2.2.1],
        by rw [v.other _ (by decide), v'.other _ (by decide), k.1.1.rsp, k'.1.1.rsp, esp]⟩))
      (fun t k => upd_ok hp k) (fun t k => upd_ok hp' k)
  have r5 := rel_agree (P₁ := XU w s₀) (P₂ := XU w s₀') (G₁ := XFA w s₀) (G₂ := XFA w s₀') (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.fa (fun t k => finArgs_ok hp k) (fun t k => finArgs_ok hp' k)
  have r6 : RelCT isa (fun t t' => XFA w s₀ t ∧ XFA w s₀' t') (tcall .r13 2 f.fin)
      fun t t' => XF w s₀ t ∧ XF w s₀' t' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.hmacFinN) kc.tl2 (fun t t' k k' => ag13 hq k.1.1 k'.1.1)
      (fun t k => WP.mono (tload hp k.1.1 (j := 2) (by decide)) fun u v => by rwa [show _ = _ from hp.tmem.2.2] at v)
      (fun t k => WP.mono (tload hp' k.1.1 (j := 2) (by decide)) fun u v => by
        rwa [show _ = _ from hp'.tmem.2.2, ← hq.hf] at v)
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.f) (fun t k => by rw [k.1.1.sy, hq.hf]; exact hp'.tok.f)
      (Proof.Pbkdf2.Md.X86_64.Pbk.hfin_rel w.ok (hF w) fun u u' ⟨⟨t, k, v⟩, ⟨t', k', v'⟩⟩ => ⟨fin_args hp k v,
        by have := fin_args hp' k' v'; simp only [sA, prk] at this ⊢; rwa [← e3, ← e4, ← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), k.1.1.rsp, k'.1.1.rsp, esp]⟩))
      (fun t k => fin_ok hp k) (fun t k => fin_ok hp' k)
  have hfr := xFr_eq
  have r7 := rel_agree (P₁ := XF w s₀) (P₂ := XF w s₀') (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [.rsp])
    (fun t t' k k' r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [k.1.rsp, k'.1.rsp, esp]) kc.epi
    (fun t k => by
      rw [epi_eq]
      exact WP.mono (Spill.restore_ok .rsp savedL s₀.gpr t (by decide)
        (fun q hq => by rw [k.1.rsp]; exact in_fr hp k.1.wr (by have := saved_in q hq; omega_using [hfr, this]))
        (by rw [k.1.rsp]; exact k.1.saved)) fun _ _ => trivial)
    (fun t k => by
      rw [epi_eq]
      exact WP.mono (Spill.restore_ok .rsp savedL s₀'.gpr t (by decide)
        (fun q hq => by rw [k.1.rsp]; exact in_fr hp' k.1.wr (by have := saved_in q hq; omega_using [hfr, this]))
        (by rw [k.1.rsp]; exact k.1.saved)) fun _ _ => trivial)
  exact ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ _ => trivial)

end

/-- `vg_hkdf_extract` is constant time: two runs whose public data agree
leak the same trace. -/
theorem extract_ct {w : MdHash} {f : Fns} {ns : List String} (hw : HOk w)
    (hns : ∀ n ∈ [w.H.hmacInitAnyN, w.H.updN, w.H.hmacFinN], n ∈ ns) :
    ConstantTime isa (extractR w f ns xStack).pre (extractR w f ns xStack).pub (extract f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc hw h; have hp' := pre_alloc hw h'
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, q6, qn⟩ := hpub
  have hq : PubEq w (allocState xFr e) (allocState xFr e') :=
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
      by rw [tab_alloc, tab_alloc, q6], qn _ (hns _ (by simp)), qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (extract f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold extract
  refine RelCT.alloc (R := fun _ _ => True) ((main_rel hp hp' hq).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.X86_64.Extract
