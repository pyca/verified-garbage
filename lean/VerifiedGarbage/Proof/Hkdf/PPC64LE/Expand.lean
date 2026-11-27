module

public import VerifiedGarbage.Proof.Hkdf.PPC64LE.Key
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Hkdf.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith

/-!
# HKDF on PPC64LE: `vg_hkdf_expand`, correct

The contract the proof is written against (`expandR`), for the table `hmac`
of one hash function `w` (`HVar`), whose functions an indirect call of `f`'s
reaches: `expand(key, info, info_len, out, out_len, hmac)` writes
HKDF-Expand's `out_len` bytes to `out`, for every pseudorandom key the
states at `key` are keyed with (`Spec.Hkdf.Keyed`). The stack the function
uses (`eStack` bytes) is, from its lowest byte `L` up, the 96 bytes the
functions it calls use and its frame (`eFr` bytes: the return address and
our caller's `r14`–`r23` at `L + 128`, the working state at `L + 216`,
`T(i)` at `L + 408`, the counter's byte at `L + 472`, the working space at
`L + 480`). The prologue saves the return address and our caller's
registers, and keeps the arguments, `D`, `B`, the length of `T(i - 1)` and
the counter in `r14`–`r23` (`pro_ok`, from which on `ER` holds). Each block
(`block_ok`) makes the working state the inner state at `key` (a copy of
its hash value), absorbs `T(i - 1)`, `info` and the counter, finalizes with
the outer state at `key + 192` into `T(i)` in the frame, and copies its
first `min(D, rem)` bytes to `out`; before block `i + 1`, `out`'s first
`min(i D, L)` bytes are `T(1) ‖ … ‖ T(i)`'s (`EI`). The blocks run while
bytes of `out` are left (`loop_ok`), and the epilogue restores the return
address and our caller's registers.
-/

@[expose] public section

namespace VG.Proof.Hkdf.PPC64LE.Expand

open VG.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_mov wp_addi wp_add wp_sub wp_and wp_lsr wp_li wp_addSp
  wp_ld wp_std wp_stb wp_mflr wp_mtlr)
open VG.Impl.Hkdf.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.RsaOaep.PPC64LE (Fns copyLoop)
open VG.Proof.HmacTable.PPC64LE (HVar TabOK TabMem)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

/-- `expand(key, info, info_len, out, out_len, hmac)`, with `N` bytes of
stack, for the table `hmac` of `w`, whose functions an indirect call of `f`'s
reaches, with the addresses of the functions `ns` public. -/
def expandR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let info : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let out : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let tab : Region := ⟨s.gpr .r8, 48⟩
    let stk : Region := below s.sp N
    s.rd = [key, info, tab] ∧ s.wr = [out] ∧ (s.gpr .r7).toNat ≤ 255 * w.H.D ∧
      key.Disjoint out ∧ info.Disjoint out ∧ tab.Disjoint out ∧ N ≤ s.sp.toNat ∧
      stk.Disjoint key ∧ stk.Disjoint info ∧ stk.Disjoint out ∧ stk.Disjoint tab ∧
      (s.gpr .r3).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 48 ≤ 2 ^ 64 ∧
      TabMem w s.syms (s.gpr .r8) s.mem ∧
      s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B ∧ TabOK w f s.syms
  post s s' := ∀ prk, Spec.Hkdf.Keyed w.ok.SH s.mem (s.gpr .r3) prk →
    Spec.Hkdf.expand w.ok.SH.H w.H.D prk (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) (s.gpr .r7).toNat =
      some (bytesAt s'.mem (s.gpr .r6) (s.gpr .r7).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_expand` uses: its frame, and below it what HMAC's
functions use. -/
def eStack : Nat := eFr + 96

theorem eFr_eq : eFr = 2256 := rfl
theorem eStack_eq : eStack = 2352 := rfl

section
variable (s₀ : State)

/-- The arguments, on entry to the frame's body. -/
abbrev key : Addr := s₀.gpr .r3
abbrev info : Addr := s₀.gpr .r4
abbrev infoLen : Nat := (s₀.gpr .r5).toNat
abbrev out : Addr := s₀.gpr .r6
abbrev outLen : Nat := (s₀.gpr .r7).toNat
abbrev tab : Addr := s₀.gpr .r8

abbrev keyR : Region := ⟨key s₀, 384⟩
abbrev infoR : Region := ⟨info s₀, infoLen s₀⟩
abbrev outR : Region := ⟨out s₀, outLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩

end

/-- An address of the stack, from its lowest byte. -/
abbrev at_ (L : Addr) (d : Nat) : Addr := L + BitVec.ofNat 64 d

/-- The stack the function uses. -/
abbrev stkR (L : Addr) : Region := ⟨L, eStack⟩

/-- The regions the frame's body writes. -/
abbrev wrs (s₀ : State) (L : Addr) : List Region := [stkR L, outR s₀]

/-- The state the frame's body starts in, from the stack's lowest byte `L`. -/
structure Pre (w : HVar) (f : Fns) (s₀ : State) (L : Addr) : Prop where
  sp : s₀.sp = at_ L 96
  nL : L.toNat + eStack ≤ 2 ^ 64
  rd : s₀.rd = [keyR s₀, infoR s₀, tabR s₀]
  wr : s₀.wr = [⟨at_ L 128, 2224⟩, outR s₀]
  ol : outLen s₀ ≤ 255 * w.H.D
  k_o : (keyR s₀).Disjoint (outR s₀)
  i_o : (infoR s₀).Disjoint (outR s₀)
  t_o : (tabR s₀).Disjoint (outR s₀)
  s_k : (stkR L).Disjoint (keyR s₀)
  s_i : (stkR L).Disjoint (infoR s₀)
  s_o : (stkR L).Disjoint (outR s₀)
  s_t : (stkR L).Disjoint (tabR s₀)
  nk : (key s₀).toNat + 384 ≤ 2 ^ 64
  ni : (info s₀).toNat + infoLen s₀ ≤ 2 ^ 64
  no : (out s₀).toNat + outLen s₀ ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w s₀.syms (tab s₀) s₀.mem
  tD : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B
  tok : TabOK w f s₀.syms

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hp : (expandR w f ns eStack).pre s) :
    Pre w f (allocated eFr s) (s.sp - BitVec.ofNat 64 eStack) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := hp
  obtain ⟨e₀, -, hn⟩ := alloc_at s (F := eFr) (C := 96) h7
  have hfr : Region.Sub ⟨s.sp - BitVec.ofNat 64 eFr, 8⟩ ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  have hm := alloc_mem s eFr
  have hd : ∀ r' ∈ [(⟨s.sp - BitVec.ofNat 64 eFr, 8⟩ : Region)], Region.Disjoint ⟨s.gpr .r8, 48⟩ r' :=
    fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact (h11.sub_left hfr).symm
  refine ⟨e₀, hn, h1, ?_, h3, h4, h5, h6, h8, h9, h10, h11, h12, h13, h14, h15, ?_, ?_, ?_, h19⟩
  · show (⟨s.sp - BitVec.ofNat 64 eFr + 32, eFr - 32⟩ : Region) :: s.wr = _
    rw [h2, e₀, show (32 : Addr) = BitVec.ofNat 64 32 from rfl, Offset.add_add]; rfl
  · obtain ⟨t0, t1, t2⟩ := h16
    refine ⟨?_, ?_, ?_⟩
    · show (allocated eFr s).mem.readW (s.gpr .r8 + BitVec.ofNat 64 0) 64 = s.syms w.initN
      rw [hm.readW (r := ⟨s.gpr .r8, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact t0
    · show (allocated eFr s).mem.readW (s.gpr .r8 + BitVec.ofNat 64 8) 64 = s.syms w.H.updN
      rw [hm.readW (r := ⟨s.gpr .r8, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact t1
    · show (allocated eFr s).mem.readW (s.gpr .r8 + BitVec.ofNat 64 16) 64 = s.syms w.finN
      rw [hm.readW (r := ⟨s.gpr .r8, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact t2
  · show (allocated eFr s).mem.readW (s.gpr .r8 + BitVec.ofNat 64 32) 64 = _
    rw [hm.readW (r := ⟨s.gpr .r8, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact h17
  · show (allocated eFr s).mem.readW (s.gpr .r8 + BitVec.ofNat 64 40) 64 = _
    rw [hm.readW (r := ⟨s.gpr .r8, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact h18

end

/-! ## What every piece keeps -/

/-- The registers `expand` saves. -/
abbrev eregs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23]

/-- The registers kept from the end of the prologue on, and memory. -/
structure ER (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  r14 : t.gpr .r14 = tab s₀
  r15 : t.gpr .r15 = key s₀
  r16 : t.gpr .r16 = info s₀
  r17 : t.gpr .r17 = s₀.gpr .r5
  r20 : t.gpr .r20 = BitVec.ofNat 64 w.H.D
  r21 : t.gpr .r21 = BitVec.ofNat 64 w.H.B
  cs : ∀ r ∈ preserved, r ∉ eregs → t.gpr r = s₀.gpr r
  saved : Spill.Saved (at_ L 96) s₀.gpr eSaved t.mem
  svlr : t.mem.readW (at_ L 128) 64 = s₀.lr
  frame : Frame (wrs s₀ L) s₀.mem t.mem

theorem saved_fits : Spill.Fits eSaved := by decide

theorem saved_in : ∀ q ∈ eSaved, 32 ≤ q.2 ∧ q.2 + 8 ≤ 32 + 88 := by decide

/-- The save area: the return address and our caller's registers. -/
abbrev svR (L : Addr) : Region := ⟨at_ L 128, 88⟩

/-- A part of the stack apart from the save area, or of `out`. -/
def Wk (s₀ : State) (L : Addr) (r : Region) : Prop :=
  (Region.Sub r (stkR L) ∧ (svR L).Disjoint r) ∨ Region.Sub r (outR s₀)

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L)
include hp

omit hp in
theorem svR_sub : Region.Sub (svR L) (stkR L) := Offset.sub_base _ (by decide)

theorem Wk.ok {r : Region} (h : Wk s₀ L r) : (svR L).Disjoint r ∧ ∃ r' ∈ wrs s₀ L, Region.Sub r r' := by
  rcases h with ⟨h₁, h₂⟩ | h
  · exact ⟨h₂, _, by simp, h₁⟩
  · exact ⟨(hp.s_o.sub_left svR_sub).sub_right h, _, by simp, h⟩

theorem ER.keep {t t' : State} (h : ER w s₀ L t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk s₀ L r) : ER w s₀ L t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide)).trans h.r14,
    (hg _ (by decide)).trans h.r15, (hg _ (by decide)).trans h.r16, (hg _ (by decide)).trans h.r17,
    (hg _ (by decide)).trans h.r20, (hg _ (by decide)).trans h.r21,
    fun r hr hk => (hg r hr).trans (h.cs r hr hk),
    h.saved.frame_in saved_in hf fun r hr => by
      rw [at_, Offset.add_add]; exact (Wk.ok hp (hw r hr)).1,
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Wk.ok hp (hw r hr)).1).sub_left
      (Region.sub_prefix (by decide))) (by decide)]; exact h.svlr,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem ER.same {t t' : State} (h : ER w s₀ L t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) : ER w s₀ L t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide)).trans h.r14,
    (hg _ (by decide)).trans h.r15, (hg _ (by decide)).trans h.r16, (hg _ (by decide)).trans h.r17,
    (hg _ (by decide)).trans h.r20, (hg _ (by decide)).trans h.r21,
    fun r hr hk => (hg r hr).trans (h.cs r hr hk), by rw [hm]; exact h.saved, by rw [hm]; exact h.svlr,
    by rw [hm]; exact h.frame⟩

omit hp in
/-- Code that writes only volatile registers, and no memory. -/
theorem ER.only {t t' : State} (h : ER w s₀ L t) {rs : List Reg} (o : Only rs t t') (hsy : t'.syms = t.syms)
    (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : ER w s₀ L t' :=
  h.same o.rd o.wr o.sp hsy (keep_pres o.keep hrs) o.mem

omit hp in
/-- Code that also writes the registers that count. -/
theorem ER.samec {t t' : State} (h : ER w s₀ L t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ preserved, r ∉ ([.r18, .r19, .r22, .r23] : List Reg) → t'.gpr r = t.gpr r)
    (hm : t'.mem = t.mem) : ER w s₀ L t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide) (by decide)).trans h.r14,
    (hg _ (by decide) (by decide)).trans h.r15, (hg _ (by decide) (by decide)).trans h.r16,
    (hg _ (by decide) (by decide)).trans h.r17, (hg _ (by decide) (by decide)).trans h.r20,
    (hg _ (by decide) (by decide)).trans h.r21,
    fun r hr hk => (hg r hr (by revert hk; revert r; decide)).trans (h.cs r hr hk), by rw [hm]; exact h.saved,
    by rw [hm]; exact h.svlr, by rw [hm]; exact h.frame⟩

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem ER.bytes {t : State} (hk : ER w s₀ L t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs s₀ L, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

/-- The bytes of `key`'s and `info`'s regions are those on entry. -/
theorem ER.keyB {t : State} (hk : ER w s₀ L t) {o n : Nat} (hon : o + n ≤ 384) (i : Nat) (hi : i < n) :
    t.mem (key s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hs : Region.Sub ⟨key s₀ + BitVec.ofNat 64 o, n⟩ (keyR s₀) := Offset.sub_base _ hon
  exact hk.frame.bytes (R := ⟨key s₀ + BitVec.ofNat 64 o, n⟩) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_k.symm.sub_left hs
    · exact hp.k_o.sub_left hs) (by show n ≤ 2 ^ 64; omega_using [hon]) hi

theorem ER.infoB {t : State} (hk : ER w s₀ L t) :
    bytesAt t.mem (info s₀) (infoLen s₀) = bytesAt s₀.mem (info s₀) (infoLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_i.symm
    · exact hp.i_o) (Nat.le_of_lt (s₀.gpr .r5).isLt)

/-- A word of the table is as on entry. -/
theorem ER.tabW {t : State} (hk : ER w s₀ L t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tabR s₀) (Offset.contains_base _ ho (by omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.s_t.symm
      · exact hp.t_o) (by decide)

/-- The table's word at `o`, readable. -/
theorem tin {t : State} (hrd : t.rd = s₀.rd) {o : Nat} (ho : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
  ⟨tabR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp),
    Offset.contains_base _ ho (by omega_using [ho])⟩

/-- A part of the frame's local variable space is writable. -/
theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 2352) :
    InRegions t.wr (at_ L d) n := by
  rw [hwr, hp.wr]; exact in_at L _ h₁ (by omega_using [h₂]) (by decide)

theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 2352) :
    InRegions (t.rd ++ t.wr) (at_ L d) n :=
  let ⟨r, hr, hc⟩ := in_frw hp hwr h₁ h₂; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A part of the stack apart from the save area. -/
theorem wk_at {d n : Nat} (h₁ : 216 ≤ d ∨ d + n ≤ 128) (h₂ : d + n ≤ 2352) : Wk s₀ L ⟨at_ L d, n⟩ :=
  .inl ⟨Offset.sub_base _ (by rw [eStack_eq]; exact h₂), Offset.disjoint _ (by omega_using [h₁])
    (by decide) (by have := hp.nL; rw [eStack_eq] at this; omega_using [this, h₂])⟩

omit hp in
/-- A region at `L + d` of `n` bytes, within the stack. -/
theorem st_sub {d n : Nat} (h : d + n ≤ 2352) : Region.Sub ⟨at_ L d, n⟩ (stkR L) :=
  Offset.sub_base _ (by rw [eStack_eq]; exact h)

/-- Two regions of the stack apart. -/
theorem st_dis {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (h₁ : d + n ≤ 2352) (h₂ : e + k ≤ 2352) :
    Region.Disjoint ⟨at_ L d, n⟩ ⟨at_ L e, k⟩ :=
  Offset.disjoint _ h (by have := hp.nL; rw [eStack_eq] at this; omega_using [this, h₁])
    (by have := hp.nL; rw [eStack_eq] at this; omega_using [this, h₂])

theorem st_nw {d n : Nat} (h : d + n ≤ 2352) (hd : d < 2352 := by decide) : (at_ L d).toNat + n ≤ 2 ^ 64 := by
  have := hp.nL; rw [eStack_eq] at this
  rw [at_, toNat_at (by omega_using [this, hd])]; omega_using [this, h]

/-- The stack pointer is above the stack the callees use. -/
theorem sp_ge {t : State} (ht : t.sp = s₀.sp) {n : Nat} (hn : n ≤ 96) : n ≤ t.sp.toNat := by
  have := hp.nL; rw [eStack_eq] at this
  rw [ht, hp.sp, at_, toNat_at (by omega_using [this])]; omega_using [hn]

omit hp in
/-- The frame's local variable space holds a region of it. -/
theorem fr_off {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 2352) :
    ∃ off, at_ L d = at_ L 128 + BitVec.ofNat 64 off ∧ off + n ≤ 2224 :=
  sub_at L h₁ (by omega_using [h₂])

/-- The stack below the stack pointer, from `L`. -/
theorem below_sp {t : State} (ht : t.sp = s₀.sp) {n : Nat} (hn : n ≤ 96) :
    below t.sp n = ⟨at_ L (96 - n), n⟩ := by
  rw [ht, hp.sp]; exact below_off L hn

/-- `out`, at an offset, apart from a region of the stack. -/
theorem out_apart {o n : Nat} (h : o + n ≤ outLen s₀) {d k : Nat} (hd : d + k ≤ 2352) :
    Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 o, n⟩ ⟨at_ L d, k⟩ :=
  ((hp.s_o.sub_left (st_sub hd)).sub_right (Offset.sub_base _ h)).symm

end

/-! ## The loop's invariant -/

/-- The length of `T(k)`: none for `T(0)`, `D` after. -/
abbrev pl (w : HVar) (k : Nat) : Nat := if k = 0 then 0 else w.H.D

/-- `info`. -/
abbrev infoOf (s₀ : State) : List Byte := bytesAt s₀.mem (info s₀) (infoLen s₀)

/-- The pseudorandom keys the states at `key` are keyed with. -/
abbrev Keyd (w : HVar) (s₀ : State) (prk : List Byte) : Prop := Spec.Hkdf.Keyed w.ok.SH s₀.mem (key s₀) prk

/-- The bytes of `out` written after `k` blocks. -/
abbrev done (w : HVar) (s₀ : State) (k : Nat) : Nat := min (k * w.H.D) (outLen s₀)

/-- Before block `k + 1`: the registers and memory kept, `out`'s first
`done` bytes, `T(k)` in the frame, and the registers that count. -/
structure EI (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (t : State) : Prop where
  er : ER w s₀ L t
  r18 : t.gpr .r18 = out s₀ + BitVec.ofNat 64 (done w s₀ k)
  r19 : t.gpr .r19 = BitVec.ofNat 64 (outLen s₀ - done w s₀ k)
  r22 : t.gpr .r22 = BitVec.ofNat 64 (pl w k)
  r23 : t.gpr .r23 = BitVec.ofNat 64 (k + 1)
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (out s₀) (done w s₀ k) =
    (Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) k [] 1).take (done w s₀ k)
  tb : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (at_ L 408) (pl w k) = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k

/-! ## The prologue -/

theorem pro_eq : expandPro = .mflr .r0 :: .addSp .r11 0 :: .store .d .r0 .r11 oLr :: (Spill.saveCode .r11 eSaved ++
    [mov .r14 .r8, mov .r15 .r3, mov .r16 .r4, mov .r17 .r5, mov .r18 .r6, mov .r19 .r7,
      .load .d .r20 .r14 32, .load .d .r21 .r14 40, .li .r22 0, .li .r23 1]) := rfl

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L)
include hp

theorem pro_ok : WP isa (.block expandPro) s₀ (EI w s₀ L 0) := by
  rw [pro_eq]
  refine WP.of_syms (wp_mflr fun s₁ o₁ e₁ => wp_addSp fun s₂ o₂ e₂ => ?_)
  obtain b₂ : s₂.gpr .r11 = at_ L 96 := by rw [e₂, o₁.sp, hp.sp, BitVec.add_zero]
  refine wp_std (a := at_ L 128) (by rw [b₂, show oLr = 32 from rfl, at_, Offset.add_add])
    (by rw [o₂.wr, o₁.wr, hp.wr]; exact in_head _ (by decide)) fun s₃ m₃ => ?_
  obtain b₃ : s₃.gpr .r11 = at_ L 96 := by rw [m₃.gpr, b₂]
  refine Spill.save_ok (b := .r11) (by decide) (by decide) (fun q hq => ?_) ?_
  · rw [b₃, m₃.wr, o₂.wr, o₁.wr, hp.wr, at_, Offset.add_add]
    have := saved_in q hq
    exact in_at L _ (by omega_using [this]) (by omega_using [this]) (by decide)
  generalize hs₄ : ({ s₃ with mem := Spill.saveMem s₃.mem (s₃.gpr .r11) s₃.gpr eSaved } : State) = s₄ at *
  obtain K₄ : Keep [] s₃ s₄ := by subst hs₄; exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  obtain m₄ : s₄.mem = Spill.saveMem s₃.mem (at_ L 96) s₃.gpr eSaved := by subst hs₄; rw [b₃]
  obtain m₃' : s₃.mem = s₀.mem.writeW (at_ L 128) s₀.lr := by
    rw [m₃.mem, o₂.get .r0, e₁, o₂.mem, o₁.mem]
  obtain g₃ : ∀ r, r ∉ [Reg.r0, .r11] → s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [m₃.gpr, o₂.gpr r (fun h => hr (by simp at h; simp [h])), o₁.gpr r (fun h => hr (by simp at h; simp [h]))]
  obtain F₄ : Frame [⟨at_ L 136, 80⟩] s₃.mem s₄.mem := by
    rw [m₄]
    have := Spill.saveMem_frame (lo := 40) (n := 80) (l := eSaved) (by decide) (by decide) s₃.mem (at_ L 96) s₃.gpr
    rwa [at_, Offset.add_add] at this
  obtain F₄' : Frame (wrs s₀ L) s₀.mem s₄.mem := by
    have f₃ : Frame (wrs s₀ L) s₀.mem s₃.mem := by
      rw [m₃']
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
    exact f₃.trans (F₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stkR L, by simp, Offset.sub_base _ (by decide)⟩)
  -- The table's words, as on entry.
  obtain tw : ∀ o, o + 8 ≤ 48 → s₄.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 =
      s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 := fun o ho =>
    F₄'.readW (r := tabR s₀) (Offset.contains_base _ ho (by omega_using [ho])) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.s_t.symm
      · exact hp.t_o) (by decide)
  refine wp_mov fun s₅ o₅ e₅ => wp_mov fun s₆ o₆ e₆ => wp_mov fun s₇ o₇ e₇ => wp_mov fun s₈ o₈ e₈ =>
    wp_mov fun s₉ o₉ e₉ => wp_mov fun s₁₀ o₁₀ e₁₀ => ?_
  have K₁₀ : Keep [.r14, .r15, .r16, .r17, .r18, .r19] s₄ s₁₀ :=
    (o₅.keep.trans (o₆.keep.trans (o₇.keep.trans (o₈.keep.trans (o₉.keep.trans o₁₀.keep))))).mono
  obtain a14 : s₁₀.gpr .r14 = tab s₀ := by
    rw [o₁₀.get .r14, o₉.get .r14, o₈.get .r14, o₇.get .r14, o₆.get .r14, e₅, K₄.get .r8]
    exact g₃ _ (by decide)
  obtain m₁₀ : s₁₀.mem = s₄.mem := by rw [o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem]
  refine wp_ld (a := tab s₀ + BitVec.ofNat 64 32) (by rw [a14]) (tin hp (by
      rw [K₁₀.rd, K₄.rd, m₃.rd, o₂.rd, o₁.rd]) (by decide)) fun s₁₁ o₁₁ e₁₁ => ?_
  refine wp_ld (a := tab s₀ + BitVec.ofNat 64 40) (by rw [o₁₁.get .r14, a14]) (tin hp (by
      rw [o₁₁.rd, K₁₀.rd, K₄.rd, m₃.rd, o₂.rd, o₁.rd]) (by decide)) fun s₁₂ o₁₂ e₁₂ => ?_
  refine wp_li (by decide) fun s₁₃ o₁₃ e₁₃ => wp_li (by decide) fun s₁₄ o₁₄ e₁₄ => WP.block_nil fun sy => ?_
  have K : Keep [.r0, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23] s₀ s₁₄ :=
    (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (K₄.trans (K₁₀.trans (o₁₁.keep.trans (o₁₂.keep.trans
      (o₁₃.keep.trans o₁₄.keep)))))))).mono
  obtain m₁₄ : s₁₄.mem = s₄.mem := by rw [o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem, m₁₀]
  have er : ER w s₀ L s₁₄ := by
    refine ⟨K.rd, K.wr, K.sp, sy, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hk => K.gpr r ((by decide : ∀ r ∈ preserved,
        r ∉ eregs → r ∉ ([.r0, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23] : List Reg)) r hr hk),
      ?_, ?_, by rw [m₁₄]; exact F₄'⟩
    · rw [o₁₄.get .r14, o₁₃.get .r14, o₁₂.get .r14, o₁₁.get .r14, a14]
    · rw [o₁₄.get .r15, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15, o₉.get .r15, o₈.get .r15,
        o₇.get .r15, e₆, o₅.get .r3, K₄.get .r3]; exact g₃ _ (by decide)
    · rw [o₁₄.get .r16, o₁₃.get .r16, o₁₂.get .r16, o₁₁.get .r16, o₁₀.get .r16, o₉.get .r16, o₈.get .r16,
        e₇, o₆.get .r4, o₅.get .r4, K₄.get .r4]; exact g₃ _ (by decide)
    · rw [o₁₄.get .r17, o₁₃.get .r17, o₁₂.get .r17, o₁₁.get .r17, o₁₀.get .r17, o₉.get .r17, e₈,
        o₇.get .r5, o₆.get .r5, o₅.get .r5, K₄.get .r5]; exact g₃ _ (by decide)
    · rw [o₁₄.get .r20, o₁₃.get .r20, o₁₂.get .r20, e₁₁, m₁₀, tw 32 (by decide)]; exact hp.tD
    · rw [o₁₄.get .r21, o₁₃.get .r21, e₁₂, o₁₁.mem, m₁₀, tw 40 (by decide)]; exact hp.tB
    · intro q hq
      rw [m₁₄, m₄, Spill.saveMem_saved saved_fits s₃.mem (at_ L 96) s₃.gpr q hq]
      exact g₃ _ (by revert hq; revert q; decide)
    · rw [m₁₄, F₄.readW (r := ⟨at_ L 128, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by decide)) (by decide) (by have := hp.nL; omega_using [this]))
        (by decide), m₃', Mem.readW_writeW_self64]
  refine ⟨er, ?_, ?_, ?_, ?_, fun prk _ => ?_, fun prk _ => ?_⟩
  · rw [o₁₄.get .r18, o₁₃.get .r18, o₁₂.get .r18, o₁₁.get .r18, o₁₀.get .r18, e₉, o₈.get .r6, o₇.get .r6,
      o₆.get .r6, o₅.get .r6, K₄.get .r6, g₃ _ (by decide)]
    simp only [done, Nat.zero_mul, Nat.zero_min, BitVec.add_zero]
  · rw [o₁₄.get .r19, o₁₃.get .r19, o₁₂.get .r19, o₁₁.get .r19, e₁₀, o₉.get .r7, o₈.get .r7, o₇.get .r7,
      o₆.get .r7, o₅.get .r7, K₄.get .r7, g₃ _ (by decide)]
    simp only [done, Nat.zero_mul, Nat.zero_min, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [o₁₄.get .r22, e₁₃]; rfl
  · rw [e₁₄]
  · simp [done, bytesAt]
  · simp [pl, bytesAt, Proof.Hkdf.tBlock]

end

/-! ## A block -/

/-- `copyLoop` copies `n` bytes from `q` to `p`: what changes, and the bytes. -/
theorem copy_run {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = q) (h5 : s.gpr .r5 = p) (h6 : s.gpr .r6 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) (hd : Region.Disjoint ⟨q, n⟩ ⟨p, n⟩) :
    WP isa copyLoop s fun t => Keep [.r7, .r4, .r5, .r6] s t ∧ Frame [⟨p, n⟩] s.mem t.mem ∧
      ∀ i < n, t.mem (p + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
  have hl : (Spec.Rsa.bytesAt s.mem q n).length = n := by simp [Spec.Rsa.bytesAt]
  refine WP.mono (Proof.RsaOaep.PPC64LE.copy_ok hn hn' h4 h5 h6 hr hw fun j hj i hi e => hd _
      (Offset.contains_base q (d := j) (n := 1) (by omega_using [hj]) (by omega_using [hj, hn']))
      (by rw [e]; exact Offset.contains_base p (d := i) (n := 1) (by omega_using [hi]) (by omega_using [hi, hn'])))
    fun t ⟨K, hm⟩ => ⟨K, ?_, fun i hi => ?_⟩
  · rw [hm]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  · rw [hm, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [hl]; exact hi) (by rw [hl]; exact hn')]
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]

/-- `T(k)` has `pl k` bytes. -/
theorem tBlock_len (w : HVar) (prk info : List Byte) (k : Nat) :
    (Proof.Hkdf.tBlock w.ok.SH.H prk info k).length = pl w k := by
  cases k with
  | zero => rfl
  | succ k => exact Proof.Hkdf.tBlock_length _ _ _ w.ok.hashLen k

/-- During block `k + 1`: the registers and memory kept, `out`'s first `k D`
bytes, and the registers that count. -/
structure BR (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (t : State) : Prop where
  er : ER w s₀ L t
  r18 : t.gpr .r18 = out s₀ + BitVec.ofNat 64 (k * w.H.D)
  r19 : t.gpr .r19 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D)
  r22 : t.gpr .r22 = BitVec.ofNat 64 (pl w k)
  r23 : t.gpr .r23 = BitVec.ofNat 64 (k + 1)
  lt : k * w.H.D < outLen s₀
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (out s₀) (k * w.H.D) =
    Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) k [] 1

/-- `K₀` of a pseudorandom key. -/
abbrev k0 (w : HVar) (prk : List Byte) : List Byte := blockKey w.ok.SH.H prk

/-- The working state represents `K₀ ⊕ ipad`, then `m`, for each
pseudorandom key the states are keyed with. -/
abbrev WS (w : HVar) (s₀ : State) (L : Addr) (t : State) (m : List Byte → List Byte) : Prop :=
  ∀ prk, Keyd w s₀ prk → w.ok.SH.Repr t.mem (at_ L 216) (xorPad (k0 w prk) ipad ++ m prk)

/-- `T(k)` in the frame, for each pseudorandom key. -/
abbrev TB (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (at_ L 408) (pl w k) = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k

/-- The registers that count. -/
abbrev cregs : List Reg := [.r18, .r19, .r22, .r23]

theorem BR.keep {w : HVar} {s₀ : State} {L : Addr} {k : Nat} {t t' : State} (h : BR w s₀ L k t) (he : ER w s₀ L t')
    (hg : ∀ r ∈ cregs, t'.gpr r = t.gpr r)
    (hb : bytesAt t'.mem (out s₀) (k * w.H.D) = bytesAt t.mem (out s₀) (k * w.H.D)) : BR w s₀ L k t' :=
  ⟨he, (hg _ (by decide)).trans h.r18, (hg _ (by decide)).trans h.r19, (hg _ (by decide)).trans h.r22,
    (hg _ (by decide)).trans h.r23, h.lt, fun prk hK => hb.trans (h.ob prk hK)⟩

/-- The bytes of a region apart from `rs` are kept. -/
theorem keep_fr {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    (hR : R.len ≤ 2 ^ 64) : bytesAt m' R.base R.len = bytesAt m R.base R.len :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes hd hR hi

/-- The sizes the block needs. -/
structure Sz (w : HVar) : Prop where
  hS : w.H.S ≤ 192
  hD : w.H.D ≤ 64
  hD0 : 0 < w.H.D
  hB : w.H.B ≤ 128
  hW : w.H.W ≤ 1872
  hA : w.I.scratch * 8 ≤ 1872
  hpl : ∀ k, pl w k ≤ w.H.D

theorem sz {w : HVar} (hw : HOk w) : Sz w :=
  ⟨hw.hS, w.ok.hD64, w.ok.hD0, by rcases w.ok.dims.B with h | h <;> omega_using [h], hw.hW, hw.hA,
    fun k => by unfold pl; split <;> omega_using []⟩

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

/-- `info` fits HMAC's count with a block of key, `T(i - 1)` and the counter. -/
theorem info_lt : w.H.B + w.H.D + infoLen s₀ + 1 < 2 ^ 64 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hp.s_i.symm hp.ni (by have := hp.nL; exact this)
  have z := sz hw
  have h' : infoLen s₀ + eStack ≤ 2 ^ 64 := h
  rw [eStack_eq] at h'
  omega_using [h', z.hB, z.hD]

omit hp hw in
/-- The working state, as the inner state at `key`, for each pseudorandom key. -/
theorem ws_of {t : State}
    (hc : ∀ i < 64, t.mem (at_ L 216 + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 i)) :
    WS w s₀ L t fun _ => [] := by
  intro prk hK
  rw [List.append_nil]
  refine w.ok.reloc _ _ _ _ _ ?_ (fun i hi => hc i (by have := w.ok.dims.N; omega_using [this, hi])) hK.1
  rw [xorPad_length, blockKey_length, Nat.mod_self]

/-- The copy of the inner state at `key`'s hash value to the working state. -/
theorem copy_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t) :
    WP isa (.seq (.block copyArgs) copyLoop) t fun u =>
      BR w s₀ L k u ∧ TB w s₀ L k u ∧ WS w s₀ L u (fun _ => []) ∧ u.syms = s₀.syms := by
  have z := sz hw
  have k₀ := h.er
  unfold copyArgs
  refine WP.seq (WP.of_syms (wp_mov fun t₁ o₁ e₁ => wp_addSp fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    WP.block_nil fun sy => ?_))
  have K₃ : Keep [.r4, .r5, .r6] t t₃ := (o₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  have m₃ : t₃.mem = t.mem := by rw [o₃.mem, o₂.mem, o₁.mem]
  have k₃ : ER w s₀ L t₃ := k₀.same K₃.rd K₃.wr K₃.sp sy (keep_pres K₃) m₃
  have a4 : t₃.gpr .r4 = key s₀ := by rw [o₃.get .r4, o₂.get .r4, e₁, k₀.r15]
  have a5 : t₃.gpr .r5 = at_ L 216 := by
    rw [o₃.get .r5, e₂, o₁.sp, k₀.sp, hp.sp, at_, show eWs = 120 from rfl, Offset.add_add]
  have a6 : t₃.gpr .r6 = BitVec.ofNat 64 64 := e₃
  refine WP.of_syms (WP.mono (copy_run (n := 64) (by decide) (by decide) a4 a5 a6 (fun j hj => ?_) (fun i hi => ?_)
    ((((hp.s_k.sub_left (st_sub (d := 216) (n := 64) (by decide))).symm).sub_left
      (Region.sub_prefix (by decide))))) fun u ⟨K, F, hc⟩ sy' => ?_)
  · rw [k₃.rd, hp.rd]
    exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  · rw [at_, Offset.add_add]; exact in_frw hp k₃.wr (by omega_using []) (by omega_using [hi])
  have ku : ER w s₀ L u := k₃.keep hp K.rd K.wr K.sp sy' (keep_pres K) F (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact wk_at hp (.inl (by decide)) (by decide))
  have dfr : ∀ {R : Region}, Region.Disjoint R ⟨at_ L 216, 64⟩ → R.len ≤ 2 ^ 64 →
      bytesAt u.mem R.base R.len = bytesAt t₃.mem R.base R.len := fun hd hl =>
    keep_fr F (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  refine ⟨h.keep ku (fun r hr => by
      rw [K.gpr r (by revert hr; revert r; decide), K₃.gpr r (by revert hr; revert r; decide)]) ?_,
    fun prk hK => ?_, ws_of fun i hi => ?_, sy'.trans (sy.trans k₀.sy)⟩
  · have hd := out_apart hp (o := 0) (n := k * w.H.D) (by omega_using [hk]) (d := 216) (k := 64) (by decide)
    rw [BitVec.add_zero] at hd
    exact (dfr hd (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])).trans (by rw [m₃])
  · have hp1 := z.hpl k
    have hD := z.hD
    have hd : Region.Disjoint ⟨at_ L 408, pl w k⟩ ⟨at_ L 216, 64⟩ :=
      st_dis hp (.inr (by decide)) (by omega_using [hp1, hD]) (by decide)
    exact (dfr hd (by show pl w k ≤ 2 ^ 64; omega_using [hp1, hD])).trans
      (by rw [m₃]; exact ht prk hK)
  · rw [hc i hi, m₃]
    have := ER.keyB hp k₀ (o := 0) (n := 64) (by decide) i hi
    rwa [BitVec.add_zero] at this

end

/-! ## The calls of a block -/

/-- What `update`'s arguments are, for `len` bytes at `dat`. -/
structure UA (w : HVar) (L : Addr) (dat : Addr) (len : Nat) (t : State) : Prop where
  r3 : t.gpr .r3 = at_ L 216
  r5 : t.gpr .r5 = dat
  r6 : (t.gpr .r6).toNat = len
  r7 : t.gpr .r7 = at_ L 480
  d_w : Region.Disjoint ⟨dat, len⟩ ⟨at_ L 216, w.H.S⟩
  d_k : Region.Disjoint ⟨dat, len⟩ ⟨at_ L 480, w.H.W⟩
  d_b : Region.Disjoint ⟨at_ L 48, 48⟩ ⟨dat, len⟩
  cov : Covers [⟨dat, len⟩] (t.rd ++ t.wr)

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

theorem upd_args {k : Nat} {t t' : State} (h : BR w s₀ L k t) {dat : Addr} {len : Nat} (ha : UA w L dat len t)
    (o : Only [.r12] t t') : UpdArgs w t' (at_ L 216) dat (at_ L 480) len := by
  have z := sz hw
  have bS := below_sp hp (o.sp.trans h.er.sp) (n := 48) (by decide)
  refine ⟨by rw [o.get .r3, ha.r3], by rw [o.get .r5, ha.r5], by rw [o.get .r6, ha.r6], by rw [o.get .r7, ha.r7],
    st_dis hp (.inl (by omega_using [z.hS])) (by omega_using [z.hS]) (by omega_using [z.hW]), ha.d_w, ha.d_k,
    sp_ge hp (o.sp.trans h.er.sp) (by decide), ?_, by rw [bS]; exact ha.d_b, ?_, ?_, ?_⟩
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [z.hS])
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [z.hW])
  · refine Covers.append_left (by rw [o.rd, o.wr]; exact ha.cov) (Covers.of_sub fun r hr => ?_)
    rw [o.rd, o.wr, h.er.rd, h.er.wr, hp.rd, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hS])⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hW])⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [o.wr, h.er.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hS])⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hW])⟩

/-- `update` with `len` bytes at `dat`, once the load of its address wrote
`r12`: the working state absorbs them, and `BR` and `T(k)` are kept. -/
theorem upd_step {k : Nat} {t t' : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t) {m : List Byte → List Byte}
    (hws : WS w s₀ L t m) {dat : Addr} {len : Nat} (ha : UA w L dat len t)
    (hc : t.gpr .r4 = BitVec.ofNat 64 (w.H.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) (o : Only [.r12] t t') (sy : t'.syms = t.syms) :
    WP isa (.call w.H.updN w.H.updC) t' fun u' => BR w s₀ L k u' ∧ TB w s₀ L k u' ∧
      WS w s₀ L u' (fun prk => m prk ++ bytesAt t.mem dat len) ∧ u'.syms = s₀.syms := by
  have z := sz hw
  have bS := below_sp hp (o.sp.trans h.er.sp) (n := 48) (by decide)
  refine upd_call (upd_args hp hw h ha o) fun s' a hu => ?_
  have k' : ER w s₀ L s' := (h.er.only o sy).keep hp a.rd a.wr a.sp a.sy a.cs a.frame (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact wk_at hp (.inl (by decide)) (by omega_using [z.hS])
    · exact wk_at hp (.inl (by decide)) (by omega_using [z.hW])
    · rw [bS]; exact wk_at hp (.inr (by decide)) (by decide))
  have hm : t'.mem = t.mem := o.mem
  have apart : ∀ {R : Region}, (∀ r ∈ ([⟨at_ L 216, w.H.S⟩, ⟨at_ L 480, w.H.W⟩] ++ [below t'.sp 48] : List Region),
      R.Disjoint r) → R.len ≤ 2 ^ 64 → bytesAt s'.mem R.base R.len = bytesAt t.mem R.base R.len := fun h₁ hl =>
    (keep_fr a.frame h₁ hl).trans (by rw [hm])
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  refine ⟨h.keep k' (fun r hr => by
      rw [a.cs r (by revert hr; revert r; decide), o.gpr r (by revert hr; revert r; decide)]) ?_,
    fun prk hK => ?_, fun prk hK => ?_, a.sy.trans (sy.trans h.er.sy)⟩
  · have := apart (R := ⟨out s₀ + BitVec.ofNat 64 0, k * w.H.D⟩) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact out_apart hp (by omega_using [hk]) (by omega_using [z.hS])
      · exact out_apart hp (by omega_using [hk]) (by omega_using [z.hW])
      · rw [bS]; exact out_apart hp (by omega_using [hk]) (by decide))
      (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
    simpa only [BitVec.add_zero] using this
  · have hp' := z.hpl k
    have := apart (R := ⟨at_ L 408, pl w k⟩) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st_dis hp (.inr (by omega_using [z.hS])) (by omega_using [hp', z.hD]) (by omega_using [z.hS])
      · exact st_dis hp (.inl (by omega_using [hp', z.hD])) (by omega_using [hp', z.hD]) (by omega_using [z.hW])
      · rw [bS]; exact st_dis hp (.inr (by decide)) (by omega_using [hp', z.hD]) (by decide))
      (by show pl w k ≤ 2 ^ 64; omega_using [hp', z.hD])
    exact this.trans (ht prk hK)
  · have := hu _ (by rw [hm]; exact hws prk hK) (by
      rw [o.get .r4, hc, List.length_append, xorPad_length, blockKey_length, hml prk])
    rwa [hm, List.append_assoc] at this

omit hw in
/-- The loads of the table's functions' addresses. -/
theorem tload1 {t : State} (k : ER w s₀ L t) :
    WP isa (.block [.load .d .r12 .r14 (8 * 1)]) t fun u =>
      Only [.r12] t u ∧ u.gpr .r12 = s₀.syms w.H.updN ∧ u.syms = t.syms :=
  tload_ok (by decide) (by decide) k.r14 (tin hp k.rd (by decide)) (by rw [k.tabW hp (by decide)]; exact hp.tmem.2.1)

omit hw in
theorem tload2 {t : State} (k : ER w s₀ L t) :
    WP isa (.block [.load .d .r12 .r14 (8 * 2)]) t fun u =>
      Only [.r12] t u ∧ u.gpr .r12 = s₀.syms w.finN ∧ u.syms = t.syms :=
  tload_ok (by decide) (by decide) k.r14 (tin hp k.rd (by decide)) (by rw [k.tabW hp (by decide)]; exact hp.tmem.2.2)

/-- `update` with `len` bytes at `dat`, through the table. -/
theorem upd_stage {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t) {m : List Byte → List Byte}
    (hws : WS w s₀ L t m) {dat : Addr} {len : Nat} (ha : UA w L dat len t)
    (hc : t.gpr .r4 = BitVec.ofNat 64 (w.H.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) :
    WP isa (tcall .r14 1 f.upd) t fun u' => BR w s₀ L k u' ∧ TB w s₀ L k u' ∧
      WS w s₀ L u' (fun prk => m prk ++ bytesAt t.mem dat len) ∧ u'.syms = s₀.syms := by
  unfold tcall
  refine WP.seq (WP.mono (tload1 hp h.er) fun t' ⟨o, e, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (upd_step hp hw h ht hws ha hc hml o sy)
  show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, sy, h.er.sy]; exact hp.tok.u

/-- A part of the frame after the working state, for `update`'s data. -/
theorem fr_ua {t : State} (k : ER w s₀ L t) {d n : Nat} (h₁ : 408 ≤ d) (h₂ : d + n ≤ 480) :
    Region.Disjoint ⟨at_ L d, n⟩ ⟨at_ L 216, w.H.S⟩ ∧ Region.Disjoint ⟨at_ L d, n⟩ ⟨at_ L 480, w.H.W⟩ ∧
      Region.Disjoint ⟨at_ L 48, 48⟩ ⟨at_ L d, n⟩ ∧ Covers [⟨at_ L d, n⟩] (t.rd ++ t.wr) := by
  have z := sz hw
  exact ⟨st_dis hp (.inr (by omega_using [z.hS, h₁])) (by omega_using [h₂]) (by omega_using [z.hS]),
    st_dis hp (.inl h₂) (by omega_using [h₂]) (by omega_using [z.hW]),
    st_dis hp (.inl (by omega_using [h₁])) (by decide) (by omega_using [h₂]),
    Covers.one (in_fr hp k.wr (by omega_using [h₁]) (by omega_using [h₂]))⟩

end

/-- `update`'s arguments for `len` bytes at `dat`, the working state
holding `B + n` bytes (`m`). -/
structure AT (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (dat : Addr) (len n : Nat) (m : List Byte → List Byte)
    (t : State) : Prop where
  br : BR w s₀ L k t
  tb : TB w s₀ L k t
  ws : WS w s₀ L t m
  ua : UA w L dat len t
  r4 : t.gpr .r4 = BitVec.ofNat 64 (w.H.B + n)
  sy : t.syms = s₀.syms

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

/-- `update`'s arguments for `T(k)`. -/
theorem argsT_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t) (hws : WS w s₀ L t fun _ => []) :
    WP isa (.block updT) t (AT w s₀ L k (at_ L 408) (pl w k) 0 fun _ => []) := by
  have z := sz hw
  unfold updT
  refine WP.of_syms (wp_addSp fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_addSp fun t₃ o₃ e₃ =>
    wp_mov fun t₄ o₄ e₄ => wp_addSp fun t₅ o₅ e₅ => WP.block_nil fun sy => ?_)
  have K : Keep [.r3, .r4, .r5, .r6, .r7] t t₅ :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
  have m₅ : t₅.mem = t.mem := by rw [o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have k₅ : ER w s₀ L t₅ := h.er.same K.rd K.wr K.sp sy (keep_pres K) m₅
  have h₅ : BR w s₀ L k t₅ := h.keep k₅ (fun r hr => K.gpr r (by revert hr; revert r; decide)) (by rw [m₅])
  have hpl := z.hpl k
  obtain ⟨dw, dk, db, cov⟩ := fr_ua hp hw k₅ (d := 408) (n := pl w k) (by decide) (by omega_using [hpl, z.hD])
  have sp₄ : t₄.sp = s₀.sp := by rw [o₄.sp, o₃.sp, o₂.sp, o₁.sp, h.er.sp]
  have ua : UA w L (at_ L 408) (pl w k) t₅ := by
    refine ⟨?_, ?_, ?_, ?_, dw, dk, db, cov⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, h.er.sp, hp.sp, at_, show eWs = 120 from rfl,
        Offset.add_add]
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.sp, o₁.sp, h.er.sp, hp.sp, at_, show eT = 312 from rfl, Offset.add_add]
    · rw [o₅.get .r6, e₄, o₃.get .r22, o₂.get .r22, o₁.get .r22, h.r22, BitVec.toNat_ofNat]
      omega_using [hpl, z.hD]
    · rw [e₅, sp₄, hp.sp, at_, show eW = 384 from rfl, Offset.add_add]
  exact ⟨h₅, fun prk hK => by rw [m₅]; exact ht prk hK, fun prk hK => by rw [m₅]; exact hws prk hK, ua,
    by rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂, o₁.get .r21, h.er.r21, Nat.add_zero], sy.trans h.er.sy⟩

/-- What `update` with `T(k)` gives. -/
abbrev PT (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (u : State) : Prop := BR w s₀ L k u ∧ TB w s₀ L k u ∧
  WS w s₀ L u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) ∧ u.syms = s₀.syms

theorem callT_ok {k : Nat} {t : State} (a : AT w s₀ L k (at_ L 408) (pl w k) 0 (fun _ => []) t) :
    WP isa (tcall .r14 1 f.upd) t (PT w s₀ L k) :=
  WP.mono (upd_stage hp hw a.br a.tb a.ws a.ua a.r4 (fun _ => rfl))
    fun _ ⟨hv, htv, hwv, syv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [List.nil_append, a.tb prk hK] at this, syv⟩

/-- `update` with `T(k)`. -/
theorem stageT_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t) (hws : WS w s₀ L t fun _ => []) :
    WP isa (.seq (.block updT) (tcall .r14 1 f.upd)) t (PT w s₀ L k) :=
  WP.seq (WP.mono (argsT_ok hp hw h ht hws) fun _ a => callT_ok hp hw a)

/-- `update`'s arguments for `info`. -/
theorem argsI_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) :
    WP isa (.block updI) t
      (AT w s₀ L k (info s₀) (infoLen s₀) (pl w k) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) := by
  have z := sz hw
  unfold updI
  refine WP.of_syms (wp_addSp fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ =>
    wp_mov fun t₄ o₄ e₄ => wp_addSp fun t₅ o₅ e₅ => WP.block_nil fun sy => ?_)
  have K : Keep [.r3, .r4, .r5, .r6, .r7] t t₅ :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
  have m₅ : t₅.mem = t.mem := by rw [o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have k₅ : ER w s₀ L t₅ := h.er.same K.rd K.wr K.sp sy (keep_pres K) m₅
  have h₅ : BR w s₀ L k t₅ := h.keep k₅ (fun r hr => K.gpr r (by revert hr; revert r; decide)) (by rw [m₅])
  have hpl := z.hpl k
  have sp₄ : t₄.sp = s₀.sp := by rw [o₄.sp, o₃.sp, o₂.sp, o₁.sp, h.er.sp]
  have ua : UA w L (info s₀) (infoLen s₀) t₅ := by
    refine ⟨?_, ?_, ?_, ?_, (hp.s_i.sub_left (st_sub (by omega_using [z.hS]))).symm,
      (hp.s_i.sub_left (st_sub (by omega_using [z.hW]))).symm, hp.s_i.sub_left (st_sub (by decide)),
      Covers.one ⟨infoR s₀, List.mem_append_left _ (by rw [k₅.rd, hp.rd]; simp), Region.contains_self _ _⟩⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, h.er.sp, hp.sp, at_, show eWs = 120 from rfl,
        Offset.add_add]
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r16, o₁.get .r16, h.er.r16]
    · rw [o₅.get .r6, e₄, o₃.get .r17, o₂.get .r17, o₁.get .r17, h.er.r17]
    · rw [e₅, sp₄, hp.sp, at_, show eW = 384 from rfl, Offset.add_add]
  refine ⟨h₅, fun prk hK => by rw [m₅]; exact ht prk hK, fun prk hK => by rw [m₅]; exact hws prk hK, ua, ?_,
    sy.trans h.er.sy⟩
  rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂, o₁.get .r21, o₁.get .r22, h.er.r21, h.r22, BitVec.ofNat_add_ofNat]

/-- What `update` with `info` gives. -/
abbrev PI (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (u : State) : Prop := BR w s₀ L k u ∧ TB w s₀ L k u ∧
  WS w s₀ L u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀) ∧ u.syms = s₀.syms

theorem callI_ok {k : Nat} {t : State}
    (a : AT w s₀ L k (info s₀) (infoLen s₀) (pl w k) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) t) :
    WP isa (tcall .r14 1 f.upd) t (PI w s₀ L k) :=
  WP.mono (upd_stage hp hw a.br a.tb a.ws a.ua (by rw [a.r4, tBlock_len]) (fun prk => by rw [tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv, syv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.br.er.infoB hp] at this, syv⟩

/-- `update` with `info`. -/
theorem stageI_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k) :
    WP isa (.seq (.block updI) (tcall .r14 1 f.upd)) t (PI w s₀ L k) :=
  WP.seq (WP.mono (argsI_ok hp hw h ht hws) fun _ a => callI_ok hp hw a)

end

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

/-- The counter's byte stored in the frame; `update`'s arguments for it. -/
theorem argsC_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.block updC) t fun u =>
      AT w s₀ L k (at_ L 472) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++
        infoOf s₀) u ∧ bytesAt u.mem (at_ L 472) 1 = [BitVec.ofNat 8 (k + 1)] := by
  have z := sz hw
  have hpl := z.hpl k
  have hil := info_lt hp hw
  unfold updC
  refine WP.of_syms (wp_addSp fun t₁ o₁ e₁ => ?_)
  have b₁ : t₁.gpr .r11 = at_ L 96 := by rw [e₁, h.er.sp, hp.sp, BitVec.add_zero]
  refine wp_stb (a := at_ L 472) (by rw [b₁, show eC = 376 from rfl, at_, Offset.add_add])
    (in_frw hp (by rw [o₁.wr, h.er.wr]) (by decide) (by decide)) fun t₂ m₂ => ?_
  refine wp_addSp fun t₃ o₃ e₃ => wp_add fun t₄ o₄ e₄ => wp_add fun t₅ o₅ e₅ => wp_addSp fun t₆ o₆ e₆ =>
    wp_li (by decide) fun t₇ o₇ e₇ => wp_addSp fun t₈ o₈ e₈ => WP.block_nil fun sy => ?_
  have K : Keep [.r11, .r3, .r4, .r4, .r5, .r6, .r7] t t₈ :=
    (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans
      (o₇.keep.trans o₈.keep))))))).mono
  have mm : t₈.mem = t.mem.writeW (at_ L 472) ((t.gpr .r23).setWidth 8) := by
    rw [o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, m₂.mem, o₁.get .r23, o₁.mem]
  have F : Frame [⟨at_ L 472, 1⟩] t.mem t₈.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₈ : ER w s₀ L t₈ := h.er.keep hp K.rd K.wr K.sp sy (keep_pres K) F (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact wk_at hp (.inl (by decide)) (by decide))
  have apart : ∀ {R : Region}, R.Disjoint ⟨at_ L 472, 1⟩ → R.len ≤ 2 ^ 64 →
      bytesAt t₈.mem R.base R.len = bytesAt t.mem R.base R.len := fun hd hl =>
    keep_fr F (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  have h₈ : BR w s₀ L k t₈ := h.keep k₈ (fun r hr => K.gpr r (by revert hr; revert r; decide)) (by
    have d := out_apart hp (o := 0) (n := k * w.H.D) (by omega_using [hk]) (d := 472) (k := 1) (by decide)
    rw [BitVec.add_zero] at d
    exact apart d (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol]))
  have tb₈ : TB w s₀ L k t₈ := fun prk hK => by
    have d : Region.Disjoint ⟨at_ L 408, pl w k⟩ ⟨at_ L 472, 1⟩ :=
      st_dis hp (.inl (by omega_using [hpl, z.hD])) (by omega_using [hpl, z.hD]) (by decide)
    exact (apart d (by show pl w k ≤ 2 ^ 64; omega_using [hpl, z.hD])).trans (ht prk hK)
  have ws₈ : WS w s₀ L t₈ fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ := fun prk hK =>
    w.ok.congr _ _ _ _ (fun i hi => F.bytes (R := ⟨at_ L 216, w.H.S⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact st_dis hp (.inl (by omega_using [z.hS])) (by omega_using [z.hS]) (by decide))
      (by show w.H.S ≤ 2 ^ 64; omega_using [z.hS]) hi) (hws prk hK)
  obtain ⟨dw, dk, db, cov⟩ := fr_ua hp hw k₈ (d := 472) (n := 1) (by decide) (by decide)
  have sp₂ : t₂.sp = s₀.sp := by rw [m₂.sp, o₁.sp, h.er.sp]
  have ua : UA w L (at_ L 472) 1 t₈ := by
    refine ⟨?_, ?_, ?_, ?_, dw, dk, db, cov⟩
    · rw [o₈.get .r3, o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, e₃, sp₂, hp.sp, at_,
        show eWs = 120 from rfl, Offset.add_add]
    · rw [o₈.get .r5, o₇.get .r5, e₆, o₅.sp, o₄.sp, o₃.sp, sp₂, hp.sp, at_, show eC = 376 from rfl,
        Offset.add_add]
    · rw [o₈.get .r6, e₇]; rfl
    · rw [e₈, o₇.sp, o₆.sp, o₅.sp, o₄.sp, o₃.sp, sp₂, hp.sp, at_, show eW = 384 from rfl, Offset.add_add]
  have hbyte : bytesAt t₈.mem (at_ L 472) 1 = [BitVec.ofNat 8 (k + 1)] := by
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
    rw [mm, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, h.r23, Proof.RsaOaep.PPC64LE.trunc8]
  refine ⟨⟨h₈, tb₈, ws₈, ua, ?_, sy.trans h.er.sy⟩, hbyte⟩
  rw [o₈.get .r4, o₇.get .r4, o₆.get .r4, e₅, e₄, o₃.get .r21, o₃.get .r22, o₄.get .r17, o₃.get .r17,
    m₂.gpr, o₁.get .r21, o₁.get .r22, o₁.get .r17, h.er.r21, h.r22, h.er.r17]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hB : w.H.B < 2 ^ 64 := by omega_using [z.hB]
  rw [Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt (by omega_using [hpl, z.hD] : pl w k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega_using [z.hB, hpl, z.hD] : w.H.B + pl w k < 2 ^ 64)]
  show (w.H.B + pl w k + infoLen s₀) % 2 ^ 64 = (w.H.B + (pl w k + infoLen s₀)) % 2 ^ 64
  rw [Nat.add_assoc]

/-- `update`'s arguments for the counter. -/
abbrev AC (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (u : State) : Prop :=
  AT w s₀ L k (at_ L 472) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++
    infoOf s₀) u ∧ bytesAt u.mem (at_ L 472) 1 = [BitVec.ofNat 8 (k + 1)]

/-- What `update` with the counter gives. -/
abbrev PC (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (u : State) : Prop := BR w s₀ L k u ∧ TB w s₀ L k u ∧
  WS w s₀ L u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++
    [BitVec.ofNat 8 (k + 1)]) ∧ u.syms = s₀.syms

theorem callC_ok {k : Nat} {t : State} (a : AC w s₀ L k t) : WP isa (tcall .r14 1 f.upd) t (PC w s₀ L k) :=
  WP.mono (upd_stage hp hw a.1.br a.1.tb a.1.ws a.1.ua
      (by rw [a.1.r4, List.length_append, tBlock_len, bytesAt_length])
      (fun prk => by rw [List.length_append, List.length_append, tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv, syv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.2] at this, syv⟩

/-- `update` with the counter's byte, stored in the frame first. -/
theorem stageC_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (ht : TB w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.seq (.block updC) (tcall .r14 1 f.upd)) t (PC w s₀ L k) :=
  WP.seq (WP.mono (argsC_ok hp hw h ht hws) fun _ a => callC_ok hp hw a)

end

/-- `finalize`'s arguments. -/
structure FA (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (t : State) : Prop where
  r3 : t.gpr .r3 = at_ L 216
  r4 : t.gpr .r4 = key s₀ + BitVec.ofNat 64 192
  r5 : t.gpr .r5 = BitVec.ofNat 64 (w.H.B + (pl w k + infoLen s₀ + 1))
  r6 : t.gpr .r6 = at_ L 408
  r7 : t.gpr .r7 = at_ L 480

/-- The outer state's region, within `key`. -/
abbrev ouR (w : HVar) (s₀ : State) : Region := ⟨key s₀ + BitVec.ofNat 64 192, w.H.S⟩

/-- `T(k + 1)` in the frame, for each pseudorandom key. -/
abbrev TF (w : HVar) (s₀ : State) (L : Addr) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (at_ L 408) w.H.D = Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) (k + 1)

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

omit hp in
theorem ou_sub : Region.Sub (ouR w s₀) (keyR s₀) :=
  Offset.sub_base _ (by have := (sz hw).hS; omega_using [this])

theorem fin_args {k : Nat} {t t' : State} (h : BR w s₀ L k t) (ha : FA w s₀ L k t) (o : Only [.r12] t t') :
    FinArgs w t' (at_ L 216) (key s₀ + BitVec.ofNat 64 192) (at_ L 408) (at_ L 480) := by
  have z := sz hw
  have bS := below_sp hp (o.sp.trans h.er.sp) (n := 96) (by decide)
  have ouS := ou_sub hw (s₀ := s₀)
  refine ⟨by rw [o.get .r3, ha.r3], by rw [o.get .r4, ha.r4], by rw [o.get .r6, ha.r6], by rw [o.get .r7, ha.r7],
    (hp.s_k.sub_left (st_sub (by omega_using [z.hS]))).sub_right ouS,
    st_dis hp (.inl (by omega_using [z.hS])) (by omega_using [z.hS]) (by omega_using [z.hD]),
    st_dis hp (.inl (by omega_using [z.hS])) (by omega_using [z.hS]) (by omega_using [z.hA]),
    ((hp.s_k.sub_left (st_sub (by omega_using [z.hD]))).sub_right ouS).symm,
    ((hp.s_k.sub_left (st_sub (by omega_using [z.hA]))).sub_right ouS).symm,
    st_dis hp (.inl (by omega_using [z.hD])) (by omega_using [z.hD]) (by omega_using [z.hA]),
    sp_ge hp (o.sp.trans h.er.sp) (by decide), ?_, ?_, ?_, ?_, st_nw hp (by omega_using [z.hS]), ?_,
    st_nw hp (by omega_using [z.hD]), st_nw hp (by omega_using [z.hA]), ?_, ?_⟩
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [z.hS])
  · rw [bS]; exact (hp.s_k.sub_left (st_sub (by decide))).sub_right ouS
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [z.hD])
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [z.hA])
  · have nk := hp.nk
    rw [toNat_at (by omega_using [nk])]; omega_using [nk, z.hS]
  · rw [o.rd, o.wr, h.er.rd, h.er.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨keyR s₀, by simp, 192, rfl, by dsimp only; omega_using [z.hS]⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hS])⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hD])⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hA])⟩
  · rw [o.wr, h.er.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hS])⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hD])⟩
    · exact ⟨⟨at_ L 128, 2224⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [z.hA])⟩

/-- `finalize`, once the load of its address wrote `r12`: `T(k + 1)`. -/
theorem fin_step {k : Nat} {t t' : State} (h : BR w s₀ L k t) (ha : FA w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
    (o : Only [.r12] t t') (sy : t'.syms = t.syms) :
    WP isa (.call w.finN w.H.finalize) t' fun u' => BR w s₀ L k u' ∧ TF w s₀ L k u' ∧ u'.syms = s₀.syms := by
  have z := sz hw
  have bS := below_sp hp (o.sp.trans h.er.sp) (n := 96) (by decide)
  refine fin_call (fin_args hp hw h ha o) fun s' a hf => ?_
  have k' : ER w s₀ L s' := (h.er.only o sy).keep hp a.rd a.wr a.sp a.sy a.cs a.frame (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact wk_at hp (.inl (by decide)) (by omega_using [z.hS])
    · exact wk_at hp (.inl (by decide)) (by omega_using [z.hD])
    · exact wk_at hp (.inl (by decide)) (by omega_using [z.hA])
    · rw [bS]; exact wk_at hp (.inr (by decide)) (by decide))
  have hm : t'.mem = t.mem := o.mem
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  have hpl := z.hpl k
  have hil := info_lt hp hw
  refine ⟨h.keep k' (fun r hr => by
      rw [a.cs r (by revert hr; revert r; decide), o.gpr r (by revert hr; revert r; decide)]) ?_,
    fun prk hK => ?_, a.sy.trans (sy.trans h.er.sy)⟩
  · have dO : ∀ r ∈ ([⟨at_ L 216, w.H.S⟩, ⟨at_ L 408, w.H.D⟩, ⟨at_ L 480, w.I.scratch * 8⟩] ++
        [below t'.sp 96] : List Region), Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 0, k * w.H.D⟩ r := by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact out_apart hp (by omega_using [hk]) (by omega_using [z.hS])
      · exact out_apart hp (by omega_using [hk]) (by omega_using [z.hD])
      · exact out_apart hp (by omega_using [hk]) (by omega_using [z.hA])
      · rw [bS]; exact out_apart hp (by omega_using [hk]) (by decide)
    have := keep_fr a.frame dO (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
    rw [BitVec.add_zero] at this
    exact this.trans (by rw [hm])
  · have hl : (k0 w prk).length = w.H.B := blockKey_length w prk
    have hou : w.ok.SH.Repr t.mem (key s₀ + BitVec.ofNat 64 192) (xorPad (k0 w prk) opad) :=
      w.ok.congr _ _ _ _ (fun i hi => ER.keyB hp h.er (o := 192) (n := w.H.S)
        (by omega_using [z.hS]) i hi) hK.2
    have htl : (Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]).length =
        pl w k + infoLen s₀ + 1 := by
      rw [List.length_append, List.length_append, tBlock_len, bytesAt_length]; rfl
    exact hf (k0 w prk) (Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
      hl (by rw [hl, htl]; omega_using [hil, hpl])
      (by rw [hm]; exact hws prk hK) (by rw [o.get .r5, ha.r5, htl]) (by rw [hm]; exact hou)

/-- `finalize`'s arguments. -/
theorem argsF_ok {k : Nat} {t : State} (h : BR w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.block finT) t fun u => BR w s₀ L k u ∧ FA w s₀ L k u ∧
      WS w s₀ L u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) ∧
      u.syms = s₀.syms := by
  have z := sz hw
  have hpl := z.hpl k
  have hil := info_lt hp hw
  unfold finT
  refine WP.of_syms (wp_addSp fun t₁ o₁ e₁ => wp_addi (fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ =>
    wp_add fun t₄ o₄ e₄ => wp_addi (fun t₅ o₅ e₅ => wp_addSp fun t₆ o₆ e₆ => wp_addSp fun t₇ o₇ e₇ =>
    WP.block_nil fun sy => ?_)))
  have K : Keep [.r3, .r4, .r5, .r5, .r5, .r6, .r7] t t₇ :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans o₇.keep)))))).mono
  have m₇ : t₇.mem = t.mem := by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have k₇ : ER w s₀ L t₇ := h.er.same K.rd K.wr K.sp sy (keep_pres K) m₇
  have h₇ : BR w s₀ L k t₇ := h.keep k₇ (fun r hr => K.gpr r (by revert hr; revert r; decide)) (by rw [m₇])
  have sp₅ : t₅.sp = s₀.sp := by rw [o₅.sp, o₄.sp, o₃.sp, o₂.sp, o₁.sp, h.er.sp]
  have fa : FA w s₀ L k t₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, h.er.sp, hp.sp, at_,
        show eWs = 120 from rfl, Offset.add_add]
    · rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂, o₁.get .r15, h.er.r15]
    · rw [o₇.get .r5, o₆.get .r5, e₅, e₄, e₃, o₂.get .r21, o₂.get .r22, o₃.get .r17, o₂.get .r17,
        o₁.get .r21, o₁.get .r22, o₁.get .r17, h.er.r21, h.r22, h.er.r17]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hB : w.H.B < 2 ^ 64 := by omega_using [z.hB]
      rw [Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt (by omega_using [hpl, z.hD] : pl w k < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega_using [z.hB, hpl, z.hD] : w.H.B + pl w k < 2 ^ 64),
        Nat.mod_eq_of_lt (show w.H.B + pl w k + infoLen s₀ < 2 ^ 64 by omega_using [hpl, hil])]
      show (w.H.B + pl w k + infoLen s₀ + 1) % 2 ^ 64 = (w.H.B + (pl w k + infoLen s₀ + 1)) % 2 ^ 64
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
    · rw [o₇.get .r6, e₆, sp₅, hp.sp, at_, show eT = 312 from rfl, Offset.add_add]
    · rw [e₇, o₆.sp, sp₅, hp.sp, at_, show eW = 384 from rfl, Offset.add_add]
  exact ⟨h₇, fa, fun prk hK => by rw [m₇]; exact hws prk hK, sy.trans h.er.sy⟩

/-- `finalize` through the table. -/
theorem callF_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (fa : FA w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (tcall .r14 2 f.fin) t fun u => BR w s₀ L k u ∧ TF w s₀ L k u ∧ u.syms = s₀.syms := by
  unfold tcall
  refine WP.seq (WP.mono (tload2 hp h.er) fun t' ⟨o, e, sy'⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (fin_step hp hw h fa hws o sy')
  show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, sy', h.er.sy]; exact hp.tok.f

/-- `finalize`'s arguments, then `finalize` through the table. -/
theorem stageF_ok {k : Nat} {t : State} (h : BR w s₀ L k t)
    (hws : WS w s₀ L t fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.seq (.block finT) (tcall .r14 2 f.fin)) t fun u => BR w s₀ L k u ∧ TF w s₀ L k u ∧ u.syms = s₀.syms :=
  WP.seq (WP.mono (argsF_ok hp hw h hws) fun _ ⟨hb, fa, hw', _⟩ => callF_ok hp hw hb fa hw')

end

/-! ## The copy to `out` -/

/-- The bytes of `T(k + 1)` block `k + 1` writes to `out`. -/
abbrev nb (w : HVar) (s₀ : State) (k : Nat) : Nat := min w.H.D (outLen s₀ - k * w.H.D)

theorem done_succ {w : HVar} {s₀ : State} {k : Nat} (h : k * w.H.D < outLen s₀) :
    done w s₀ (k + 1) = k * w.H.D + nb w s₀ k := by
  unfold done nb; rw [Nat.succ_mul]; omega_using [h]

/-- The first `n` of `N` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n N : Nat} (h : n ≤ N) :
    bytesAt m p n = (bytesAt m p N).take n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

/-- `min(D, rem)` bytes of `T(k + 1)` to `out`, then the registers for block
`k + 2`. -/
theorem out_ok {k : Nat} {t : State} (h : BR w s₀ L k t) (hT : TF w s₀ L k t) :
    WP isa (.seq (.block outArgs) (.seq copyLoop (.block nextBlock))) t
      fun u => EI w s₀ L (k + 1) u ∧ u.syms = s₀.syms := by
  have z := sz hw
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  have hol' := hp.ol
  have hn0 : 0 < nb w s₀ k := by unfold nb; omega_using [z.hD0, hk]
  have hnD : nb w s₀ k ≤ w.H.D := Nat.min_le_left _ _
  have hnR : k * w.H.D + nb w s₀ k ≤ outLen s₀ := by unfold nb; omega_using [hk]
  unfold outArgs
  refine WP.seq (WP.of_syms (wp_sub fun t₁ o₁ e₁ => wp_lsr (fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_sub fun t₄ o₄ e₄ => wp_and fun t₅ o₅ e₅ => wp_add fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ =>
    wp_addSp fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ => wp_sub fun t₁₀ o₁₀ e₁₀ => WP.block_nil fun sy => ?_)))
  have K : Keep [.r10, .r6, .r7, .r6, .r10, .r6, .r9, .r4, .r5, .r19] t t₁₀ :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans (o₇.keep.trans
      (o₈.keep.trans (o₉.keep.trans o₁₀.keep))))))))).mono
  have m₁₀ : t₁₀.mem = t.mem := by
    rw [o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have k₁₀ : ER w s₀ L t₁₀ := h.er.samec K.rd K.wr K.sp sy (fun r hr hc => K.gpr r (by
    revert hc; revert hr; revert r; decide)) m₁₀
  have a6 : t₁₀.gpr .r6 = BitVec.ofNat 64 (nb w s₀ k) := by
    pupd_simp [o₁₀.gpr, o₉.gpr, o₈.gpr, o₇.gpr, e₆, o₆.gpr, e₅, o₅.gpr, e₄, o₄.gpr, e₃, o₃.gpr, e₂, o₂.gpr,
      e₁, o₁.gpr]
    rw [h.r19, h.er.r20]
    exact Proof.RsaOaep.PPC64LE.minSel (by omega_using [hol', z.hD]) (by omega_using [z.hD])
  have a9 : t₁₀.gpr .r9 = BitVec.ofNat 64 (nb w s₀ k) := by
    rw [o₁₀.get .r9, o₉.get .r9, o₈.get .r9, e₇, ← a6, o₁₀.get .r6, o₉.get .r6, o₈.get .r6, o₇.get .r6]
  have a4 : t₁₀.gpr .r4 = at_ L 408 := by
    rw [o₁₀.get .r4, o₉.get .r4, e₈, o₇.sp, o₆.sp, o₅.sp, o₄.sp, o₃.sp, o₂.sp, o₁.sp, h.er.sp, hp.sp, at_,
      show eT = 312 from rfl, Offset.add_add]
  have a5 : t₁₀.gpr .r5 = out s₀ + BitVec.ofNat 64 (k * w.H.D) := by
    rw [o₁₀.get .r5, e₉, o₈.get .r18, o₇.get .r18, o₆.get .r18, o₅.get .r18, o₄.get .r18, o₃.get .r18,
      o₂.get .r18, o₁.get .r18, h.r18]
  have a19 : t₁₀.gpr .r19 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D) - BitVec.ofNat 64 (nb w s₀ k) := by
    rw [e₁₀, ← o₁₀.get .r6, a6, o₉.get .r19, o₈.get .r19, o₇.get .r19,
      o₆.get .r19, o₅.get .r19, o₄.get .r19, o₃.get .r19, o₂.get .r19, o₁.get .r19, h.r19]
  have hwT : ∀ j < nb w s₀ k, InRegions (t₁₀.rd ++ t₁₀.wr) (at_ L 408 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [at_, Offset.add_add]; exact in_fr hp k₁₀.wr (by omega_using []) (by omega_using [hj, hnD, z.hD])
  have hwO : ∀ i < nb w s₀ k, InRegions t₁₀.wr (out s₀ + BitVec.ofNat 64 (k * w.H.D) + BitVec.ofNat 64 i) 1 :=
    fun i hi => by
      rw [Offset.add_add, k₁₀.wr, hp.wr]
      exact ⟨outR s₀, by simp, Offset.contains_base _ (by omega_using [hi, hnR]) (by omega_using [hi, hnR, hol])⟩
  have dTO : Region.Disjoint ⟨at_ L 408, nb w s₀ k⟩ ⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ :=
    (out_apart hp hnR (by omega_using [hnD, z.hD])).symm
  refine WP.seq (WP.of_syms (WP.mono (copy_run hn0 (by omega_using [hnD, z.hD]) a4 a5 a6 hwT hwO dTO)
    fun u ⟨Ku, Fu, hc⟩ sy' => ?_))
  have ku : ER w s₀ L u := k₁₀.keep hp Ku.rd Ku.wr Ku.sp sy' (keep_pres Ku) Fu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact .inr (Offset.sub_base _ hnR))
  unfold nextBlock
  refine WP.of_syms (wp_add fun v₁ p₁ f₁ => wp_mov fun v₂ p₂ f₂ => wp_addi (fun v₃ p₃ f₃ =>
    WP.block_nil fun sy'' => ?_))
  have Kv : Keep [.r18, .r22, .r23] u v₃ := (p₁.keep.trans (p₂.keep.trans p₃.keep)).mono
  have mv : v₃.mem = u.mem := by rw [p₃.mem, p₂.mem, p₁.mem]
  have kv : ER w s₀ L v₃ := ku.samec Kv.rd Kv.wr Kv.sp sy'' (fun r hr hc => Kv.gpr r (by
    revert hc; revert hr; revert r; decide)) mv
  have hFm : Frame [⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩] t.mem v₃.mem := by
    rw [mv, ← m₁₀]; exact Fu
  have dfr : ∀ {R : Region}, R.Disjoint ⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ → R.len ≤ 2 ^ 64 →
      bytesAt v₃.mem R.base R.len = bytesAt t.mem R.base R.len := fun hd hl =>
    keep_fr hFm (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hpl : pl w (k + 1) = w.H.D := by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
  have hds := done_succ (w := w) (s₀ := s₀) hk
  refine ⟨⟨kv, ?_, ?_, ?_, ?_, fun prk hK => ?_, fun prk hK => ?_⟩, sy''.trans (sy'.trans (sy.trans h.er.sy))⟩
  · rw [p₃.get .r18, p₂.get .r18, f₁, Ku.get .r18, Ku.get .r9, a9, o₁₀.get .r18, o₉.get .r18, o₈.get .r18,
      o₇.get .r18, o₆.get .r18, o₅.get .r18, o₄.get .r18, o₃.get .r18, o₂.get .r18, o₁.get .r18, h.r18,
      Offset.add_add, hds]
  · rw [p₃.get .r19, p₂.get .r19, p₁.get .r19, Ku.get .r19, a19, hds]
    apply BitVec.eq_of_toNat_eq
    have hR : (BitVec.ofNat 64 (outLen s₀ - k * w.H.D)).toNat = outLen s₀ - k * w.H.D := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol])]
    have hN : (BitVec.ofNat 64 (nb w s₀ k)).toNat = nb w s₀ k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hnD, z.hD])]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hR, hN]; omega_using [hnR]), hR, hN,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol])]
    omega_using [hnR]
  · rw [p₃.get .r22, f₂, p₁.get .r20, Ku.get .r20, k₁₀.r20, hpl]
  · rw [f₃, p₂.get .r23, p₁.get .r23, Ku.get .r23, o₁₀.get .r23, o₉.get .r23, o₈.get .r23, o₇.get .r23,
      o₆.get .r23, o₅.get .r23, o₄.get .r23, o₃.get .r23, o₂.get .r23, o₁.get .r23, h.r23, BitVec.ofNat_add_ofNat]
  · have hbl := Proof.Hkdf.blocks_length w.ok.SH.H prk (infoOf s₀) w.ok.hashLen k
    rw [hds, Proof.Hkdf.blocks_succ, List.take_append, List.take_of_length_le (by omega_using [hbl]),
      hbl, Nat.add_sub_cancel_left, VG.Proof.Hmac.Common.bytesAt_add, ← h.ob prk hK]
    congr 1
    · have := dfr (R := ⟨out s₀ + BitVec.ofNat 64 0, k * w.H.D⟩)
        (Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hk, hol]) (by omega_using [hnR, hol]))
        (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
      simpa only [BitVec.add_zero] using this
    · have hcp : bytesAt v₃.mem (out s₀ + BitVec.ofNat 64 (k * w.H.D)) (nb w s₀ k) =
          bytesAt t.mem (at_ L 408) (nb w s₀ k) := by
        simp only [bytesAt]
        exact List.map_congr_left fun i hi => by rw [mv, hc i (List.mem_range.mp hi), m₁₀]
      rw [hcp, bytesAt_take _ _ hnD, hT prk hK]
  · rw [hpl, dfr (R := ⟨at_ L 408, w.H.D⟩) (out_apart hp hnR (by omega_using [z.hD])).symm
      (by show w.H.D ≤ 2 ^ 64; omega_using [z.hD])]
    exact hT prk hK

end

/-! ## The blocks -/

/-- While bytes of `out` are left, the state before block `k + 1` is one during it. -/
theorem ei_br {w : HVar} {s₀ : State} {L : Addr} {k : Nat} {t : State} (h : EI w s₀ L k t) (hs : t.gpr .r19 ≠ 0) :
    BR w s₀ L k t ∧ TB w s₀ L k t := by
  have hlt : k * w.H.D < outLen s₀ := by
    refine Nat.lt_of_not_le fun hc => hs ?_
    rw [h.r19, show done w s₀ k = outLen s₀ from Nat.min_eq_right hc, Nat.sub_self]; rfl
  have hd : done w s₀ k = k * w.H.D := Nat.min_eq_left (Nat.le_of_lt hlt)
  refine ⟨⟨h.er, by rw [h.r18, hd], by rw [h.r19, hd], h.r22, h.r23, hlt, fun prk hK => ?_⟩, h.tb⟩
  have := h.ob prk hK
  rw [hd] at this
  rw [this, List.take_of_length_le (by
    rw [Proof.Hkdf.blocks_length w.ok.SH.H prk (infoOf s₀) w.ok.hashLen k])]

/-- `ofNat x` is not zero for a positive `x` below `2 ^ 64`. -/
theorem ofNat_ne_zero {x : Nat} (h₀ : 0 < x) (h : x < 2 ^ 64) : BitVec.ofNat 64 x ≠ 0 := fun e =>
  absurd (congrArg BitVec.toNat e) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; exact Nat.ne_of_gt h₀)

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L) (hw : HOk w)
include hp hw

/-- One block. -/
theorem block_ok {k : Nat} {t : State} (h : EI w s₀ L k t) (hs : t.gpr .r19 ≠ 0) :
    WP isa (block f) t fun u => EI w s₀ L (k + 1) u ∧ u.syms = s₀.syms := by
  obtain ⟨hb, ht⟩ := ei_br h hs
  unfold block
  refine WP.seq (WP.mono (copy_ok hp hw hb ht) fun t₁ ⟨b₁, h₁, w₁, _⟩ => ?_)
  refine WP.seq (WP.mono (stageT_ok hp hw b₁ h₁ w₁) fun t₂ ⟨b₂, h₂, w₂, _⟩ => ?_)
  refine WP.seq (WP.mono (stageI_ok hp hw b₂ h₂ w₂) fun t₃ ⟨b₃, h₃, w₃, _⟩ => ?_)
  refine WP.seq (WP.mono (stageC_ok hp hw b₃ h₃ w₃) fun t₄ ⟨b₄, h₄, w₄, _⟩ => ?_)
  refine WP.seq (WP.mono (stageF_ok hp hw b₄ w₄) fun t₅ ⟨b₅, h₅, _⟩ => ?_)
  exact out_ok hp hw b₅ h₅

/-- The blocks, while bytes of `out` are left. -/
theorem loop_ok {k : Nat} {t : State} (h : EI w s₀ L k t) (hs : t.gpr .r19 ≠ 0) :
    WP isa (.loop (block f) (.nonzero .d .r19)) t fun u =>
      ∃ K, EI w s₀ L K u ∧ outLen s₀ ≤ K * w.H.D ∧ u.syms = s₀.syms := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  have hD0 := w.ok.hD0
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧ EI w s₀ L j u ∧ u.gpr .r19 ≠ 0)
    ?_ _ t ⟨k, rfl, h, hs⟩
  rintro n u ⟨j, rfl, hj, hu⟩
  have hlt := (ei_br hj hu).1.lt
  refine WP.mono (block_ok hp hw hj hu) fun v ⟨hv, sy⟩ => ?_
  rw [eval_nonzero_ofNat' v .r19 (by omega_using [hol]) hv.r19]
  by_cases e : outLen s₀ ≤ (j + 1) * w.H.D
  · refine .inl ⟨?_, j + 1, hv, e, sy⟩
    rw [show done w s₀ (j + 1) = outLen s₀ from Nat.min_eq_right e, Nat.sub_self]; rfl
  · have hd : done w s₀ (j + 1) = (j + 1) * w.H.D := Nat.min_eq_left (by omega_using [e])
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    refine .inr ⟨?_, outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, e, hD0, hsm], j + 1, rfl, hv, ?_⟩
    · rw [hd, decide_eq_true (by omega_using [e] : outLen s₀ - (j + 1) * w.H.D ≠ 0)]
    · rw [hv.r19, hd]; exact ofNat_ne_zero (by omega_using [e]) (by omega_using [hol])

omit hw in
/-- The epilogue: the return address and our caller's registers restored. -/
theorem epi_ok {t : State} (k : ER w s₀ L t) :
    WP isa (.block expandEpi) t fun v => (∀ r ∈ preserved, v.gpr r = s₀.gpr r) ∧ v.sp = s₀.sp ∧
      v.lr = s₀.lr ∧ v.mem = t.mem := by
  unfold expandEpi restoreLr
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun t₁ o₁ e₁ => ?_
  have b₁ : t₁.gpr .r11 = at_ L 96 := by rw [e₁, k.sp, hp.sp, BitVec.add_zero]
  refine wp_ld (a := at_ L 128) (by rw [b₁, show oLr = 32 from rfl, at_, Offset.add_add])
    (in_fr hp (by rw [o₁.wr, k.wr]) (by decide) (by decide))
    fun t₂ o₂ e₂ => wp_mtlr fun t₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  have b₃ : t₃.gpr .r11 = at_ L 96 := by rw [g₃, o₂.get .r11, b₁]
  refine WP.mono (Spill.restore_wp (b := .r11) (l := eSaved) (by decide) b₃ (by decide) (by decide)
    (fun q hq => by
      rw [at_, Offset.add_add]
      have := saved_in q hq
      exact in_fr hp (by rw [wr₃, o₂.wr, o₁.wr, k.wr]) (by omega_using [this]) (by omega_using [this]))
    (by rw [m₃, o₂.mem, o₁.mem]; exact k.saved)) fun v hr => ⟨fun r hr' => ?_, by rw [hr.sp, sp₃, o₂.sp, o₁.sp, k.sp],
      by rw [hr.lr, lr₃, e₂, o₁.mem, k.svlr], by rw [hr.mem, m₃, o₂.mem, o₁.mem]⟩
  refine hr.gpr_of ?_
  by_cases hk : r ∈ eregs
  · exact .inl (by revert hk; revert r; decide)
  · refine .inr ?_
    have n0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr' (by decide)
    have n11 : r ∉ [Reg.r11] := fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr' (by decide)
    rw [g₃, o₂.gpr r n0, o₁.gpr r n11, k.cs r hr' hk]

/-- The frame's body. -/
theorem main_ok : WP isa (expandMain f) s₀ fun u => (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧
      u.sp = s₀.sp ∧ u.lr = s₀.lr ∧ ∀ prk, Keyd w s₀ prk →
        bytesAt u.mem (out s₀) (outLen s₀) =
          (Spec.Hkdf.blocks w.ok.SH.H prk (infoOf s₀) ((outLen s₀ + w.H.D - 1) / w.H.D) [] 1).take (outLen s₀) := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  have hD0 := w.ok.hD0
  unfold expandMain
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => ?_)
  have hd0 : done w s₀ 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  have s19 : t₁.gpr .r19 = BitVec.ofNat 64 (outLen s₀) := by rw [h₁.r19, hd0, Nat.sub_zero]
  refine WP.seq (WP.mono (Q := fun (u : State) => ∃ K, EI w s₀ L K u ∧ outLen s₀ ≤ K * w.H.D ∧ u.syms = s₀.syms)
    (WP.ite _ (eval_nonzero_ofNat' t₁ .r19 hol s19) (fun ht => ?_) (fun he => ?_)) fun t₂ ⟨K, h₂, hK, _⟩ => ?_)
  · exact loop_ok hp hw h₁ (by
      rw [s19]; exact ofNat_ne_zero (Nat.pos_of_ne_zero (of_decide_eq_true ht)) hol)
  · refine WP.block_nil ⟨0, h₁, ?_, h₁.er.sy⟩
    rw [Decidable.not_not.mp (of_decide_eq_false he)]; exact Nat.zero_le _
  refine WP.mono (epi_ok hp h₂.er) fun u ⟨hcs, hsp, hlr, hm⟩ => ⟨hcs, hsp, hlr, fun prk hk => ?_⟩
  have hdK : done w s₀ K = outLen s₀ := Nat.min_eq_right hK
  have ob := h₂.ob prk hk
  rw [hdK] at ob
  rw [hm, ob]
  -- Both block counts cover the `L` bytes.
  have hN : outLen s₀ ≤ (outLen s₀ + w.H.D - 1) / w.H.D * w.H.D := by
    have e₁ := Nat.div_add_mod (outLen s₀ + w.H.D - 1) w.H.D
    have e₂ := Nat.mod_lt (outLen s₀ + w.H.D - 1) hD0
    rw [Nat.mul_comm] at e₁
    omega_using [e₁, e₂, hD0]
  have tk := fun a b (ha : outLen s₀ ≤ a * w.H.D) =>
    Proof.Hkdf.blocks_take w.ok.SH.H prk (infoOf s₀) w.ok.hashLen (a := a) ha b
  rcases Nat.le_total K ((outLen s₀ + w.H.D - 1) / w.H.D) with hl | hl
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
    rw [hj, tk K j hK]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
    rw [hj, tk _ j hN]

end

/-- `vg_hkdf_expand`, in its frame. -/
theorem expand_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (expandR w f ns eStack).pre s) :
    WP isa (expand f) s fun s' => abiPreserved s s' ∧ (expandR w f ns eStack).post s s' := by
  have hsp : eStack ≤ s.sp.toNat := hp.2.2.2.2.2.2.1
  obtain p := pre_alloc hp
  obtain ⟨e₀, -, -⟩ := alloc_at s (F := eFr) (C := 96) hsp
  unfold expand
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by rw [eStack_eq] at hsp; rw [eFr_eq]; omega_using [hsp])
    (WP.mono (main_ok p hw) fun v ⟨hcs, hvsp, hlr, hP⟩ m un fl => ?_)
  refine ⟨free_abi hcs hvsp hlr m un, fun prk hK => ?_⟩
  have hfs : Region.Sub ⟨s.sp - BitVec.ofNat 64 eFr, eFr⟩ ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  have hfs8 : Region.Sub ⟨s.sp - BitVec.ofNat 64 eFr, 8⟩ ⟨s.sp - BitVec.ofNat 64 eStack, eStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  -- The `free` loses the frame's bytes, which lie apart from `out`.
  obtain e : bytesAt m (s.gpr .r6) (s.gpr .r7).toNat = bytesAt v.mem (s.gpr .r6) (s.gpr .r7).toNat :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => lost_byte fl (R := outR (allocated eFr s))
      (p.s_o.sub_left hfs).symm hi
  -- The push's back chain lies apart from `key` and `info`.
  have hm := alloc_mem s eFr
  have hK' : Keyd w (allocated eFr s) prk := by
    refine ⟨w.ok.congr _ _ _ _ (fun i hi => ?_) hK.1, w.ok.congr _ _ _ _ (fun i hi => ?_) hK.2⟩
    · have := hm.bytes (R := ⟨s.gpr .r3, 384⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (p.s_k.sub_left hfs8).symm)
        (by show 384 ≤ 2 ^ 64; decide) (i := i) (by show i < 384; have := (sz hw).hS; omega_using [hi, this])
      exact this
    · have := hm.bytes (R := ⟨s.gpr .r3, 384⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (p.s_k.sub_left hfs8).symm)
        (by show 384 ≤ 2 ^ 64; decide) (i := 192 + i) (by show 192 + i < 384; have := (sz hw).hS; omega_using [hi, this])
      rwa [← Offset.add_add] at this
  have hinfo : infoOf (allocated eFr s) = bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat :=
    bytes_keep (R := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩) hm (p.s_i.sub_left hfs8).symm (Nat.le_of_lt (s.gpr .r5).isLt)
  rw [e]
  have hP' := hP prk hK'
  rw [hinfo] at hP'
  refine Eq.trans ?_ (congrArg some hP').symm
  have hol : (s.gpr .r7).toNat ≤ 255 * w.H.D := p.ol
  unfold Spec.Hkdf.expand
  rw [ite_eq_right (Nat.not_lt.mpr hol)]
  rfl

/-! ## Constant time -/

/-- The registers that hold public values from the prologue on. -/
abbrev pubRegs : List Reg := eregs

/-- The taint checks of the pieces of `vg_hkdf_expand` between the calls. -/
structure EChecks : Prop where
  pro : Ck [.r3, .r4, .r5, .r6, .r7, .r8] (.block expandPro)
  tl1 : Ck [.r14] (.block [.load .d .r12 .r14 (8 * 1)])
  tl2 : Ck [.r14] (.block [.load .d .r12 .r14 (8 * 2)])
  cp : Ck pubRegs (.seq (.block copyArgs) copyLoop)
  uT : Ck pubRegs (.block updT)
  uI : Ck pubRegs (.block updI)
  uC : Ck pubRegs (.block updC)
  fT : Ck pubRegs (.block finT)
  ou : Ck pubRegs (.seq (.block outArgs) (.seq copyLoop (.block nextBlock)))
  nil : Ck [] (.block [])
  epi : Ck [] (.block expandEpi)

theorem echecks : EChecks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : HVar) (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  regs : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8], s₀.gpr r = s₀'.gpr r
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.finN = s₀'.syms w.finN

section
variable {w : HVar} {f : Fns} {s₀ s₀' : State} {L : Addr} (hp : Pre w f s₀ L) (hp' : Pre w f s₀' L)
  (hq : PubEq w s₀ s₀') (hw : HOk w)
include hp hp' hq hw

omit hp hp' hw in
/-- During the same block, the two runs agree on the public registers. -/
theorem agB {k : Nat} {t t' : State} (h : BR w s₀ L k t) (h' : BR w s₀' L k t') :
    t.sp = t'.sp ∧ ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  have e7 := hq.regs .r7 (by simp)
  refine ⟨by rw [h.er.sp, h'.er.sp, hq.sp], fun r hr => ?_⟩
  simp only [pubRegs, eregs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.er.r14, h'.er.r14]; exact hq.regs .r8 (by simp)
  · rw [h.er.r15, h'.er.r15]; exact hq.regs .r3 (by simp)
  · rw [h.er.r16, h'.er.r16]; exact hq.regs .r4 (by simp)
  · rw [h.er.r17, h'.er.r17]; exact hq.regs .r5 (by simp)
  · rw [h.r18, h'.r18, show out s₀ = out s₀' from hq.regs .r6 (by simp)]
  · rw [h.r19, h'.r19, show outLen s₀ = outLen s₀' from congrArg BitVec.toNat e7]
  · rw [h.er.r20, h'.er.r20]
  · rw [h.er.r21, h'.er.r21]
  · rw [h.r22, h'.r22]
  · rw [h.r23, h'.r23]

omit hp hp' hw in
theorem ag14 {k : Nat} {t t' : State} (h : BR w s₀ L k t) (h' : BR w s₀' L k t') :
    t.sp = t'.sp ∧ ∀ r ∈ [Reg.r14], t.gpr r = t'.gpr r :=
  ⟨(agB hq h h').1, fun r hr => (agB hq h h').2 r (by simp at hr; subst hr; simp)⟩

omit hp hp' hw in
/-- Before the same block, the two runs have as many bytes of `out` left. -/
theorem s19E {k : Nat} {t t' : State} (h : EI w s₀ L k t) (h' : EI w s₀' L k t') : t.gpr .r19 = t'.gpr .r19 := by
  rw [h.r19, h'.r19]
  show BitVec.ofNat 64 ((s₀.gpr .r7).toNat - min (k * w.H.D) (s₀.gpr .r7).toNat) =
    BitVec.ofNat 64 ((s₀'.gpr .r7).toNat - min (k * w.H.D) (s₀'.gpr .r7).toNat)
  rw [hq.regs .r7 (by simp)]

/-- One block leaks the same trace in both runs. -/
theorem block_rel (j : Nat) :
    RelCT isa (fun t t' => (EI w s₀ L j t ∧ t.gpr .r19 ≠ 0) ∧ (EI w s₀' L j t' ∧ t'.gpr .r19 ≠ 0)) (block f)
      fun u u' => (EI w s₀ L (j + 1) u ∧ u.syms = s₀.syms) ∧ (EI w s₀' L (j + 1) u' ∧ u'.syms = s₀'.syms) := by
  have kc := echecks
  have e3 := hq.regs .r3 (by simp); have e4 := hq.regs .r4 (by simp); have e5 := hq.regs .r5 (by simp)
  have il : infoLen s₀ = infoLen s₀' := congrArg BitVec.toNat e5
  unfold block
  have r1 := rel_agree (P₁ := fun t => EI w s₀ L j t ∧ t.gpr .r19 ≠ 0)
    (P₂ := fun t => EI w s₀' L j t ∧ t.gpr .r19 ≠ 0)
    (G₁ := fun u => BR w s₀ L j u ∧ TB w s₀ L j u ∧ WS w s₀ L u (fun _ => []) ∧ u.syms = s₀.syms)
    (G₂ := fun u => BR w s₀' L j u ∧ TB w s₀' L j u ∧ WS w s₀' L u (fun _ => []) ∧ u.syms = s₀'.syms)
    (rs := pubRegs) (fun t t' h h' => agB hq (ei_br h.1 h.2).1 (ei_br h'.1 h'.2).1) kc.cp
    (fun t h => copy_ok hp hw (ei_br h.1 h.2).1 (ei_br h.1 h.2).2)
    (fun t h => copy_ok hp' hw (ei_br h.1 h.2).1 (ei_br h.1 h.2).2)
  have r2 := rel_agree (P₁ := fun u => BR w s₀ L j u ∧ TB w s₀ L j u ∧ WS w s₀ L u (fun _ => []) ∧ u.syms = s₀.syms)
    (P₂ := fun u => BR w s₀' L j u ∧ TB w s₀' L j u ∧ WS w s₀' L u (fun _ => []) ∧ u.syms = s₀'.syms)
    (G₁ := AT w s₀ L j (at_ L 408) (pl w j) 0 fun _ => []) (G₂ := AT w s₀' L j (at_ L 408) (pl w j) 0 fun _ => [])
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uT
    (fun t h => argsT_ok hp hw h.1 h.2.1 h.2.2.1) (fun t h => argsT_ok hp' hw h.1 h.2.1 h.2.2.1)
  have r3 : RelCT isa (fun t t' => AT w s₀ L j (at_ L 408) (pl w j) 0 (fun _ => []) t ∧
      AT w s₀' L j (at_ L 408) (pl w j) 0 (fun _ => []) t') (tcall .r14 1 f.upd)
      fun u u' => PT w s₀ L j u ∧ PT w s₀' L j u' :=
    rel_wp (tcall_rel (rs := [.r14]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag14 hq a.br a'.br)
      (fun t a => tload1 hp a.br.er) (fun t a => by rw [hq.up]; exact tload1 hp' a.br.er)
      (fun t a => by rw [a.sy]; exact hp.tok.u) (fun t a => by rw [a.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, a, o, _, _⟩, ⟨t', a', o', _, _⟩⟩ => ⟨upd_args hp hw a.br a.ua o,
        upd_args hp' hw a'.br a'.ua o', by rw [o.sp, o'.sp, a.br.er.sp, a'.br.er.sp, hq.sp],
        by rw [o.get .r4, o'.get .r4, a.r4, a'.r4]⟩))
      (fun t a => callT_ok hp hw a) (fun t a => callT_ok hp' hw a)
  have r4 := rel_agree (P₁ := PT w s₀ L j) (P₂ := PT w s₀' L j)
    (G₁ := AT w s₀ L j (info s₀) (infoLen s₀) (pl w j) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j)
    (G₂ := AT w s₀' L j (info s₀') (infoLen s₀') (pl w j) fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uI
    (fun t h => argsI_ok hp hw h.1 h.2.1 h.2.2.1) (fun t h => argsI_ok hp' hw h.1 h.2.1 h.2.2.1)
  have r5 : RelCT isa (fun t t' =>
      AT w s₀ L j (info s₀) (infoLen s₀) (pl w j) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j) t ∧
      AT w s₀' L j (info s₀') (infoLen s₀') (pl w j) (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j) t')
      (tcall .r14 1 f.upd) fun u u' => PI w s₀ L j u ∧ PI w s₀' L j u' :=
    rel_wp (tcall_rel (rs := [.r14]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag14 hq a.br a'.br)
      (fun t a => tload1 hp a.br.er) (fun t a => by rw [hq.up]; exact tload1 hp' a.br.er)
      (fun t a => by rw [a.sy]; exact hp.tok.u) (fun t a => by rw [a.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, a, o, _, _⟩, ⟨t', a', o', _, _⟩⟩ => ⟨upd_args hp hw a.br a.ua o,
        by have := upd_args hp' hw a'.br a'.ua o'; simp only [info, infoLen] at this ⊢; rwa [← e4, ← e5] at this,
        by rw [o.sp, o'.sp, a.br.er.sp, a'.br.er.sp, hq.sp],
        by rw [o.get .r4, o'.get .r4, a.r4, a'.r4]⟩))
      (fun t a => callI_ok hp hw a) (fun t a => callI_ok hp' hw a)
  have r6 := rel_agree (P₁ := PI w s₀ L j) (P₂ := PI w s₀' L j) (G₁ := AC w s₀ L j) (G₂ := AC w s₀' L j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uC
    (fun t h => argsC_ok hp hw h.1 h.2.1 h.2.2.1) (fun t h => argsC_ok hp' hw h.1 h.2.1 h.2.2.1)
  have r7 : RelCT isa (fun t t' => AC w s₀ L j t ∧ AC w s₀' L j t') (tcall .r14 1 f.upd)
      fun u u' => PC w s₀ L j u ∧ PC w s₀' L j u' :=
    rel_wp (tcall_rel (rs := [.r14]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag14 hq a.1.br a'.1.br)
      (fun t a => tload1 hp a.1.br.er) (fun t a => by rw [hq.up]; exact tload1 hp' a.1.br.er)
      (fun t a => by rw [a.1.sy]; exact hp.tok.u) (fun t a => by rw [a.1.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, a, o, _, _⟩, ⟨t', a', o', _, _⟩⟩ => ⟨upd_args hp hw a.1.br a.1.ua o,
        upd_args hp' hw a'.1.br a'.1.ua o', by rw [o.sp, o'.sp, a.1.br.er.sp, a'.1.br.er.sp, hq.sp],
        by rw [o.get .r4, o'.get .r4, a.1.r4, a'.1.r4, il]⟩))
      (fun t a => callC_ok hp hw a) (fun t a => callC_ok hp' hw a)
  have r8 := rel_agree (P₁ := PC w s₀ L j) (P₂ := PC w s₀' L j)
    (G₁ := fun u => BR w s₀ L j u ∧ FA w s₀ L j u ∧ WS w s₀ L u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk
      (infoOf s₀) j ++ infoOf s₀ ++ [BitVec.ofNat 8 (j + 1)]) ∧ u.syms = s₀.syms)
    (G₂ := fun u => BR w s₀' L j u ∧ FA w s₀' L j u ∧ WS w s₀' L u (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk
      (infoOf s₀') j ++ infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]) ∧ u.syms = s₀'.syms)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.fT
    (fun t h => argsF_ok hp hw h.1 h.2.2.1) (fun t h => argsF_ok hp' hw h.1 h.2.2.1)
  have r9 : RelCT isa (fun t t' =>
      (BR w s₀ L j t ∧ FA w s₀ L j t ∧ WS w s₀ L t (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀) j ++
        infoOf s₀ ++ [BitVec.ofNat 8 (j + 1)]) ∧ t.syms = s₀.syms) ∧
      (BR w s₀' L j t' ∧ FA w s₀' L j t' ∧ WS w s₀' L t' (fun prk => Proof.Hkdf.tBlock w.ok.SH.H prk (infoOf s₀') j ++
        infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]) ∧ t'.syms = s₀'.syms)) (tcall .r14 2 f.fin)
      fun u u' => (BR w s₀ L j u ∧ TF w s₀ L j u ∧ u.syms = s₀.syms) ∧
        (BR w s₀' L j u' ∧ TF w s₀' L j u' ∧ u'.syms = s₀'.syms) :=
    rel_wp (tcall_rel (rs := [.r14]) (a := s₀.syms w.finN) kc.tl2 (fun t t' a a' => ag14 hq a.1 a'.1)
      (fun t a => tload2 hp a.1.er) (fun t a => by rw [hq.hf]; exact tload2 hp' a.1.er)
      (fun t a => by rw [a.2.2.2]; exact hp.tok.f) (fun t a => by rw [a.2.2.2, hq.hf]; exact hp'.tok.f)
      (fin_rel fun u u' ⟨⟨t, a, o, _, _⟩, ⟨t', a', o', _, _⟩⟩ => ⟨fin_args hp hw a.1 a.2.1 o,
        by have := fin_args hp' hw a'.1 a'.2.1 o'; simp only [key] at this ⊢; rwa [← e3] at this,
        by rw [o.sp, o'.sp, a.1.er.sp, a'.1.er.sp, hq.sp],
        by rw [o.get .r5, o'.get .r5, a.2.1.r5, a'.2.1.r5, il]⟩))
      (fun t a => callF_ok hp hw a.1 a.2.1 a.2.2.1) (fun t a => callF_ok hp' hw a.1 a.2.1 a.2.2.1)
  have r10 := rel_agree (P₁ := fun u => BR w s₀ L j u ∧ TF w s₀ L j u ∧ u.syms = s₀.syms)
    (P₂ := fun u => BR w s₀' L j u ∧ TF w s₀' L j u ∧ u.syms = s₀'.syms)
    (G₁ := fun u => EI w s₀ L (j + 1) u ∧ u.syms = s₀.syms) (G₂ := fun u => EI w s₀' L (j + 1) u ∧ u.syms = s₀'.syms)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.ou
    (fun t h => out_ok hp hw h.1 h.2.1) (fun t h => out_ok hp' hw h.1 h.2.1)
  exact r1.seq ((r2.seq r3).seq ((r4.seq r5).seq ((r6.seq r7).seq ((r8.seq r9).seq r10))))

/-- The blocks leak the same trace in both runs. -/
theorem loop_rel {k : Nat} :
    RelCT isa (fun t t' => (EI w s₀ L k t ∧ t.gpr .r19 ≠ 0) ∧ (EI w s₀' L k t' ∧ t'.gpr .r19 ≠ 0))
      (.loop (block f) (.nonzero .d .r19)) fun u u' => (∃ K, EI w s₀ L K u) ∧ (∃ K, EI w s₀' L K u') := by
  have hD0 := w.ok.hD0
  refine (RelCT.loop (M := isa) (I := fun n (t t' : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧
      ((EI w s₀ L j t ∧ t.gpr .r19 ≠ 0) ∧ (EI w s₀' L j t' ∧ t'.gpr .r19 ≠ 0))) (fun n => ?_)
      (outLen s₀ - k * w.H.D)).mono (fun t t' h => ⟨k, rfl, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hn : n = outLen s₀ - j * w.H.D
  · subst hn
    refine (block_rel hp hp' hq hw j).mono (fun t t' h => h.2) fun u u' ⟨⟨hv, _⟩, ⟨hv', _⟩⟩ => ?_
    have e := s19E hq hv hv'
    refine ⟨by rw [eval_nonzero, eval_nonzero, e], fun _ => ⟨⟨_, hv⟩, ⟨_, hv'⟩⟩, fun hc => ?_⟩
    have hs : u.gpr .r19 ≠ 0 := by rw [eval_nonzero] at hc; simpa using hc
    have hlt := (ei_br hv hs).1.lt
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    exact ⟨outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, hsm, hD0], j + 1, rfl, ⟨hv, hs⟩, ⟨hv', e ▸ hs⟩⟩
  · exact RelCT.of_false fun _ _ h => hn h.1

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (expandMain f) fun _ _ => True := by
  have kc := echecks
  unfold expandMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := EI w s₀ L 0) (G₂ := EI w s₀' L 0)
    (rs := [.r3, .r4, .r5, .r6, .r7, .r8]) (fun s s' hs hs' => by subst hs hs'; exact ⟨hq.sp, hq.regs⟩) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => EI w s₀ L 0 t ∧ EI w s₀' L 0 t')
      (.ite (.nonzero .d .r19) (.loop (block f) (.nonzero .d .r19)) (.block []))
      fun u u' => (∃ K, EI w s₀ L K u) ∧ (∃ K, EI w s₀' L K u') := by
    refine RelCT.ite (fun t t' h => by rw [eval_nonzero, eval_nonzero, s19E hq h.1 h.2]) ?_ ?_
    · refine (loop_rel hp hp' hq hw (k := 0)).mono (fun t t' h => ?_) fun _ _ h => h
      obtain ⟨⟨h₁, h₂⟩, hc⟩ := h
      have hs : t.gpr .r19 ≠ 0 := by rw [eval_nonzero] at hc; simpa using hc
      exact ⟨⟨h₁, hs⟩, ⟨h₂, s19E hq h₁ h₂ ▸ hs⟩⟩
    · exact (rel_agree (P₁ := EI w s₀ L 0) (P₂ := EI w s₀' L 0) (G₁ := fun u => ∃ K, EI w s₀ L K u)
        (G₂ := fun u => ∃ K, EI w s₀' L K u) (rs := []) (fun t t' h h' => ⟨by rw [h.er.sp, h'.er.sp, hq.sp], by simp⟩)
        kc.nil (fun t h => WP.block_nil ⟨0, h⟩) (fun t h => WP.block_nil ⟨0, h⟩)).mono (fun t t' h => h.1)
        fun _ _ h => h
  have r3 := rel_agree (P₁ := fun u => ∃ K, EI w s₀ L K u) (P₂ := fun u => ∃ K, EI w s₀' L K u)
    (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [])
    (fun t t' ⟨_, k⟩ ⟨_, k'⟩ => ⟨by rw [k.er.sp, k'.er.sp, hq.sp], fun _ h => absurd h List.not_mem_nil⟩) kc.epi
    (fun t ⟨_, k⟩ => WP.mono (epi_ok hp k.er) fun _ _ => trivial)
    (fun t ⟨_, k⟩ => WP.mono (epi_ok hp' k.er) fun _ _ => trivial)
  exact (r1.seq (r2.seq r3)).mono (fun _ _ h => h) fun _ _ _ => trivial

end

/-- `vg_hkdf_expand` is constant time: two runs whose public data agree
leak the same trace. -/
theorem expand_ct {w : HVar} {f : Fns} {ns : List String} (hw : HOk w) (hns : ∀ n ∈ [w.H.updN, w.finN], n ∈ ns) :
    ConstantTime isa (expandR w f ns eStack).pre (expandR w f ns eStack).pub (expand f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, qn⟩ := hpub
  rw [← qsp] at hp'
  have hq : PubEq w (allocated eFr e) (allocated eFr e') :=
    ⟨by simp only [allocated, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q3, q4, q5, q6, q7, q8], qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (expand f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold expand
  refine RelCT.alloc (fun x y ⟨hx, hy⟩ => by rw [hx, hy, qsp]) ((main_rel hp hp' hq hw).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.PPC64LE.Expand
