module

public import VerifiedGarbage.Proof.Hkdf.PPC64LE.Key
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Hkdf.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-!
# HKDF on PPC64LE: `vg_hkdf_extract`, correct

The contract the proof is written against (`extractR`), for the table
`hmac` of one hash function `w` (`HVar`), whose functions an indirect call
of `f`'s reaches: `extract(salt, salt_len, ikm, ikm_len, prk, prk_len,
hmac)` writes `HMAC(salt, IKM)` to `prk`, which is `D` bytes long. The stack
the function uses (`xStack` bytes) is, from its lowest byte `L` up, the 144
bytes the functions it calls use and its frame (`xFr` bytes: the return
address and our caller's `r14`–`r17` at `L + 176`, HMAC's inner and outer
states at `L + 224` and `L + 416`, the working space at `L + 608`). The
prologue saves the return address and our caller's registers, keeps the
arguments it needs after the calls in `r14`–`r17` (`pro_ok`, from which on
`XR` holds); then `init` with the salt as the key, `update` with the input
keying material and `finalize` into `prk`, each through the table
(`init_ok`, `upd_ok`, `fin_ok`); and the epilogue restores the return
address and our caller's registers.
-/

@[expose] public section

namespace VG.Proof.Hkdf.PPC64LE.Extract

open VG.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_mov wp_addi wp_add wp_addSp wp_ld wp_std wp_mflr wp_mtlr)
open VG.Impl.Hkdf.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.HmacTable.PPC64LE (HVar TabOK TabMem)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

/-- `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`, with `N`
bytes of stack, for the table `hmac` of `w`, whose functions an indirect call
of `f`'s reaches, with the addresses of the functions `ns` public. -/
def extractR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let salt : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let ikm : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let prk : Region := ⟨s.gpr .r7, w.H.D⟩
    let tab : Region := ⟨s.gpr .r9, 48⟩
    let stk : Region := below s.sp N
    s.rd = [salt, ikm, tab] ∧ s.wr = [prk] ∧ (s.gpr .r8).toNat = w.H.D ∧
      salt.Disjoint prk ∧ ikm.Disjoint prk ∧ tab.Disjoint prk ∧ N ≤ s.sp.toNat ∧
      stk.Disjoint salt ∧ stk.Disjoint ikm ∧ stk.Disjoint prk ∧ stk.Disjoint tab ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + w.H.D ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 48 ≤ 2 ^ 64 ∧
      TabMem w s.syms (s.gpr .r9) s.mem ∧
      s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B ∧ TabOK w f s.syms
  post s s' := bytesAt s'.mem (s.gpr .r7) w.H.D =
    Spec.Hkdf.extract w.ok.SH.H (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_extract` uses: its frame, and below it what HMAC's
functions use. -/
def xStack : Nat := xFr + 144

theorem xFr_eq : xFr = 2336 := rfl
theorem xStack_eq : xStack = 2480 := rfl

section
variable (s₀ : State)

/-- The arguments, on entry to the frame's body. -/
abbrev salt : Addr := s₀.gpr .r3
abbrev saltLen : Nat := (s₀.gpr .r4).toNat
abbrev ikm : Addr := s₀.gpr .r5
abbrev ikmLen : Nat := (s₀.gpr .r6).toNat
abbrev prk : Addr := s₀.gpr .r7
abbrev tab : Addr := s₀.gpr .r9

abbrev saltR : Region := ⟨salt s₀, saltLen s₀⟩
abbrev ikmR : Region := ⟨ikm s₀, ikmLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩

end

/-- An address of the stack, from its lowest byte. -/
abbrev at_ (L : Addr) (d : Nat) : Addr := L + BitVec.ofNat 64 d

/-- `prk`. -/
abbrev prkR (w : HVar) (s₀ : State) : Region := ⟨prk s₀, w.H.D⟩

/-- The stack the function uses. -/
abbrev stkR (L : Addr) : Region := ⟨L, xStack⟩

/-- The regions the frame's body writes. -/
abbrev wrs (w : HVar) (s₀ : State) (L : Addr) : List Region := [stkR L, prkR w s₀]

/-- The state the frame's body starts in, from the stack's lowest byte `L`. -/
structure Pre (w : HVar) (f : Fns) (s₀ : State) (L : Addr) : Prop where
  sp : s₀.sp = at_ L 144
  nL : L.toNat + xStack ≤ 2 ^ 64
  rd : s₀.rd = [saltR s₀, ikmR s₀, tabR s₀]
  wr : s₀.wr = [⟨at_ L 176, 2304⟩, prkR w s₀]
  pl : (s₀.gpr .r8).toNat = w.H.D
  s_p : (saltR s₀).Disjoint (prkR w s₀)
  i_p : (ikmR s₀).Disjoint (prkR w s₀)
  t_p : (tabR s₀).Disjoint (prkR w s₀)
  k_s : (stkR L).Disjoint (saltR s₀)
  k_i : (stkR L).Disjoint (ikmR s₀)
  k_p : (stkR L).Disjoint (prkR w s₀)
  k_t : (stkR L).Disjoint (tabR s₀)
  ns : (salt s₀).toNat + saltLen s₀ ≤ 2 ^ 64
  ni : (ikm s₀).toNat + ikmLen s₀ ≤ 2 ^ 64
  np : (prk s₀).toNat + w.H.D ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w s₀.syms (tab s₀) s₀.mem
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B
  tok : TabOK w f s₀.syms

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hp : (extractR w f ns xStack).pre s) :
    Pre w f (allocated xFr s) (s.sp - BitVec.ofNat 64 xStack) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hp
  obtain ⟨e₀, -, hn⟩ := alloc_at s (F := xFr) (C := 144) h7
  have hfr : Region.Sub ⟨s.sp - BitVec.ofNat 64 xFr, 8⟩ ⟨s.sp - BitVec.ofNat 64 xStack, xStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  have hm := alloc_mem s xFr
  have hd : ∀ r' ∈ [(⟨s.sp - BitVec.ofNat 64 xFr, 8⟩ : Region)], Region.Disjoint ⟨s.gpr .r9, 48⟩ r' :=
    fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact (h11.sub_left hfr).symm
  refine ⟨e₀, hn, h1, ?_, h3, h4, h5, h6, h8, h9, h10, h11, h12, h13, h14, h15, ?_, ?_, h18⟩
  · show (⟨s.sp - BitVec.ofNat 64 xFr + 32, xFr - 32⟩ : Region) :: s.wr = _
    rw [h2, e₀, show (32 : Addr) = BitVec.ofNat 64 32 from rfl, Offset.add_add]; rfl
  · obtain ⟨t0, t1, t2⟩ := h16
    refine ⟨?_, ?_, ?_⟩
    · show (allocated xFr s).mem.readW (s.gpr .r9 + BitVec.ofNat 64 0) 64 = s.syms w.initN
      rw [hm.readW (r := ⟨s.gpr .r9, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact t0
    · show (allocated xFr s).mem.readW (s.gpr .r9 + BitVec.ofNat 64 8) 64 = s.syms w.H.updN
      rw [hm.readW (r := ⟨s.gpr .r9, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact t1
    · show (allocated xFr s).mem.readW (s.gpr .r9 + BitVec.ofNat 64 16) 64 = s.syms w.finN
      rw [hm.readW (r := ⟨s.gpr .r9, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact t2
  · show (allocated xFr s).mem.readW (s.gpr .r9 + BitVec.ofNat 64 40) 64 = _
    rw [hm.readW (r := ⟨s.gpr .r9, 48⟩) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)]; exact h17

end

/-! ## What every piece keeps -/

/-- The registers `XR` fixes. -/
abbrev kregs : List Reg := [.r14, .r15, .r16, .r17]

/-- The registers and memory kept from the end of the prologue on. -/
structure XR (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  r14 : t.gpr .r14 = ikm s₀
  r15 : t.gpr .r15 = s₀.gpr .r6
  r16 : t.gpr .r16 = prk s₀
  r17 : t.gpr .r17 = tab s₀
  cs : ∀ r ∈ preserved, r ∉ kregs → t.gpr r = s₀.gpr r
  saved : Spill.Saved (at_ L 144) s₀.gpr xSaved t.mem
  svlr : t.mem.readW (at_ L 176) 64 = s₀.lr
  frame : Frame (wrs w s₀ L) s₀.mem t.mem

theorem saved_fits : Spill.Fits xSaved := by decide

theorem saved_in : ∀ q ∈ xSaved, 32 ≤ q.2 ∧ q.2 + 8 ≤ 32 + 48 := by decide

/-- The save area: the return address and our caller's registers. -/
abbrev svR (L : Addr) : Region := ⟨at_ L 176, 48⟩

/-- A part of the stack apart from the save area, or of `prk`. -/
def Wk (w : HVar) (s₀ : State) (L : Addr) (r : Region) : Prop :=
  (Region.Sub r (stkR L) ∧ (svR L).Disjoint r) ∨ Region.Sub r (prkR w s₀)

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L)
include hp

omit hp in
theorem svR_sub : Region.Sub (svR L) (stkR L) := Offset.sub_base _ (by decide)

theorem Wk.ok {r : Region} (h : Wk w s₀ L r) : (svR L).Disjoint r ∧ ∃ r' ∈ wrs w s₀ L, Region.Sub r r' := by
  rcases h with ⟨h₁, h₂⟩ | h
  · exact ⟨h₂, _, by simp, h₁⟩
  · exact ⟨(hp.k_p.sub_left svR_sub).sub_right h, _, by simp, h⟩

theorem XR.keep {t t' : State} (h : XR w s₀ L t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk w s₀ L r) : XR w s₀ L t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide)).trans h.r14,
    (hg _ (by decide)).trans h.r15, (hg _ (by decide)).trans h.r16, (hg _ (by decide)).trans h.r17,
    fun r hr hk => (hg r hr).trans (h.cs r hr hk),
    h.saved.frame_in saved_in hf fun r hr => by
      rw [at_, Offset.add_add]; exact (Wk.ok hp (hw r hr)).1,
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Wk.ok hp (hw r hr)).1).sub_left
      (Region.sub_prefix (by decide))) (by decide)]; exact h.svlr,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem XR.same {t t' : State} (h : XR w s₀ L t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) : XR w s₀ L t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by decide)).trans h.r14,
    (hg _ (by decide)).trans h.r15, (hg _ (by decide)).trans h.r16, (hg _ (by decide)).trans h.r17,
    fun r hr hk => (hg r hr).trans (h.cs r hr hk), by rw [hm]; exact h.saved, by rw [hm]; exact h.svlr,
    by rw [hm]; exact h.frame⟩

omit hp in
theorem XR.only {t t' : State} (h : XR w s₀ L t) {rs : List Reg} (o : Only rs t t') (hsy : t'.syms = t.syms)
    (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : XR w s₀ L t' :=
  h.same o.rd o.wr o.sp hsy (keep_pres o.keep hrs) o.mem

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem XR.bytes {t : State} (hk : XR w s₀ L t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs w s₀ L, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem XR.saltB {t : State} (hk : XR w s₀ L t) :
    bytesAt t.mem (salt s₀) (saltLen s₀) = bytesAt s₀.mem (salt s₀) (saltLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_s.symm
    · exact hp.s_p) (Nat.le_of_lt (s₀.gpr .r4).isLt)

theorem XR.ikmB {t : State} (hk : XR w s₀ L t) :
    bytesAt t.mem (ikm s₀) (ikmLen s₀) = bytesAt s₀.mem (ikm s₀) (ikmLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_i.symm
    · exact hp.i_p) (Nat.le_of_lt (s₀.gpr .r6).isLt)

/-- A word of the table is as on entry. -/
theorem XR.tabW {t : State} (hk : XR w s₀ L t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tabR s₀) (Offset.contains_base _ ho (by omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.k_t.symm
      · exact hp.t_p) (by decide)

/-- The table's word at `o`, readable. -/
theorem tin {t : State} (hrd : t.rd = s₀.rd) {o : Nat} (ho : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
  ⟨tabR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp),
    Offset.contains_base _ ho (by omega_using [ho])⟩

/-- A part of the frame's local variable space is writable. -/
theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {d n : Nat} (h₁ : 176 ≤ d) (h₂ : d + n ≤ 2480) :
    InRegions t.wr (at_ L d) n := by
  rw [hwr, hp.wr]; exact in_at L _ h₁ (by omega_using [h₂]) (by decide)

theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {d n : Nat} (h₁ : 176 ≤ d) (h₂ : d + n ≤ 2480) :
    InRegions (t.rd ++ t.wr) (at_ L d) n :=
  let ⟨r, hr, hc⟩ := in_frw hp hwr h₁ h₂; ⟨r, List.mem_append_right _ hr, hc⟩

end

/-! ## The prologue -/

theorem pro_eq : extractPro = .mflr .r0 :: .addSp .r11 0 :: .store .d .r0 .r11 oLr :: (Spill.saveCode .r11 xSaved ++
    [mov .r14 .r5, mov .r15 .r6, mov .r16 .r7, mov .r17 .r9, mov .r5 .r3, mov .r6 .r4, .addSp .r3 xIn,
      .addSp .r4 xOut, .addSp .r7 xW]) := rfl

/-- After the prologue: `XR`, and `init`'s arguments. -/
def XA (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop :=
  XR w s₀ L t ∧ t.gpr .r3 = at_ L 224 ∧ t.gpr .r4 = at_ L 416 ∧ t.gpr .r5 = salt s₀ ∧
    t.gpr .r6 = s₀.gpr .r4 ∧ t.gpr .r7 = at_ L 608

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L)
include hp

theorem pro_ok : WP isa (.block extractPro) s₀ (XA w s₀ L) := by
  rw [pro_eq]
  refine WP.of_syms (wp_mflr fun s₁ o₁ e₁ => wp_addSp fun s₂ o₂ e₂ => ?_)
  obtain b₂ : s₂.gpr .r11 = at_ L 144 := by rw [e₂, o₁.sp, hp.sp, BitVec.add_zero]
  refine wp_std (a := at_ L 176) (by rw [b₂, show oLr = 32 from rfl, at_, Offset.add_add])
    (by rw [o₂.wr, o₁.wr, hp.wr]; exact in_head _ (by decide)) fun s₃ m₃ => ?_
  obtain b₃ : s₃.gpr .r11 = at_ L 144 := by rw [m₃.gpr, b₂]
  refine Spill.save_ok (b := .r11) (by decide) (by decide) (fun q hq => ?_) ?_
  · rw [b₃, m₃.wr, o₂.wr, o₁.wr, hp.wr, at_, Offset.add_add]
    have := saved_in q hq
    exact in_at L _ (by omega_using [this]) (by omega_using [this]) (by decide)
  refine wp_mov fun s₅ o₅ e₅ => wp_mov fun s₆ o₆ e₆ => wp_mov fun s₇ o₇ e₇ => wp_mov fun s₈ o₈ e₈ =>
    wp_mov fun s₉ o₉ e₉ => wp_mov fun s₁₀ o₁₀ e₁₀ => wp_addSp fun s₁₁ o₁₁ e₁₁ => wp_addSp fun s₁₂ o₁₂ e₁₂ =>
    wp_addSp fun s₁₃ o₁₃ e₁₃ => WP.block_nil fun sy => ?_
  -- The state after the saves.
  generalize hs₄ : ({ s₃ with mem := Spill.saveMem s₃.mem (s₃.gpr .r11) s₃.gpr xSaved } : State) = s₄ at *
  obtain K₄ : Keep [] s₃ s₄ := by subst hs₄; exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  obtain m₄ : s₄.mem = Spill.saveMem s₃.mem (at_ L 144) s₃.gpr xSaved := by subst hs₄; rw [b₃]
  have K : Keep [.r0, .r11, .r14, .r15, .r16, .r17, .r5, .r6, .r3, .r4, .r7] s₀ s₁₃ :=
    (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (K₄.trans (o₅.keep.trans (o₆.keep.trans (o₇.keep.trans
      (o₈.keep.trans (o₉.keep.trans (o₁₀.keep.trans (o₁₁.keep.trans (o₁₂.keep.trans o₁₃.keep)))))))))))).mono
  obtain m₁₃ : s₁₃.mem = s₄.mem := by
    rw [o₁₃.mem, o₁₂.mem, o₁₁.mem, o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem]
  obtain m₃' : s₃.mem = s₀.mem.writeW (at_ L 176) s₀.lr := by
    rw [m₃.mem, o₂.get .r0, e₁, o₂.mem, o₁.mem]
  obtain g₃ : ∀ r, r ∉ [Reg.r0, .r11] → s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [m₃.gpr, o₂.gpr r (fun h => hr (by simp at h; simp [h])), o₁.gpr r (fun h => hr (by simp at h; simp [h]))]
  -- The saves write only the slots.
  obtain F₄ : Frame [⟨at_ L 184, 32⟩] s₃.mem s₄.mem := by
    rw [m₄]
    have := Spill.saveMem_frame (lo := 40) (n := 32) (l := xSaved) (by decide) (by decide) s₃.mem (at_ L 144) s₃.gpr
    rwa [at_, Offset.add_add] at this
  have sp₁₃ : s₁₃.sp = s₀.sp := K.sp
  refine ⟨⟨K.rd, K.wr, sp₁₃, sy, ?_, ?_, ?_, ?_, fun r hr hk => K.gpr r ((by decide : ∀ r ∈ preserved,
      r ∉ kregs → r ∉ ([.r0, .r11, .r14, .r15, .r16, .r17, .r5, .r6, .r3, .r4, .r7] : List Reg)) r hr hk), ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (pupd_simp [o₁₃.gpr, e₁₃, o₁₂.gpr, e₁₂, o₁₁.gpr, e₁₁, o₁₀.gpr, e₁₀, o₉.gpr, e₉, o₈.gpr, e₈,
    o₇.gpr, e₇, o₆.gpr, e₆, o₅.gpr, e₅, K₄.gpr, m₃.gpr, o₂.gpr, o₁.gpr]; done)
  · -- The saved registers.
    intro q hq
    rw [m₁₃, m₄, Spill.saveMem_saved saved_fits s₃.mem (at_ L 144) s₃.gpr q hq]
    exact g₃ _ (by revert hq; revert q; decide)
  · -- The return address.
    rw [m₁₃, F₄.readW (r := ⟨at_ L 176, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by have := hp.nL; omega_using [this]))
      (by decide), m₃', Mem.readW_writeW_self64]
  · -- Memory changed only in the stack.
    rw [m₁₃]
    have f₃ : Frame (wrs w s₀ L) s₀.mem s₃.mem := by
      rw [m₃']
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
    exact f₃.trans (F₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stkR L, by simp, Offset.sub_base _ (by decide)⟩)
  · rw [o₁₃.get .r3, o₁₂.get .r3, e₁₁, o₁₀.sp, o₉.sp, o₈.sp, o₇.sp, o₆.sp, o₅.sp, K₄.sp, m₃.sp, o₂.sp, o₁.sp,
      hp.sp, at_, show xIn = 80 from rfl, Offset.add_add]
  · rw [o₁₃.get .r4, e₁₂, o₁₁.sp, o₁₀.sp, o₉.sp, o₈.sp, o₇.sp, o₆.sp, o₅.sp, K₄.sp, m₃.sp, o₂.sp, o₁.sp,
      hp.sp, at_, show xOut = 272 from rfl, Offset.add_add]
  · rw [e₁₃, o₁₂.sp, o₁₁.sp, o₁₀.sp, o₉.sp, o₈.sp, o₇.sp, o₆.sp, o₅.sp, K₄.sp, m₃.sp, o₂.sp, o₁.sp,
      hp.sp, at_, show xW = 464 from rfl, Offset.add_add]

end

/-! ## The calls -/

/-- The key `K₀` the salt makes. -/
abbrev k0Of (w : HVar) (s₀ : State) : List Byte := blockKey w.ok.SH.H (bytesAt s₀.mem (salt s₀) (saltLen s₀))

/-- The input keying material. -/
abbrev ikmOf (s₀ : State) : List Byte := bytesAt s₀.mem (ikm s₀) (ikmLen s₀)

/-- After `init`: the states of `K₀`. -/
def XI (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop :=
  XR w s₀ L t ∧ w.ok.SH.Repr t.mem (at_ L 224) (xorPad (k0Of w s₀) ipad) ∧
    w.ok.SH.Repr t.mem (at_ L 416) (xorPad (k0Of w s₀) opad)

/-- After `update`'s arguments. -/
def XUA (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop :=
  XI w s₀ L t ∧ t.gpr .r3 = at_ L 224 ∧ t.gpr .r4 = BitVec.ofNat 64 w.H.B ∧ t.gpr .r5 = ikm s₀ ∧
    t.gpr .r6 = s₀.gpr .r6 ∧ t.gpr .r7 = at_ L 608

/-- After `update`: the inner state holds the input keying material too. -/
def XU (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop :=
  XR w s₀ L t ∧ w.ok.SH.Repr t.mem (at_ L 224) (xorPad (k0Of w s₀) ipad ++ ikmOf s₀) ∧
    w.ok.SH.Repr t.mem (at_ L 416) (xorPad (k0Of w s₀) opad)

/-- After `finalize`'s arguments. -/
def XFA (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop :=
  XU w s₀ L t ∧ t.gpr .r3 = at_ L 224 ∧ t.gpr .r4 = at_ L 416 ∧
    t.gpr .r5 = BitVec.ofNat 64 w.H.B + s₀.gpr .r6 ∧ t.gpr .r6 = prk s₀ ∧ t.gpr .r7 = at_ L 608

/-- After `finalize`: `PRK`. -/
def XF (w : HVar) (s₀ : State) (L : Addr) (t : State) : Prop :=
  XR w s₀ L t ∧ bytesAt t.mem (prk s₀) w.H.D = hmacBlockKey w.ok.SH.H (k0Of w s₀) (ikmOf s₀)

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L)
include hp

/-- A part of the stack apart from the save area. -/
theorem wk_at {d n : Nat} (h₁ : 224 ≤ d ∨ d + n ≤ 176) (h₂ : d + n ≤ 2480) : Wk w s₀ L ⟨at_ L d, n⟩ :=
  .inl ⟨Offset.sub_base _ (by rw [xStack_eq]; exact h₂), Offset.disjoint _ (by omega_using [h₁])
    (by decide) (by have := hp.nL; rw [xStack_eq] at this; omega_using [this, h₂])⟩


omit hp in
/-- A region at `L + d` of `n` bytes, within the stack. -/
theorem st_sub {d n : Nat} (h : d + n ≤ 2480) : Region.Sub ⟨at_ L d, n⟩ (stkR L) :=
  Offset.sub_base _ (by rw [xStack_eq]; exact h)

/-- Two regions of the stack apart. -/
theorem st_dis {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (h₁ : d + n ≤ 2480) (h₂ : e + k ≤ 2480) :
    Region.Disjoint ⟨at_ L d, n⟩ ⟨at_ L e, k⟩ :=
  Offset.disjoint _ h (by have := hp.nL; rw [xStack_eq] at this; omega_using [this, h₁])
    (by have := hp.nL; rw [xStack_eq] at this; omega_using [this, h₂])

theorem st_nw {d n : Nat} (h : d + n ≤ 2480) (hd : d < 2480 := by decide) : (at_ L d).toNat + n ≤ 2 ^ 64 := by
  have := hp.nL; rw [xStack_eq] at this
  rw [at_, toNat_at (by omega_using [this, hd])]; omega_using [this, h]

/-- The stack pointer is above the stack the callees use. -/
theorem sp_ge {t : State} (ht : t.sp = s₀.sp) {n : Nat} (hn : n ≤ 144) : n ≤ t.sp.toNat := by
  have := hp.nL; rw [xStack_eq] at this
  rw [ht, hp.sp, at_, toNat_at (by omega_using [this])]; omega_using [hn]

omit hp in
/-- The frame's local variable space holds a region of it. -/
theorem fr_off {d n : Nat} (h₁ : 176 ≤ d) (h₂ : d + n ≤ 2480) :
    ∃ off, at_ L d = at_ L 176 + BitVec.ofNat 64 off ∧ off + n ≤ 2304 :=
  sub_at L h₁ (by omega_using [h₂])

/-- The stack below the stack pointer, from `L`. -/
theorem below_sp {t : State} (ht : t.sp = s₀.sp) {n : Nat} (hn : n ≤ 144) :
    below t.sp n = ⟨at_ L (144 - n), n⟩ := by
  rw [ht, hp.sp]; exact below_off L hn

/-- The loads of the table's functions' addresses. -/
theorem tload0 {t : State} (k : XR w s₀ L t) :
    WP isa (.block [.load .d .r12 .r17 (8 * 0)]) t fun u =>
      Only [.r12] t u ∧ u.gpr .r12 = s₀.syms w.initN ∧ u.syms = t.syms :=
  tload_ok (by decide) (by decide) k.r17 (tin hp k.rd (by decide)) (by rw [k.tabW hp (by decide)]; exact hp.tmem.1)

theorem tload1 {t : State} (k : XR w s₀ L t) :
    WP isa (.block [.load .d .r12 .r17 (8 * 1)]) t fun u =>
      Only [.r12] t u ∧ u.gpr .r12 = s₀.syms w.H.updN ∧ u.syms = t.syms :=
  tload_ok (by decide) (by decide) k.r17 (tin hp k.rd (by decide)) (by rw [k.tabW hp (by decide)]; exact hp.tmem.2.1)

theorem tload2 {t : State} (k : XR w s₀ L t) :
    WP isa (.block [.load .d .r12 .r17 (8 * 2)]) t fun u =>
      Only [.r12] t u ∧ u.gpr .r12 = s₀.syms w.finN ∧ u.syms = t.syms :=
  tload_ok (by decide) (by decide) k.r17 (tin hp k.rd (by decide)) (by rw [k.tabW hp (by decide)]; exact hp.tmem.2.2)

/-- What `init` needs, once the load of its address wrote `r12`. -/
theorem init_args (hw : HOk w) {t t' : State} (h : XA w s₀ L t) (o : Only [.r12] t t') :
    AnyArgs w t' (at_ L 224) (at_ L 416) (salt s₀) (at_ L 608) (saltLen s₀) := by
  obtain ⟨k, a3, a4, a5, a6, a7⟩ := h
  have hS := hw.hS
  have hA := hw.hA
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have bS := below_sp hp (o.sp.trans k.sp) (n := 144) (by decide)
  refine ⟨by rw [o.get .r3, a3], by rw [o.get .r4, a4], by rw [o.get .r5, a5], by rw [o.get .r6, a6],
    by rw [o.get .r7, a7], sp_ge hp (o.sp.trans k.sp) (by decide), st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hS]),
    (hp.k_s.sub_left (st_sub (by omega_using [hS]))), st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS])
      (by omega_using [hA, hW]),
    (hp.k_s.sub_left (st_sub (by omega_using [hS]))), st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS])
      (by omega_using [hA, hW]),
    (hp.k_s.sub_left (st_sub (by omega_using [hA, hW]))).symm, ?_, ?_, ?_, ?_,
    st_nw hp (by omega_using [hS]), st_nw hp (by omega_using [hS]), hp.ns, st_nw hp (by omega_using [hA, hW]), ?_, ?_⟩
  · rw [bS]; exact st_dis hp (.inl (by omega_using [hS])) (by decide) (by omega_using [hS])
  · rw [bS]; exact st_dis hp (.inl (by omega_using [hS])) (by decide) (by omega_using [hS])
  · rw [bS]; exact hp.k_s.sub_left (st_sub (by decide))
  · rw [bS]; exact st_dis hp (.inl (by omega_using [hA, hW])) (by decide) (by omega_using [hA, hW])
  · rw [o.rd, o.wr, k.rd, k.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, sub_at0 _ (Nat.le_refl _)⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hA, hW])⟩
  · rw [o.wr, k.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hA, hW])⟩

theorem init_call (hw : HOk w) {t t' : State} (h : XA w s₀ L t) (o : Only [.r12] t t') (sy : t'.syms = t.syms) :
    WP isa (.call w.initN w.initC) t' (XI w s₀ L) := by
  have hS := hw.hS
  have hA := hw.hA
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have k := h.1
  have bS := below_sp hp (o.sp.trans k.sp) (n := 144) (by decide)
  refine any_call (init_args hp hw h o) fun s' a hI hO => ?_
  have k' : XR w s₀ L s' := (k.only o sy).keep hp a.rd a.wr a.sp a.sy a.cs a.frame (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact wk_at hp (.inl (by decide)) (by omega_using [hS])
    · exact wk_at hp (.inl (by decide)) (by omega_using [hS])
    · exact wk_at hp (.inl (by decide)) (by omega_using [hA, hW])
    · rw [bS]; exact wk_at hp (.inr (by decide)) (by decide))
  have hs : bytesAt t'.mem (salt s₀) (saltLen s₀) = bytesAt s₀.mem (salt s₀) (saltLen s₀) := by
    rw [o.mem]; exact k.saltB hp
  rw [hs] at hI hO
  exact ⟨k', hI, hO⟩

theorem init_ok (hw : HOk w) {t : State} (h : XA w s₀ L t) : WP isa (tcall .r17 0 f.init) t (XI w s₀ L) := by
  have k := h.1
  unfold tcall
  refine WP.seq (WP.mono (tload0 hp k) fun t' ⟨o, e, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (init_call hp hw h o sy)
  show f.init.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, sy, k.sy]; exact hp.tok.i

theorem updArgs_ok {t : State} (h : XI w s₀ L t) : WP isa (.block extractUpd) t (XUA w s₀ L) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractUpd
  refine WP.of_syms (wp_addSp fun t₁ o₁ e₁ => wp_ld (a := tab s₀ + BitVec.ofNat 64 40)
    (by rw [o₁.get .r17, k.r17]) (tin hp (o₁.rd.trans k.rd) (by decide)) fun t₂ o₂ e₂ => ?_)
  refine wp_mov fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_addSp fun t₅ o₅ e₅ => WP.block_nil fun sy => ?_
  have K : Keep [.r3, .r4, .r5, .r6, .r7] t t₅ :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
  have m₅ : t₅.mem = t.mem := by rw [o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have k₅ : XR w s₀ L t₅ := k.same K.rd K.wr K.sp sy (keep_pres K) m₅
  refine ⟨⟨k₅, by rw [m₅]; exact hI, by rw [m₅]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, k.sp, hp.sp, at_, show xIn = 80 from rfl,
      Offset.add_add]
  · rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂, o₁.mem, k.tabW hp (by decide)]; exact hp.tB
  · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, k.r14]
  · rw [o₅.get .r6, e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, k.r15]
  · rw [e₅, o₄.sp, o₃.sp, o₂.sp, o₁.sp, k.sp, hp.sp, at_, show xW = 464 from rfl, Offset.add_add]

/-- The input keying material fits HMAC's count with a block of key. -/
theorem ikm_lt : w.H.B + ikmLen s₀ < 2 ^ 64 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hp.k_i.symm hp.ni (by have := hp.nL; exact this)
  have hB : w.H.B ≤ 128 := by rcases w.ok.dims.B with h | h <;> omega_using [h]
  have h' : ikmLen s₀ + xStack ≤ 2 ^ 64 := h
  rw [xStack_eq] at h'
  omega_using [h', hB]

/-- What `update` needs, once the load of its address wrote `r12`. -/
theorem upd_args (hw : HOk w) {t t' : State} (h : XUA w s₀ L t) (o : Only [.r12] t t') :
    UpdArgs w t' (at_ L 224) (ikm s₀) (at_ L 608) (ikmLen s₀) := by
  obtain ⟨⟨k, -, -⟩, a3, a4, a5, a6, a7⟩ := h
  have hS := hw.hS
  have hWw := hw.hW
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have bS := below_sp hp (o.sp.trans k.sp) (n := 48) (by decide)
  refine ⟨by rw [o.get .r3, a3], by rw [o.get .r5, a5], by rw [o.get .r6, a6], by rw [o.get .r7, a7],
    st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hWw, hW]),
    (hp.k_i.sub_left (st_sub (by omega_using [hS]))).symm, (hp.k_i.sub_left (st_sub (by omega_using [hWw, hW]))).symm,
    sp_ge hp (o.sp.trans k.sp) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [hS])
  · rw [bS]; exact hp.k_i.sub_left (st_sub (by decide))
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [hWw, hW])
  · rw [o.rd, o.wr, k.rd, k.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_at0 _ (Nat.le_refl _)⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hWw, hW])⟩
  · rw [o.wr, k.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hWw, hW])⟩

theorem absorb_call (hw : HOk w) {t t' : State} (h : XUA w s₀ L t) (o : Only [.r12] t t') (sy : t'.syms = t.syms) :
    WP isa (.call w.H.updN w.H.updC) t' (XU w s₀ L) := by
  have hh := h
  obtain ⟨⟨k, hI, hO⟩, a3, a4, a5, a6, a7⟩ := h
  have hS := hw.hS
  have hWw := hw.hW
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have bS := below_sp hp (o.sp.trans k.sp) (n := 48) (by decide)
  refine upd_call (upd_args hp hw hh o) fun s' a hu => ?_
  have k' : XR w s₀ L s' := (k.only o sy).keep hp a.rd a.wr a.sp a.sy a.cs a.frame (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact wk_at hp (.inl (by decide)) (by omega_using [hS])
    · exact wk_at hp (.inl (by decide)) (by omega_using [hWw, hW])
    · rw [bS]; exact wk_at hp (.inr (by decide)) (by decide))
  have fd : ∀ r ∈ ([⟨at_ L 224, w.H.S⟩, ⟨at_ L 608, w.H.W⟩] ++ [below t'.sp 48] : List Region),
      Region.Disjoint ⟨at_ L 416, w.H.S⟩ r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st_dis hp (.inr (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hS])
    · exact st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hWw, hW])
    · rw [bS]; exact st_dis hp (.inr (by decide)) (by omega_using [hS]) (by decide)
  have hm : t'.mem = t.mem := o.mem
  have hl : (xorPad (k0Of w s₀) ipad).length = w.H.B := by rw [xorPad_length, blockKey_length]
  refine ⟨k', ?_, ?_⟩
  · have := hu _ (by rw [hm]; exact hI) (by rw [o.get .r4, a4, hl])
    rwa [hm, k.ikmB hp] at this
  · exact w.ok.congr _ _ _ _ (fun i hi => a.frame.bytes (R := ⟨at_ L 416, w.H.S⟩) fd
      (by show w.H.S ≤ 2 ^ 64; omega_using [hS]) hi |>.trans (by rw [hm])) hO

theorem upd_ok (hw : HOk w) {t : State} (h : XUA w s₀ L t) : WP isa (tcall .r17 1 f.upd) t (XU w s₀ L) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload1 hp k) fun t' ⟨o, e, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (absorb_call hp hw h o sy)
  show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, sy, k.sy]; exact hp.tok.u

theorem finArgs_ok {t : State} (h : XU w s₀ L t) : WP isa (.block extractFin) t (XFA w s₀ L) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractFin
  refine WP.of_syms (wp_addSp fun t₁ o₁ e₁ => wp_addSp fun t₂ o₂ e₂ => ?_)
  refine wp_ld (a := tab s₀ + BitVec.ofNat 64 40) (by rw [o₂.get .r17, o₁.get .r17, k.r17])
    (tin hp (o₂.rd.trans (o₁.rd.trans k.rd)) (by decide)) fun t₃ o₃ e₃ => wp_add fun t₄ o₄ e₄ =>
    wp_mov fun t₅ o₅ e₅ => wp_addSp fun t₆ o₆ e₆ => WP.block_nil fun sy => ?_
  have K : Keep [.r3, .r4, .r5, .r5, .r6, .r7] t t₆ :=
    (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans o₆.keep))))).mono
  have m₆ : t₆.mem = t.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have k₆ : XR w s₀ L t₆ := k.same K.rd K.wr K.sp sy (keep_pres K) m₆
  refine ⟨⟨k₆, by rw [m₆]; exact hI, by rw [m₆]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₆.get .r3, o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, k.sp, hp.sp, at_, show xIn = 80 from rfl,
      Offset.add_add]
  · rw [o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂, o₁.sp, k.sp, hp.sp, at_, show xOut = 272 from rfl,
      Offset.add_add]
  · rw [o₆.get .r5, o₅.get .r5, e₄, e₃, o₃.get .r15, o₂.get .r15, o₁.get .r15, k.r15, o₂.mem, o₁.mem,
      k.tabW hp (by decide), hp.tB]
  · rw [o₆.get .r6, e₅, o₄.get .r16, o₃.get .r16, o₂.get .r16, o₁.get .r16, k.r16]
  · rw [e₆, o₅.sp, o₄.sp, o₃.sp, o₂.sp, o₁.sp, k.sp, hp.sp, at_, show xW = 464 from rfl, Offset.add_add]

/-- What `finalize` needs, once the load of its address wrote `r12`. -/
theorem fin_args (hw : HOk w) {t t' : State} (h : XFA w s₀ L t) (o : Only [.r12] t t') :
    FinArgs w t' (at_ L 224) (at_ L 416) (prk s₀) (at_ L 608) := by
  obtain ⟨⟨k, -, -⟩, a3, a4, a5, a6, a7⟩ := h
  have hS := hw.hS
  have hA := hw.hA
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have bS := below_sp hp (o.sp.trans k.sp) (n := 96) (by decide)
  refine ⟨by rw [o.get .r3, a3], by rw [o.get .r4, a4], by rw [o.get .r6, a6], by rw [o.get .r7, a7],
    st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hS]),
    hp.k_p.sub_left (st_sub (by omega_using [hS])),
    st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hA, hW]),
    hp.k_p.sub_left (st_sub (by omega_using [hS])),
    st_dis hp (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [hA, hW]),
    (hp.k_p.sub_left (st_sub (by omega_using [hA, hW]))).symm,
    sp_ge hp (o.sp.trans k.sp) (by decide), ?_, ?_, ?_, ?_,
    st_nw hp (by omega_using [hS]), st_nw hp (by omega_using [hS]), hp.np, st_nw hp (by omega_using [hA, hW]), ?_, ?_⟩
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [hS])
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [hS])
  · rw [bS]; exact hp.k_p.sub_left (st_sub (by decide))
  · rw [bS]; exact st_dis hp (.inl (by decide)) (by decide) (by omega_using [hA, hW])
  · rw [o.rd, o.wr, k.rd, k.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨prkR w s₀, by simp, sub_at0 _ (Nat.le_refl _)⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hA, hW])⟩
  · rw [o.wr, k.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hS])⟩
    · exact ⟨prkR w s₀, by simp, sub_at0 _ (Nat.le_refl _)⟩
    · exact ⟨⟨at_ L 176, 2304⟩, by simp, fr_off (by decide) (by dsimp only; omega_using [hA, hW])⟩

theorem fin_call' (hw : HOk w) {t t' : State} (h : XFA w s₀ L t) (o : Only [.r12] t t') (sy : t'.syms = t.syms) :
    WP isa (.call w.finN w.H.finalize) t' (XF w s₀ L) := by
  have hh := h
  obtain ⟨⟨k, hI, hO⟩, a3, a4, a5, a6, a7⟩ := h
  have hS := hw.hS
  have hA := hw.hA
  have hW : Impl.Hkdf.PPC64LE.work = 1872 := rfl
  have bS := below_sp hp (o.sp.trans k.sp) (n := 96) (by decide)
  refine fin_call (fin_args hp hw hh o) fun s' a hf => ?_
  have k' : XR w s₀ L s' := (k.only o sy).keep hp a.rd a.wr a.sp a.sy a.cs a.frame (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact wk_at hp (.inl (by decide)) (by omega_using [hS])
    · exact .inr (fun _ h => h)
    · exact wk_at hp (.inl (by decide)) (by omega_using [hA, hW])
    · rw [bS]; exact wk_at hp (.inr (by decide)) (by decide))
  have hm : t'.mem = t.mem := o.mem
  have hl : (k0Of w s₀).length = w.H.B := blockKey_length w _
  have hc : t'.gpr .r5 = BitVec.ofNat 64 (w.H.B + (ikmOf s₀).length) := by
    rw [o.get .r5, a5, bytesAt_length]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := ikm_lt hp; have hB : w.H.B < 2 ^ 64 := by omega_using [this]
    rw [Nat.mod_eq_of_lt hB]
  exact ⟨k', hf _ _ hl (by rw [hl, bytesAt_length]; exact ikm_lt hp) (by rw [hm]; exact hI) hc (by rw [hm]; exact hO)⟩

theorem fin_ok (hw : HOk w) {t : State} (h : XFA w s₀ L t) : WP isa (tcall .r17 2 f.fin) t (XF w s₀ L) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload2 hp k) fun t' ⟨o, e, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .r12) rfl ?_ (fin_call' hp hw h o sy)
  show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .r12) = _
  rw [e, sy, k.sy]; exact hp.tok.f

/-- The epilogue: the return address and our caller's registers restored. -/
theorem epi_ok {t : State} (k : XR w s₀ L t) :
    WP isa (.block extractEpi) t fun v => (∀ r ∈ preserved, v.gpr r = s₀.gpr r) ∧ v.sp = s₀.sp ∧
      v.lr = s₀.lr ∧ v.mem = t.mem := by
  unfold extractEpi restoreLr
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun t₁ o₁ e₁ => ?_
  have b₁ : t₁.gpr .r11 = at_ L 144 := by rw [e₁, k.sp, hp.sp, BitVec.add_zero]
  refine wp_ld (a := at_ L 176) (by rw [b₁, show oLr = 32 from rfl, at_, Offset.add_add])
    (in_fr hp (by rw [o₁.wr, k.wr]) (by decide) (by decide))
    fun t₂ o₂ e₂ => wp_mtlr fun t₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  have b₃ : t₃.gpr .r11 = at_ L 144 := by rw [g₃, o₂.get .r11, b₁]
  refine WP.mono (Spill.restore_wp (b := .r11) (l := xSaved) (by decide) b₃ (by decide) (by decide)
    (fun q hq => by
      rw [at_, Offset.add_add]
      have := saved_in q hq
      exact in_fr hp (by rw [wr₃, o₂.wr, o₁.wr, k.wr]) (by omega_using [this]) (by omega_using [this]))
    (by rw [m₃, o₂.mem, o₁.mem]; exact k.saved)) fun v hr => ⟨fun r hr' => ?_, by rw [hr.sp, sp₃, o₂.sp, o₁.sp, k.sp],
      by rw [hr.lr, lr₃, e₂, o₁.mem, k.svlr], by rw [hr.mem, m₃, o₂.mem, o₁.mem]⟩
  refine hr.gpr_of ?_
  by_cases hk : r ∈ kregs
  · exact .inl (by revert hk; revert r; decide)
  · refine .inr ?_
    have n0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr' (by decide)
    have n11 : r ∉ [Reg.r11] := fun e => by simp only [List.mem_singleton] at e; subst e; exact absurd hr' (by decide)
    rw [g₃, o₂.gpr r n0, o₁.gpr r n11, k.cs r hr' hk]

end

section
variable {w : HVar} {f : Fns} {s₀ : State} {L : Addr} (hp : Pre w f s₀ L)
include hp

/-- The frame's body: our caller's registers and return address restored, and `PRK`. -/
theorem main_ok (hw : HOk w) : WP isa (extractMain f) s₀ fun u => (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧
      u.sp = s₀.sp ∧ u.lr = s₀.lr ∧
      bytesAt u.mem (prk s₀) w.H.D = hmacBlockKey w.ok.SH.H (k0Of w s₀) (ikmOf s₀) := by
  unfold extractMain
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => WP.seq (WP.mono (init_ok hp hw h₁) fun t₂ h₂ =>
    WP.seq (WP.mono (updArgs_ok hp h₂) fun t₃ h₃ => WP.seq (WP.mono (upd_ok hp hw h₃) fun t₄ h₄ =>
    WP.seq (WP.mono (finArgs_ok hp h₄) fun t₅ h₅ => WP.seq (WP.mono (fin_ok hp hw h₅) fun t₆ ⟨k₆, hP⟩ =>
      WP.mono (epi_ok hp k₆) fun u ⟨hcs, hsp, hlr, hm⟩ => ⟨hcs, hsp, hlr, by rw [hm]; exact hP⟩))))))

end

/-- `vg_hkdf_extract`, in its frame. -/
theorem extract_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (extractR w f ns xStack).pre s) :
    WP isa (extract f) s fun s' => abiPreserved s s' ∧ (extractR w f ns xStack).post s s' := by
  have hsp : xStack ≤ s.sp.toNat := hp.2.2.2.2.2.2.1
  obtain p := pre_alloc hp
  obtain ⟨e₀, -, -⟩ := alloc_at s (F := xFr) (C := 144) hsp
  unfold extract
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by rw [xStack_eq] at hsp; rw [xFr_eq]; omega_using [hsp])
    (WP.mono (main_ok p hw) fun v ⟨hcs, hvsp, hlr, hP⟩ m un fl => ?_)
  refine ⟨free_abi hcs hvsp hlr m un, ?_⟩
  -- The `free` loses the frame's bytes, which lie apart from `prk`.
  have hfs : Region.Sub ⟨s.sp - BitVec.ofNat 64 xFr, xFr⟩ ⟨s.sp - BitVec.ofNat 64 xStack, xStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  have hfs8 : Region.Sub ⟨s.sp - BitVec.ofNat 64 xFr, 8⟩ ⟨s.sp - BitVec.ofNat 64 xStack, xStack⟩ := by
    rw [e₀]; exact Offset.sub_base _ (by decide)
  obtain e : bytesAt m (s.gpr .r7) w.H.D = bytesAt v.mem (s.gpr .r7) w.H.D :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => lost_byte fl (R := prkR w (allocated xFr s))
      (p.k_p.sub_left hfs).symm hi
  have hs : bytesAt (allocated xFr s).mem ((allocated xFr s).gpr .r3) ((allocated xFr s).gpr .r4).toNat =
      bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat :=
    bytes_keep (R := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩) (alloc_mem s xFr) (p.k_s.sub_left hfs8).symm
      (Nat.le_of_lt (s.gpr .r4).isLt)
  have hi : bytesAt (allocated xFr s).mem ((allocated xFr s).gpr .r5) ((allocated xFr s).gpr .r6).toNat =
      bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    bytes_keep (R := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩) (alloc_mem s xFr) (p.k_i.sub_left hfs8).symm
      (Nat.le_of_lt (s.gpr .r6).isLt)
  show bytesAt m (s.gpr .r7) w.H.D = Spec.Hmac.hmac _ _ _
  rw [e]
  have hP' := hP
  simp only [k0Of, ikmOf, salt, saltLen, ikm, ikmLen] at hP'
  rw [hs, hi] at hP'
  exact hP'

/-! ## Constant time -/

/-- The registers `XR` fixes, which hold pointers and lengths. -/
abbrev pubRegs : List Reg := [.r14, .r15, .r16, .r17]

/-- The taint checks of the pieces of `vg_hkdf_extract` between the calls. -/
structure XChecks : Prop where
  pro : Ck [.r3, .r4, .r5, .r6, .r7, .r8, .r9] (.block extractPro)
  tl0 : Ck [.r17] (.block [.load .d .r12 .r17 (8 * 0)])
  tl1 : Ck [.r17] (.block [.load .d .r12 .r17 (8 * 1)])
  tl2 : Ck [.r17] (.block [.load .d .r12 .r17 (8 * 2)])
  ua : Ck pubRegs (.block extractUpd)
  fa : Ck pubRegs (.block extractFin)
  epi : Ck [] (.block extractEpi)

theorem xchecks : XChecks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : HVar) (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  regs : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9], s₀.gpr r = s₀'.gpr r
  hi : s₀.syms w.initN = s₀'.syms w.initN
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.finN = s₀'.syms w.finN

section
variable {w : HVar} {f : Fns} {s₀ s₀' : State} {L : Addr} (hp : Pre w f s₀ L) (hp' : Pre w f s₀' L)
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
theorem ag {t t' : State} (k : XR w s₀ L t) (k' : XR w s₀' L t') :
    t.sp = t'.sp ∧ ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  refine ⟨by rw [k.sp, k'.sp, hq.sp], fun r hr => ?_⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [k.r14, k'.r14]; exact hq.regs .r5 (by simp)
  · rw [k.r15, k'.r15]; exact hq.regs .r6 (by simp)
  · rw [k.r16, k'.r16]; exact hq.regs .r7 (by simp)
  · rw [k.r17, k'.r17]; exact hq.regs .r9 (by simp)

omit hp hp' in
theorem ag17 {t t' : State} (k : XR w s₀ L t) (k' : XR w s₀' L t') :
    t.sp = t'.sp ∧ ∀ r ∈ [Reg.r17], t.gpr r = t'.gpr r :=
  ⟨(ag hq k k').1, fun r hr => (ag hq k k').2 r (by simp at hr; subst hr; simp)⟩

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel (hw : HOk w) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (extractMain f) fun _ _ => True := by
  have kc := xchecks
  have e3 := hq.regs .r3 (by simp); have e4 := hq.regs .r4 (by simp); have e5 := hq.regs .r5 (by simp)
  have e6 := hq.regs .r6 (by simp); have e7 := hq.regs .r7 (by simp)
  unfold extractMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := XA w s₀ L) (G₂ := XA w s₀' L)
    (rs := [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (fun s s' hs hs' => by
      subst hs hs'; exact ⟨hq.sp, hq.regs⟩) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => XA w s₀ L t ∧ XA w s₀' L t') (tcall .r17 0 f.init)
      fun t t' => XI w s₀ L t ∧ XI w s₀' L t' :=
    rel_wp (tcall_rel (rs := [.r17]) (a := s₀.syms w.initN) kc.tl0 (fun t t' k k' => ag17 hq k.1 k'.1)
      (fun t k => tload0 hp k.1) (fun t k => by rw [hq.hi]; exact tload0 hp' k.1)
      (fun t k => by rw [k.1.sy]; exact hp.tok.i) (fun t k => by rw [k.1.sy, hq.hi]; exact hp'.tok.i)
      (any_rel fun u u' ⟨⟨t, k, o, _, _⟩, ⟨t', k', o', _, _⟩⟩ => ⟨init_args hp hw k o,
        by have := init_args hp' hw k' o'; simp only [salt, saltLen] at this ⊢; rwa [← e3, ← e4] at this,
        by rw [o.sp, o'.sp, k.1.sp, k'.1.sp, hq.sp]⟩))
      (fun t k => init_ok hp hw k) (fun t k => init_ok hp' hw k)
  have r3 := rel_agree (P₁ := XI w s₀ L) (P₂ := XI w s₀' L) (G₁ := XUA w s₀ L) (G₂ := XUA w s₀' L) (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.ua (fun t k => updArgs_ok hp k) (fun t k => updArgs_ok hp' k)
  have r4 : RelCT isa (fun t t' => XUA w s₀ L t ∧ XUA w s₀' L t') (tcall .r17 1 f.upd)
      fun t t' => XU w s₀ L t ∧ XU w s₀' L t' :=
    rel_wp (tcall_rel (rs := [.r17]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' k k' => ag17 hq k.1.1 k'.1.1)
      (fun t k => tload1 hp k.1.1) (fun t k => by rw [hq.up]; exact tload1 hp' k.1.1)
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.u) (fun t k => by rw [k.1.1.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, k, o, _, _⟩, ⟨t', k', o', _, _⟩⟩ => ⟨upd_args hp hw k o,
        by have := upd_args hp' hw k' o'; simp only [ikm, ikmLen] at this ⊢; rwa [← e5, ← e6] at this,
        by rw [o.sp, o'.sp, k.1.1.sp, k'.1.1.sp, hq.sp],
        by rw [o.get .r4, o'.get .r4, k.2.2.1, k'.2.2.1]⟩))
      (fun t k => upd_ok hp hw k) (fun t k => upd_ok hp' hw k)
  have r5 := rel_agree (P₁ := XU w s₀ L) (P₂ := XU w s₀' L) (G₁ := XFA w s₀ L) (G₂ := XFA w s₀' L) (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.fa (fun t k => finArgs_ok hp k) (fun t k => finArgs_ok hp' k)
  have r6 : RelCT isa (fun t t' => XFA w s₀ L t ∧ XFA w s₀' L t') (tcall .r17 2 f.fin)
      fun t t' => XF w s₀ L t ∧ XF w s₀' L t' :=
    rel_wp (tcall_rel (rs := [.r17]) (a := s₀.syms w.finN) kc.tl2 (fun t t' k k' => ag17 hq k.1.1 k'.1.1)
      (fun t k => tload2 hp k.1.1) (fun t k => by rw [hq.hf]; exact tload2 hp' k.1.1)
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.f) (fun t k => by rw [k.1.1.sy, hq.hf]; exact hp'.tok.f)
      (fin_rel fun u u' ⟨⟨t, k, o, _, _⟩, ⟨t', k', o', _, _⟩⟩ => ⟨fin_args hp hw k o,
        by have := fin_args hp' hw k' o'; simp only [prk] at this ⊢; rwa [← e7] at this,
        by rw [o.sp, o'.sp, k.1.1.sp, k'.1.1.sp, hq.sp],
        by rw [o.get .r5, o'.get .r5, k.2.2.2.1, k'.2.2.2.1, e6]⟩))
      (fun t k => fin_ok hp hw k) (fun t k => fin_ok hp' hw k)
  have r7 := rel_agree (P₁ := XF w s₀ L) (P₂ := XF w s₀' L) (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [])
    (fun t t' k k' => ⟨by rw [k.1.sp, k'.1.sp, hq.sp], fun _ h => absurd h List.not_mem_nil⟩) kc.epi
    (fun t k => WP.mono (epi_ok hp k.1) fun _ _ => trivial) (fun t k => WP.mono (epi_ok hp' k.1) fun _ _ => trivial)
  exact ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ _ => trivial)

end

/-- `vg_hkdf_extract` is constant time: two runs whose public data agree
leak the same trace. -/
theorem extract_ct {w : HVar} {f : Fns} {ns : List String} (hw : HOk w)
    (hns : ∀ n ∈ [w.initN, w.H.updN, w.finN], n ∈ ns) :
    ConstantTime isa (extractR w f ns xStack).pre (extractR w f ns xStack).pub (extract f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, qn⟩ := hpub
  rw [← qsp] at hp'
  have hq : PubEq w (allocated xFr e) (allocated xFr e') :=
    ⟨by simp only [allocated, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q3, q4, q5, q6, q7, q8, q9], qn _ (hns _ (by simp)), qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (extract f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold extract
  refine RelCT.alloc (fun x y ⟨hx, hy⟩ => by rw [hx, hy, qsp]) ((main_rel hp hp' hq hw).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.PPC64LE.Extract
