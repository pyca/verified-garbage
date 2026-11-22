module

public import VerifiedGarbage.Proof.Hkdf.AArch64.Key
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.Hkdf.AArch64

/-!
# HKDF on AArch64: `vg_hkdf_extract`, correct and constant time

The contract the proof is written against (`extractR`), for the table `hmac`
of one variant `w` (`MdHash`), whose functions an indirect call of `f`'s
reaches: `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)` writes
`HKDF-Extract(salt, IKM)` (`D` bytes) to `prk`.

As on x86-64 (`Proof/Hkdf/X86_64/Extract.lean`): the return address pushed
and the frame (`xFr` bytes: the save area, HMAC's inner and outer states,
then the working space) allocated (`pre_entered`, from which on `Pre`
holds), the prologue saves our caller's `x19`–`x22` and keeps the arguments
it needs after the calls in them (`pro_ok`, from which on `XR` holds); then
`init` with the salt as the key, `update` with the input keying material
and `finalize` into `prk`, each through the table (`init_ok`, `upd_ok`,
`fin_ok`); and the epilogue restores our caller's registers (`epi_ok`). The
pop restores `x30` from the push's slot, which nothing in the frame's body
writes (`main_ok`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.AArch64.Extract

open VG VG.AArch64 VG.AArch64.Steps
open VG.Impl.Hkdf.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (TabOK TabMem)
open VG.Proof.Hkdf.AArch64 (HOk StackAt base stackAt entered toNat_addN repr_keep Ck rel_agree)

/-- `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`, with `N`
bytes of stack, for the table `hmac` of `w`, whose functions an indirect
call of `f`'s reaches, with the addresses of the functions `ns` public. -/
def extractR (w : MdHash) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let salt : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ikm : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let prk : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let tab : Region := ⟨s.gpr .x6, 48⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 N, N⟩
    N ≤ s.sp.toNat ∧ s.rd = [salt, ikm, tab] ∧ s.wr = [prk] ∧
      salt.Disjoint prk ∧ ikm.Disjoint prk ∧ prk.Disjoint tab ∧
      stk.Disjoint salt ∧ stk.Disjoint ikm ∧ stk.Disjoint prk ∧ stk.Disjoint tab ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat = w.H.D ∧ TabMem w.H s.syms (s.gpr .x6) s.mem ∧
      s.mem.readW (s.gpr .x6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B ∧ TabOK w.H f s.syms
  post s s' := Spec.Sha256.bytesAt s'.mem (s.gpr .x4) w.H.D =
    Spec.Hkdf.extract w.ok.SH.H (Spec.Sha256.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (Spec.Sha256.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_extract` uses: the return address, its frame, and the
16 bytes below it that the calls use. -/
def xStack : Nat := xFr + 32

theorem xFr_eq : xFr = 3824 := rfl
theorem xStack_eq : xStack = 3856 := rfl

theorem xstk_eq (s : State) : s.sp - BitVec.ofNat 64 xStack = base s xFr := rfl

theorem xIn_eq : xIn = 32 := rfl
theorem xOut_eq : xOut = 224 := rfl
theorem xWork_eq : xWork = 416 := rfl
theorem work_eq : work = 3408 := rfl

/-! ## Where things are -/

section
variable (s₀ : State)

/-- An address in the frame, of the state on entry to the frame's body. -/
abbrev sA (o : Nat) : Addr := s₀.sp + BitVec.ofNat 64 o

/-- The arguments, on entry to the frame's body. -/
abbrev salt : Addr := s₀.gpr .x0
abbrev saltLen : Nat := (s₀.gpr .x1).toNat
abbrev ikm : Addr := s₀.gpr .x2
abbrev ikmLen : Nat := (s₀.gpr .x3).toNat
abbrev prk : Addr := s₀.gpr .x4
abbrev tab : Addr := s₀.gpr .x6

abbrev frR : Region := ⟨s₀.sp, xFr⟩
abbrev saltR : Region := ⟨salt s₀, saltLen s₀⟩
abbrev ikmR : Region := ⟨ikm s₀, ikmLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩
/-- The return address pushed, just above the frame. -/
abbrev pushR : Region := ⟨sA s₀ xFr, 16⟩
/-- The 16 bytes below the frame that the calls use. -/
abbrev stk : Region := below s₀.sp 16

end

/-- The regions the frame's body writes. -/
abbrev prkR (w : MdHash) (s₀ : State) : Region := ⟨prk s₀, w.H.D⟩
abbrev wrs (w : MdHash) (s₀ : State) : List Region := [frR s₀, prkR w s₀, stk s₀]

/-- The state the frame's body starts in. -/
structure Pre (w : MdHash) (f : Fns) (s₀ : State) : Prop where
  hw : HOk w
  rd : s₀.rd = [saltR s₀, ikmR s₀, tabR s₀]
  wr : s₀.wr = [frR s₀, pushR s₀, prkR w s₀]
  pl : (s₀.gpr .x5).toNat = w.H.D
  s_p : (saltR s₀).Disjoint (prkR w s₀)
  i_p : (ikmR s₀).Disjoint (prkR w s₀)
  p_t : (prkR w s₀).Disjoint (tabR s₀)
  r_p : (pushR s₀).Disjoint (prkR w s₀)
  f_s : (frR s₀).Disjoint (saltR s₀)
  f_i : (frR s₀).Disjoint (ikmR s₀)
  f_p : (frR s₀).Disjoint (prkR w s₀)
  f_t : (frR s₀).Disjoint (tabR s₀)
  b_s : (stk s₀).Disjoint (saltR s₀)
  b_i : (stk s₀).Disjoint (ikmR s₀)
  b_p : (stk s₀).Disjoint (prkR w s₀)
  b_t : (stk s₀).Disjoint (tabR s₀)
  sp : 16 ≤ s₀.sp.toNat
  top : s₀.sp.toNat + xFr + 16 ≤ 2 ^ 64
  ns : (salt s₀).toNat + saltLen s₀ ≤ 2 ^ 64
  ni : (ikm s₀).toNat + ikmLen s₀ ≤ 2 ^ 64
  np : (prk s₀).toNat + w.H.D ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  tmem : TabMem w.H s₀.syms (tab s₀) s₀.mem
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B
  tok : TabOK w.H f s₀.syms

/-- The return address's slot, above the frame. -/
theorem push_eq (s : State) : sA (entered xFr s) xFr = s.sp - 16 := BitVec.sub_add_cancel _ _

/-- The push writes only its 16 bytes. -/
theorem entered_frame (s : State) : Frame [⟨s.sp - 16, 16⟩] s.mem (entered xFr s).mem :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)

/-- Bytes apart from the return address's slot are those on entry. -/
theorem entered_bytes {s : State} {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨p, n⟩ ⟨s.sp - 16, 16⟩)
    (hn : n ≤ 2 ^ 64) : Spec.Sha256.bytesAt (entered xFr s).mem p n = Spec.Sha256.bytesAt s.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => (entered_frame s).bytes (R := ⟨p, n⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) hn hi

section
variable {w : MdHash} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_entered {s : State} (hw : HOk w) (hp : (extractR w f ns xStack).pre s) : Pre w f (entered xFr s) := by
  have hS := stackAt s xFr hp.1
  obtain ⟨-, hrd, hwr, sp', ip, pt, ks, ki, kp, kt, ns', ni, np, nt, hpl, tm, tb, tok⟩ := hp
  have hxs : xStack = xFr + 32 := rfl
  have hnw := hS.nw
  rw [xstk_eq] at ks ki kp kt
  rw [hpl] at sp' ip pt kp np
  have hsp0 : (entered xFr s).sp = base s xFr + BitVec.ofNat 64 16 := hS.frame
  obtain subF : Region.Sub (frR (entered xFr s)) ⟨base s xFr, xStack⟩ := by
    show Region.Sub ⟨(entered xFr s).sp, xFr⟩ _
    rw [hsp0]; exact Offset.sub_base _ (by omega_using [hxs])
  obtain subB : Region.Sub (stk (entered xFr s)) ⟨base s xFr, xStack⟩ := by
    show Region.Sub ⟨(entered xFr s).sp - BitVec.ofNat 64 16, 16⟩ _
    rw [hsp0, BitVec.add_sub_cancel]; exact Region.sub_prefix (by omega_using [hxs])
  obtain subP : Region.Sub (pushR (entered xFr s)) ⟨base s xFr, xStack⟩ := by
    show Region.Sub ⟨(entered xFr s).sp + BitVec.ofNat 64 xFr, 16⟩ _
    rw [hsp0, Offset.add_add]; exact Offset.sub_base _ (by omega_using [hxs])
  obtain subQ : Region.Sub ⟨s.sp - 16, 16⟩ ⟨base s xFr, xStack⟩ := by
    rw [← push_eq]; exact subP
  have htw : ∀ o, o + 8 ≤ 48 → (entered xFr s).mem.readW (s.gpr .x6 + BitVec.ofNat 64 o) 64 =
      s.mem.readW (s.gpr .x6 + BitVec.ofNat 64 o) 64 := fun o ho =>
    (entered_frame s).readW (r := ⟨s.gpr .x6, 48⟩) (Offset.contains_base _ ho (by omega_using [ho]))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kt.symm.sub_right subQ) (by decide)
  obtain hspN : (entered xFr s).sp.toNat = (base s xFr).toNat + 16 := by
    rw [hsp0, toNat_addN (by omega_using [hnw])]
  refine ⟨hw, hrd, ?_, hpl, sp', ip, pt, kp.sub_left subP, ks.sub_left subF, ki.sub_left subF, kp.sub_left subF,
    kt.sub_left subF, ks.sub_left subB, ki.sub_left subB, kp.sub_left subB, kt.sub_left subB, ?_, ?_, ns', ni,
    np, nt, ⟨(htw 0 (by decide)).trans tm.1, (htw 8 (by decide)).trans tm.2.1, (htw 16 (by decide)).trans tm.2.2⟩,
    (htw 40 (by decide)).trans tb, tok⟩
  · show (⟨(entered xFr s).sp, xFr⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
    rw [hwr, hpl, ← push_eq]; rfl
  · rw [hspN]; omega_using []
  · rw [hspN]; omega_using [hnw]

end

/-! ## What every piece keeps -/

/-- Our caller's registers the functions we call keep and we do not save. -/
abbrev kept : List Reg := [.x23, .x24, .x25, .x26, .x27, .x28]

/-- The registers `XR` fixes. -/
abbrev xRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

theorem xRegs_pres : ∀ r ∈ xRegs, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem kept_x : ∀ r ∈ kept, r ∈ xRegs := by decide
theorem kept_ne9 : ∀ r ∈ kept, r ≠ .x9 := by decide
theorem pres_split : ∀ r ∈ preserved, r ≠ .x30 → r ∈ xSaved.map Prod.fst ∨ r ∈ kept := by decide

theorem xSaved_fits : Spill.Fits xSaved := by decide
theorem xSaved_ok : ∀ p ∈ xSaved, p.2 % 8 = 0 ∧ p.2 < 32768 := xSaved_fits.1
theorem xSaved_in : ∀ q ∈ xSaved, q.2 + 8 ≤ 32 := by decide
theorem xSaved_ne9 : ∀ q ∈ xSaved, q.1 ≠ .x9 := by decide

/-- The registers and memory kept from the end of the prologue on. -/
structure XR (w : MdHash) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sy : t.syms = s₀.syms
  sp : t.sp = s₀.sp
  x19 : t.gpr .x19 = ikm s₀
  x20 : t.gpr .x20 = s₀.gpr .x3
  x21 : t.gpr .x21 = prk s₀
  x22 : t.gpr .x22 = tab s₀
  cs : ∀ r ∈ kept, t.gpr r = s₀.gpr r
  saved : Spill.Saved s₀.sp s₀.gpr xSaved t.mem
  frame : Frame (wrs w s₀) s₀.mem t.mem

/-- A part of the frame after the save area, or `prk`. -/
def Wk (w : MdHash) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 32 ≤ o ∧ o + n ≤ xFr) ∨ Region.Sub r (prkR w s₀)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem Wk.ok {r : Region} (h : Wk w s₀ r) :
    (∀ q ∈ xSaved, Region.Disjoint ⟨s₀.sp + BitVec.ofNat 64 q.2, 8⟩ r) ∧ ∃ r' ∈ wrs w s₀, Region.Sub r r' := by
  have hfr := xFr_eq
  have sv : ∀ q ∈ xSaved, Region.Sub ⟨s₀.sp + BitVec.ofNat 64 q.2, 8⟩ (frR s₀) := fun q hq =>
    Offset.sub_base _ (by have := xSaved_in q hq; omega_using [hfr, this])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h
  · refine ⟨fun q hq => Offset.disjoint _ (.inl (by have := xSaved_in q hq; omega_using [h₁, this]))
      (by have := xSaved_in q hq; omega_using [this]) (by omega_using [h₂, hfr]), _, by simp, Offset.sub_base _ h₂⟩
  · exact ⟨fun q hq => (hp.f_p.sub_left (sv q hq)).sub_right h, _, by simp, h⟩

omit hp in
theorem XR.upd {t t' : State} (h : XR w s₀ t) {d : Reg} (hd : d ∉ xRegs) {v : BitVec 64}
    (u : Upd t t' d v) : XR w s₀ t' := by
  have g : ∀ r ∈ xRegs, t'.gpr r = t.gpr r := fun r hr => u.other r fun e => hd (e ▸ hr)
  exact ⟨u.rd.trans h.rd, u.wr.trans h.wr, u.syms.trans h.sy, u.sp.trans h.sp, (g _ (by decide)).trans h.x19,
    (g _ (by decide)).trans h.x20, (g _ (by decide)).trans h.x21, (g _ (by decide)).trans h.x22,
    fun r hr => (g r (kept_x r hr)).trans (h.cs r hr), by rw [u.mem]; exact h.saved, by rw [u.mem]; exact h.frame⟩

/-- What a call leaves keeps `XR`, if it writes only parts of the frame after
the save area, `prk`, and the 16 bytes below the frame. -/
theorem XR.after {t t' : State} (h : XR w s₀ t) {ws : List Region}
    (ha : Proof.Pbkdf2.Md.AArch64.Calls.After t ws t') (hw : ∀ r ∈ ws, Wk w s₀ r) : XR w s₀ t' := by
  have g : ∀ r ∈ xRegs, t'.gpr r = t.gpr r := fun r hr => ha.cs r (xRegs_pres r hr).1 (xRegs_pres r hr).2
  have hf := ha.frame
  rw [h.sp] at hf
  have hok : ∀ r ∈ ws ++ [stk s₀], (∀ q ∈ xSaved, Region.Disjoint ⟨s₀.sp + BitVec.ofNat 64 q.2, 8⟩ r) ∧
      ∃ r' ∈ wrs w s₀, Region.Sub r r' := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact Wk.ok hp (hw r hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fun q hq => Offset.disjoint_below _ (by have := xSaved_in q hq; omega_using [this]), _, by simp,
        fun _ h => h⟩
  exact ⟨ha.rd.trans h.rd, ha.wr.trans h.wr, ha.syms.trans h.sy, ha.sp.trans h.sp, (g _ (by decide)).trans h.x19,
    (g _ (by decide)).trans h.x20, (g _ (by decide)).trans h.x21, (g _ (by decide)).trans h.x22,
    fun r hr => (g r (kept_x r hr)).trans (h.cs r hr), h.saved.frame hf fun q hq r hr => (hok r hr).1 q hq,
    h.frame.trans (hf.sub fun r hr => (hok r hr).2)⟩

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem XR.bytes {t : State} (hk : XR w s₀ t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs w s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt t.mem p n = Spec.Sha256.bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem XR.saltB {t : State} (hk : XR w s₀ t) :
    Spec.Sha256.bytesAt t.mem (salt s₀) (saltLen s₀) = Spec.Sha256.bytesAt s₀.mem (salt s₀) (saltLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_s.symm
    · exact hp.s_p
    · exact hp.b_s.symm) (Nat.le_of_lt (s₀.gpr .x1).isLt)

theorem XR.ikmB {t : State} (hk : XR w s₀ t) :
    Spec.Sha256.bytesAt t.mem (ikm s₀) (ikmLen s₀) = Spec.Sha256.bytesAt s₀.mem (ikm s₀) (ikmLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_i.symm
    · exact hp.i_p
    · exact hp.b_i.symm) (Nat.le_of_lt (s₀.gpr .x3).isLt)

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

/-- A part of the frame is in the regions. -/
theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ xFr) :
    InRegions (t.rd ++ t.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (by rw [hwr, hp.wr]; exact List.mem_cons_self),
    Offset.contains_base _ h (by have := xFr_eq; omega_using [h, this])⟩

theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ xFr) : InRegions t.wr (sA s₀ o) n :=
  ⟨_, by rw [hwr, hp.wr]; exact List.mem_cons_self, Offset.contains_base _ h (by have := xFr_eq; omega_using [h, this])⟩

/-- An offset of the frame, as a number. -/
theorem sA_toNat {o : Nat} (ho : o ≤ xFr) : (sA s₀ o).toNat = s₀.sp.toNat + o :=
  toNat_addN (by have := hp.top; omega_using [ho, this])

omit hp in
/-- The stack below the frame, apart from a part of the frame. -/
theorem stk_fr {o n : Nat} (h : o + n ≤ xFr + 16) : Region.Disjoint (stk s₀) ⟨sA s₀ o, n⟩ := by
  have hfr := xFr_eq
  exact (Offset.disjoint_below s₀.sp (n := 16) (d := o) (k := n) (by omega_using [h, hfr])).symm

omit hp in
/-- The stack a callee uses. -/
theorem below_stk {t : State} (ht : t.sp = s₀.sp) : below t.sp 16 = stk s₀ := by rw [ht]

end

/-- The load of a table's function's address. -/
theorem tload {w : MdHash} {f : Fns} {s₀ t : State} (hp : Pre w f s₀) (k : XR w s₀ t) {j : Nat}
    (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.ldr .x .x16 .x22 (8 * j)]) t fun u =>
      Upd t u .x16 (s₀.mem.readW (tab s₀ + BitVec.ofNat 64 (8 * j)) 64) := by
  refine wp_ldr ⟨Nat.mul_mod_right 8 j, by omega_using [hj]⟩ (by rw [k.x22]) (tin hp k hj) fun u v =>
    WP.block_nil ?_
  rw [← k.tabW hp hj]; exact v

/-! ## The prologue -/

theorem pro_eq : extractPro = .addSp .x9 0 :: (Spill.saveCode .x9 xSaved ++
    ([mov .x19 .x2, mov .x20 .x3, mov .x21 .x4, mov .x22 .x6, mov .x2 .x0, mov .x3 .x1, .addSp .x0 xIn,
      .addSp .x1 xOut, .addSp .x4 xWork] : List Instr)) := rfl

/-- After the prologue: `XR`, and `init`'s arguments. -/
def XA (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ t.gpr .x0 = sA s₀ xIn ∧ t.gpr .x1 = sA s₀ xOut ∧ t.gpr .x2 = salt s₀ ∧
    t.gpr .x3 = s₀.gpr .x1 ∧ t.gpr .x4 = sA s₀ xWork

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem pro_ok : WP isa (.block extractPro) s₀ (XA w s₀) := by
  have hfr := xFr_eq
  rw [pro_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h9 : t₁.gpr .x9 = s₀.sp := u₁.gpr.trans (BitVec.add_zero _)
  rw [WP.block_append_iff]
  refine WP.mono_syms (Spill.save_wp (b := .x9) (l := xSaved) xSaved_ok fun q hq => by
      rw [h9, u₁.wr]; exact in_frw hp rfl (by have := xSaved_in q hq; omega_using [this, hfr])) fun t₂ st sy₂ => ?_
  have g₂ : ∀ r, r ≠ .x9 → t₂.gpr r = s₀.gpr r := fun r h => by rw [st.gpr, u₁.other r h]
  refine wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ =>
    wp_addImm (by decide) fun t₆ u₆ => wp_addImm (by decide) fun t₇ u₇ => wp_addImm (by decide) fun t₈ u₈ =>
    wp_addSp (by decide) fun t₉ u₉ => wp_addSp (by decide) fun t₁₀ u₁₀ => wp_addSp (by decide) fun t₁₁ u₁₁ =>
    WP.block_nil ?_
  have sp₂ : t₂.sp = s₀.sp := by rw [st.sp, u₁.sp]
  have sp₈ : t₈.sp = s₀.sp := by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂]
  have mm : t₁₁.mem = Spill.saveMem s₀.mem s₀.sp t₁.gpr xSaved := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, st.mem, u₁.mem, h9]
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := BitVec.add_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, st.rd, u₁.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, st.wr, u₁.wr]
  · rw [u₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, sy₂, u₁.syms]
  · rw [u₁₁.sp, u₁₀.sp, u₉.sp, sp₈]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e0,
      g₂ _ (by decide)]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, e0, u₃.other _ (by decide),
      g₂ _ (by decide)]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, e0, u₄.other _ (by decide), u₃.other _ (by decide),
      g₂ _ (by decide)]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, e0, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂ _ (by decide)]
  · have hx : r ∈ xRegs := kept_x r hr
    have h1 : r ≠ .x0 := fun e => by subst e; exact absurd hx (by decide)
    have h2 : r ≠ .x1 := fun e => by subst e; exact absurd hx (by decide)
    have h3 : r ≠ .x2 := fun e => by subst e; exact absurd hx (by decide)
    have h4 : r ≠ .x3 := fun e => by subst e; exact absurd hx (by decide)
    have h5 : r ≠ .x4 := fun e => by subst e; exact absurd hx (by decide)
    have h6 : r ≠ .x19 := fun e => by subst e; exact absurd hr (by decide)
    have h7 : r ≠ .x20 := fun e => by subst e; exact absurd hr (by decide)
    have h8 : r ≠ .x21 := fun e => by subst e; exact absurd hr (by decide)
    have h9' : r ≠ .x22 := fun e => by subst e; exact absurd hr (by decide)
    rw [u₁₁.other _ h5, u₁₀.other _ h2, u₉.other _ h1, u₈.other _ h4, u₇.other _ h3, u₆.other _ h9',
      u₅.other _ h8, u₄.other _ h7, u₃.other _ h6, g₂ _ (kept_ne9 r hr)]
  · intro q hq
    rw [mm]
    refine (Spill.saveMem_saved xSaved_fits _ _ _ q hq).trans ?_
    exact u₁.other _ (xSaved_ne9 q hq)
  · rw [mm]
    exact (Spill.saveMem_frame_base (n := xFr) (fun q hq => by have := xSaved_in q hq; omega_using [this, hfr])
      (by omega_using [hfr]) _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨frR s₀, by simp, fun _ h => h⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, sp₈]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.sp, sp₈]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, e0, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂ _ (by decide)]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, e0,
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂ _ (by decide)]
  · rw [u₁₁.gpr, u₁₀.sp, u₉.sp, sp₈]

end

open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

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
  Offset.sub_base _ (by have hS := hp.hw.hS; omega_using [hS, xIn_eq, xFr_eq])

theorem outR : Region.Sub ⟨sA s₀ xOut, w.H.S⟩ (frR s₀) :=
  Offset.sub_base _ (by have hS := hp.hw.hS; omega_using [hS, xOut_eq, xFr_eq])

omit hp in
theorem workR {n : Nat} (hn : n ≤ work) : Region.Sub ⟨sA s₀ xWork, n⟩ (frR s₀) :=
  Offset.sub_base _ (by omega_using [hn, xWork_eq, xFr_eq, work_eq])

theorem in_out : Region.Disjoint ⟨sA s₀ xIn, w.H.S⟩ ⟨sA s₀ xOut, w.H.S⟩ := by
  have hS := hp.hw.hS
  exact Offset.disjoint _ (.inl (by omega_using [hS, xIn_eq, xOut_eq])) (by omega_using [hS, xIn_eq])
    (by omega_using [hS, xOut_eq])

theorem in_work {n : Nat} (hn : n ≤ work) : Region.Disjoint ⟨sA s₀ xIn, w.H.S⟩ ⟨sA s₀ xWork, n⟩ := by
  have hS := hp.hw.hS
  exact Offset.disjoint _ (.inl (by omega_using [hS, xIn_eq, xWork_eq])) (by omega_using [hS, xIn_eq])
    (by omega_using [hn, xWork_eq, work_eq])

theorem out_work {n : Nat} (hn : n ≤ work) : Region.Disjoint ⟨sA s₀ xOut, w.H.S⟩ ⟨sA s₀ xWork, n⟩ := by
  have hS := hp.hw.hS
  exact Offset.disjoint _ (.inl (by omega_using [hS, xOut_eq, xWork_eq])) (by omega_using [hS, xOut_eq])
    (by omega_using [hn, xWork_eq, work_eq])

/-- The input keying material fits HMAC's count with a block of key. -/
theorem ikm_lt : w.H.P.B + ikmLen s₀ < 2 ^ 64 := by
  have h := Proof.Pbkdf2.Md.AArch64.Pbk.len_add_le hp.f_i.symm hp.ni (by
    show s₀.sp.toNat + xFr ≤ 2 ^ 64; have := hp.top; omega_using [this])
  have hB : w.H.P.B ≤ 128 := w.ok.B_le
  have h' : ikmLen s₀ + xFr ≤ 2 ^ 64 := h
  omega_using [h', hB, xFr_eq]

/-- `init`'s arguments, after the load of its address. -/
theorem init_args {t t' : State} (h : XA w s₀ t) {v : Addr} (u : Upd t t' .x16 v) :
    Proof.Pbkdf2.Md.AArch64.Any.AnyArgs (H := w.H) t' (sA s₀ xIn) (sA s₀ xOut) (salt s₀) (sA s₀ xWork)
      (saltLen s₀) := by
  obtain ⟨k, a0, a1, a2, a3, a4⟩ := h
  have hA := hp.hw.hA
  have hS := hp.hw.hS
  have hfr := xFr_eq
  have hb : below t'.sp 16 = stk s₀ := below_stk (by rw [u.sp, k.sp])
  refine ⟨by rw [u.other _ (by decide), a0], by rw [u.other _ (by decide), a1], by rw [u.other _ (by decide), a2],
    by rw [u.other _ (by decide), a3], by rw [u.other _ (by decide), a4], ?_, ?_, in_out hp, in_work hp hA,
    out_work hp hA, hp.f_s.symm.sub_right (inR hp), hp.f_s.symm.sub_right (outR hp),
    hp.f_s.symm.sub_right (workR hA), by rw [u.sp, k.sp]; exact hp.sp,
    by rw [hb]; exact stk_fr (by omega_using [hS, xIn_eq, hfr]),
    by rw [hb]; exact stk_fr (by omega_using [hS, xOut_eq, hfr]), by rw [hb]; exact hp.b_s,
    by rw [hb]; exact stk_fr (by omega_using [hA, xWork_eq, hfr, work_eq]), ?_⟩
  · exact VG.Covers.left (by
      rw [u.rd, k.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
  · rw [u.wr, k.wr, hp.wr]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨frR s₀, by simp, xIn, rfl, by dsimp only; omega_using [hS, hfr, xIn_eq]⟩
    · exact ⟨frR s₀, by simp, xOut, rfl, by dsimp only; omega_using [hS, hfr, xOut_eq]⟩
    · exact ⟨frR s₀, by simp, xWork, rfl, by dsimp only; omega_using [hA, hfr, xWork_eq, work_eq]⟩
  · rw [sA_toNat hp (by omega_using [hfr, xWork_eq])]
    have := hp.top; omega_using [hA, hfr, xWork_eq, work_eq, this]

theorem init_ok {t : State} (h : XA w s₀ t) : WP isa (tcall .x22 0 f.init) t (XI w s₀) := by
  have k := h.1
  unfold tcall
  refine WP.seq (WP.mono (tload hp k (j := 0) (by decide)) fun t' u => ?_)
  have hx16 : t'.gpr .x16 = s₀.syms w.H.hmacInitAnyN := u.gpr.trans hp.tmem.1
  refine WP.icalls_of_call (a := t'.gpr .x16) rfl ?_
    (Proof.Pbkdf2.Md.AArch64.Any.any_call (n := w.H.hmacInitAnyN) w.ok w.hmacAny w.hmacAnyD (init_args hp h u)
      fun s' ha hi ho => ?_)
  · show f.init.find? (fun q => t'.syms q.1 == t'.gpr .x16) = _
    rw [hx16, u.syms, k.sy]; exact hp.tok.i
  have hA := hp.hw.hA
  have hS := hp.hw.hS
  have hfr := xFr_eq
  have k₁ : XR w s₀ t' := k.upd (by decide) u
  have k' : XR w s₀ s' := k₁.after hp ha fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨xIn, w.H.S, rfl, by decide, by omega_using [hS, hfr, xIn_eq]⟩
    · exact .inl ⟨xOut, w.H.S, rfl, by decide, by omega_using [hS, hfr, xOut_eq]⟩
    · exact .inl ⟨xWork, _, rfl, by decide, by omega_using [hA, hfr, xWork_eq, work_eq]⟩
  rw [k₁.saltB hp] at hi ho
  exact ⟨k', hi, ho⟩

end

/-! ## `update` -/

/-- After `update`'s arguments. -/
def XUA (w : MdHash) (s₀ t : State) : Prop :=
  XI w s₀ t ∧ t.gpr .x0 = sA s₀ xIn ∧ t.gpr .x1 = BitVec.ofNat 64 w.H.P.B ∧ t.gpr .x2 = ikm s₀ ∧
    t.gpr .x3 = s₀.gpr .x3 ∧ t.gpr .x4 = sA s₀ xWork

/-- After `update`: the inner state holds the input keying material too. -/
def XU (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ w.ok.SH.Repr t.mem (sA s₀ xIn) (xorPad (k0Of w s₀) ipad ++ ikmOf s₀) ∧
    w.ok.SH.Repr t.mem (sA s₀ xOut) (xorPad (k0Of w s₀) opad)

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem updArgs_ok {t : State} (h : XI w s₀ t) : WP isa (.block extractUpd) t (XUA w s₀) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractUpd
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have k₁ : XR w s₀ t₁ := k.upd (by decide) u₁
  refine wp_ldr (a := tab s₀ + BitVec.ofNat 64 40) (by decide) (by rw [k₁.x22]) (tin hp k₁ (by decide))
    fun t₂ u₂ => ?_
  refine wp_addImm (by decide) fun t₃ u₃ => wp_addImm (by decide) fun t₄ u₄ => wp_addSp (by decide) fun t₅ u₅ =>
    WP.block_nil ?_
  have k₅ : XR w s₀ t₅ := (((k₁.upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅
  have m₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := BitVec.add_zero
  refine ⟨⟨k₅, by rw [m₅]; exact hI, by rw [m₅]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      k.sp]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem,
      k.tabW hp (by decide)]
    exact hp.tB
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e0, u₂.other _ (by decide),
      u₁.other _ (by decide), k.x19]
  · rw [u₅.other _ (by decide), u₄.gpr, e0, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), k.x20]
  · rw [u₅.gpr, u₄.sp, u₃.sp, u₂.sp, u₁.sp, k.sp]

/-- `update`'s arguments, after the load of its address. -/
theorem upd_args {t t' : State} (h : XUA w s₀ t) {v : Addr} (u : Upd t t' .x16 v) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs w.ok.stream t' (sA s₀ xIn) (ikm s₀) (sA s₀ xWork) (ikmLen s₀) := by
  obtain ⟨⟨k, -, -⟩, a0, -, a2, a3, a4⟩ := h
  have hb : below t'.sp 16 = stk s₀ := below_stk (by rw [u.sp, k.sp])
  have hS := hp.hw.hS
  have hWb := hp.hw.hWb
  have hfr := xFr_eq
  have hWw : w.ok.stream.Wb ≤ work := by omega_using [hWb, work_eq]
  have hSS : w.H.stream.S = w.H.S := rfl
  exact
    { x0 := by rw [u.other _ (by decide), a0]
      x2 := by rw [u.other _ (by decide), a2]
      x3 := by rw [u.other _ (by decide), a3]
      x4 := by rw [u.other _ (by decide), a4]
      cd := VG.Covers.left (by
        rw [u.rd, k.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by simp at hr; subst hr; simp)
      cw := by
        rw [u.wr, k.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨frR s₀, by simp, xIn, rfl, by dsimp only; omega_using [hSS, hS, hfr, xIn_eq]⟩
        · exact ⟨frR s₀, by simp, xWork, rfl, by dsimp only; omega_using [hWw, hfr, xWork_eq, work_eq]⟩
      st_sc := in_work hp hWw
      d_st := hp.f_i.symm.sub_right (inR hp)
      d_sc := hp.f_i.symm.sub_right (workR hWw)
      sp16 := by rw [u.sp, k.sp]; exact hp.sp
      stk_st := by rw [hb]; exact stk_fr (by omega_using [hSS, hS, xIn_eq, hfr])
      stk_d := by rw [hb]; exact hp.b_i
      stk_sc := by rw [hb]; exact stk_fr (by omega_using [hWw, xWork_eq, hfr, work_eq]) }

theorem upd_ok {t : State} (h : XUA w s₀ t) : WP isa (tcall .x22 1 f.upd) t (XU w s₀) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload hp k (j := 1) (by decide)) fun t' u => ?_)
  have hx16 : t'.gpr .x16 = s₀.syms w.H.updN := u.gpr.trans hp.tmem.2.1
  refine WP.icalls_of_call (a := t'.gpr .x16) rfl ?_
    (Proof.Pbkdf2.Md.AArch64.Calls.upd_call w.ok.stream (upd_args hp h u) fun s' ha hr => ?_)
  · show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .x16) = _
    rw [hx16, u.syms, k.sy]; exact hp.tok.u
  have hI := h.1.2.1
  have hO := h.1.2.2
  have a1 := h.2.2.1
  have hWb := hp.hw.hWb
  have hS := hp.hw.hS
  have hfr := xFr_eq
  have hWw : w.ok.stream.Wb ≤ work := by omega_using [hWb, work_eq]
  have hSS : w.H.stream.S = w.H.S := rfl
  have hb : below t'.sp 16 = stk s₀ := below_stk (by rw [u.sp, k.sp])
  have k₁ : XR w s₀ t' := k.upd (by decide) u
  have k' : XR w s₀ s' := k₁.after hp ha fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨xIn, _, rfl, by decide, by omega_using [hSS, hS, hfr, xIn_eq]⟩
    · exact .inl ⟨xWork, _, rfl, by decide, by omega_using [hWw, hfr, xWork_eq, work_eq]⟩
  have hm : t'.mem = t.mem := u.mem
  have hl : (xorPad (k0Of w s₀) ipad).length = w.H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_length w.ok]
  refine ⟨k', ?_, ?_⟩
  · have := hr (xorPad (k0Of w s₀) ipad) (by rw [hm]; exact hI) (by rw [u.other _ (by decide), a1, hl])
    rwa [k₁.ikmB hp] at this
  · refine repr_keep (w := w) (m := t'.mem) (fun i hi => ?_) (by rw [hm]; exact hO)
    refine ha.frame.bytes (R := ⟨sA s₀ xOut, w.H.S⟩) (fun r hr => ?_) (by show w.H.S ≤ 2 ^ 64; omega_using [hS]) hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (in_out hp).symm
    · exact out_work hp hWw
    · rw [hb]; exact (stk_fr (by omega_using [hS, hfr, xOut_eq])).symm

end

/-! ## `finalize` -/

/-- After `finalize`'s arguments. -/
def XFA (w : MdHash) (s₀ t : State) : Prop :=
  XU w s₀ t ∧ t.gpr .x0 = sA s₀ xIn ∧ t.gpr .x1 = sA s₀ xOut ∧
    t.gpr .x2 = BitVec.ofNat 64 w.H.P.B + s₀.gpr .x3 ∧ t.gpr .x3 = prk s₀ ∧ t.gpr .x4 = sA s₀ xWork

/-- After `finalize`: `PRK`. -/
def XF (w : MdHash) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ bytesAt t.mem (prk s₀) w.H.D = hmacBlockKey w.ok.SH.H (k0Of w s₀) (ikmOf s₀)

/-- HMAC's `finalize` of `w`, verified. -/
theorem hF (w : MdHash) :
    Verified AArch64.target w.H.hmacFin (Proof.Pbkdf2.Md.AArch64.Calls.finG w.ok.SH w.H.W) :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_ok w.ok w.C (by rw [w.hSH, w.hW]; exact w.hmacFin.2.2)

theorem hFd (w : MdHash) : w.H.hmacFin.aarch64Depth ≤ 1 :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_fdepth w.ok.stream.finDepth w.ok.comp.noFrames

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem finArgs_ok {t : State} (h : XU w s₀ t) : WP isa (.block extractFin) t (XFA w s₀) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractFin
  refine wp_addSp (by decide) fun t₁ u₁ => wp_addSp (by decide) fun t₂ u₂ => ?_
  have k₂ : XR w s₀ t₂ := (k.upd (by decide) u₁).upd (by decide) u₂
  refine wp_ldr (a := tab s₀ + BitVec.ofNat 64 40) (by decide) (by rw [k₂.x22]) (tin hp k₂ (by decide))
    fun t₃ u₃ => ?_
  refine wp_add fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ => wp_addSp (by decide) fun t₆ u₆ =>
    WP.block_nil ?_
  have k₆ : XR w s₀ t₆ := (((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have e0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := BitVec.add_zero
  refine ⟨⟨k₆, by rw [m₆]; exact hI, by rw [m₆]; exact hO⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, k.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.sp, k.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), k.x20, m₂, k.tabW hp (by decide), hp.tB]
  · rw [u₆.other _ (by decide), u₅.gpr, e0, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), k.x21]
  · rw [u₆.gpr, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, k.sp]

/-- `finalize`'s arguments, after the load of its address. -/
theorem fin_args {t t' : State} (h : XFA w s₀ t) {v : Addr} (u : Upd t t' .x16 v) :
    Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := w.H) t' (sA s₀ xIn) (sA s₀ xOut)
      (BitVec.ofNat 64 w.H.P.B + s₀.gpr .x3) (prk s₀) (sA s₀ xWork) := by
  obtain ⟨⟨k, -, -⟩, a0, a1, a2, a3, a4⟩ := h
  have hb : below t'.sp 16 = stk s₀ := below_stk (by rw [u.sp, k.sp])
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hfr := xFr_eq
  have hWw : 8 * w.H.W ≤ work := by omega_using [hW, work_eq]
  exact
    { x0 := by rw [u.other _ (by decide), a0]
      x1 := by rw [u.other _ (by decide), a1]
      x2 := by rw [u.other _ (by decide), a2]
      x3 := by rw [u.other _ (by decide), a3]
      x4 := by rw [u.other _ (by decide), a4]
      cr := by
        rw [u.rd, u.wr, k.rd, k.wr, hp.rd, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨frR s₀, by simp, xOut, rfl, by dsimp only; omega_using [hS, hfr, xOut_eq]⟩
      cw := by
        rw [u.wr, k.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨frR s₀, by simp, xIn, rfl, by dsimp only; omega_using [hS, hfr, xIn_eq]⟩
        · exact ⟨prkR w s₀, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; omega_using []⟩
        · exact ⟨frR s₀, by simp, xWork, rfl, by dsimp only; omega_using [hWw, hfr, xWork_eq, work_eq]⟩
      i_u := in_out hp
      i_o := hp.f_p.sub_left (inR hp)
      i_s := in_work hp hWw
      u_o := hp.f_p.sub_left (outR hp)
      u_s := out_work hp hWw
      o_s := (hp.f_p.sub_left (workR hWw)).symm
      sp16 := by rw [u.sp, k.sp]; exact hp.sp
      stk_i := by rw [hb]; exact stk_fr (by omega_using [hS, xIn_eq, hfr])
      stk_u := by rw [hb]; exact stk_fr (by omega_using [hS, xOut_eq, hfr])
      stk_o := by rw [hb]; exact hp.b_p
      stk_s := by rw [hb]; exact stk_fr (by omega_using [hWw, xWork_eq, hfr, work_eq])
      scnw := by
        rw [sA_toNat hp (by omega_using [hfr, xWork_eq])]
        have := hp.top; omega_using [hWw, hfr, xWork_eq, work_eq, this] }

theorem fin_ok {t : State} (h : XFA w s₀ t) : WP isa (tcall .x22 2 f.fin) t (XF w s₀) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload hp k (j := 2) (by decide)) fun t' u => ?_)
  have hx16 : t'.gpr .x16 = s₀.syms w.H.hmacFinN := u.gpr.trans hp.tmem.2.2
  refine WP.icalls_of_call (a := t'.gpr .x16) rfl ?_
    (Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call w.ok (hF w) (hFd w) (fin_args hp h u) fun s' ha hpost => ?_)
  · show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .x16) = _
    rw [hx16, u.syms, k.sy]; exact hp.tok.f
  have hI := h.1.2.1
  have hO := h.1.2.2
  have hS := hp.hw.hS
  have hW := hp.hw.hW
  have hfr := xFr_eq
  have hWw : 8 * w.H.W ≤ work := by omega_using [hW, work_eq]
  have k' : XR w s₀ s' := (k.upd (by decide) u).after hp ha fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨xIn, _, rfl, by decide, by omega_using [hS, hfr, xIn_eq]⟩
    · exact .inr fun _ h => h
    · exact .inl ⟨xWork, _, rfl, by decide, by omega_using [hWw, hfr, xWork_eq, work_eq]⟩
  have hm : t'.mem = t.mem := u.mem
  have hl : (k0Of w s₀).length = w.H.P.B := Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_length w.ok _
  have hil : (ikmOf s₀).length = ikmLen s₀ := Proof.Hmac.Common.bytesAt_length _ _ _
  have hlt := ikm_lt hp
  refine ⟨k', hpost (k0Of w s₀) (ikmOf s₀) hl (by rw [hl, hil]; exact hlt) (by rw [hm]; exact hI) ?_
    (by rw [hm]; exact hO)⟩
  rw [hil]
  apply BitVec.eq_of_toNat_eq
  have hd := (s₀.gpr .x3).isLt
  have he : ikmLen s₀ = (s₀.gpr .x3).toNat := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hlt, hd, he]

end

/-! ## The epilogue, and the frame's body -/

theorem epi_eq : extractEpi = .addSp .x9 0 :: Spill.restoreCode .x9 xSaved := rfl

section
variable {w : MdHash} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- The epilogue restores our caller's registers. -/
theorem epi_ok {t : State} (k : XR w s₀ t) :
    WP isa (.block extractEpi) t fun u => (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s₀.gpr r) ∧
      u.sp = s₀.sp ∧ u.mem = t.mem := by
  have hfr := xFr_eq
  rw [epi_eq]
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h9 : t₁.gpr .x9 = s₀.sp := by rw [u₁.gpr, k.sp]; exact BitVec.add_zero _
  refine WP.mono (Spill.restore_wp h9 xSaved_ok (by decide) (fun q hq => ?_) (by rw [u₁.mem]; exact k.saved))
    fun u hr => ⟨fun r hr' h30 => ?_, by rw [hr.sp, u₁.sp, k.sp], by rw [hr.mem, u₁.mem]⟩
  · exact in_fr hp (u₁.wr.trans k.wr) (by have := xSaved_in q hq; omega_using [this, hfr])
  · rcases pres_split r hr' h30 with hm | hm
    · exact hr.gpr_of (.inl hm)
    · exact hr.gpr_of (.inr (by rw [u₁.other r (kept_ne9 r hm), k.cs r hm]))

/-- The frame's body: our caller's registers restored, the return address
kept, and `PRK`. -/
theorem main_ok : WP isa (extractMain f) s₀ fun u => (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s₀.gpr r) ∧
      u.sp = s₀.sp ∧ u.mem.read (sA s₀ xFr) 8 = s₀.mem.read (sA s₀ xFr) 8 ∧
      bytesAt u.mem (prk s₀) w.H.D = hmacBlockKey w.ok.SH.H (k0Of w s₀) (ikmOf s₀) := by
  have hfr := xFr_eq
  unfold extractMain
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => WP.seq (WP.mono (init_ok hp h₁) fun t₂ h₂ =>
    WP.seq (WP.mono (updArgs_ok hp h₂) fun t₃ h₃ => WP.seq (WP.mono (upd_ok hp h₃) fun t₄ h₄ =>
    WP.seq (WP.mono (finArgs_ok hp h₄) fun t₅ h₅ => WP.seq (WP.mono (fin_ok hp h₅) fun t₆ h₆ => ?_))))))
  obtain ⟨k₆, hP⟩ := h₆
  refine WP.mono (epi_ok hp k₆) fun u ⟨hcs, hsp, hm⟩ => ⟨hcs, hsp, ?_, by rw [hm]; exact hP⟩
  rw [hm]
  refine k₆.frame.read (r := ⟨sA s₀ xFr, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hfr])
  · exact hp.r_p.sub_left (Region.sub_prefix (by decide))
  · exact (stk_fr (o := xFr) (n := 8) (by omega_using [])).symm

end

/-- `vg_hkdf_extract` meets `extractR` and keeps the callee-saved registers
and the stack pointer. -/
theorem extract_correct {w : MdHash} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hp : (extractR w f ns xStack).pre s) :
    WP isa (extract f) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (extractR w f ns xStack).post s s' := by
  have hS := stackAt s xFr hp.1
  have p := pre_entered hw hp
  have hN := hp.1
  obtain ⟨-, -, -, -, -, -, ks, ki, kp, -, -, -, -, -, hpl, -, -, -⟩ := hp
  have hxs : xStack = xFr + 32 := rfl
  have hnw := hS.nw
  rw [xstk_eq] at ks ki kp
  unfold extract framed
  refine WP.frameAlloc (by omega_using [hN, hxs]) (by decide) ?_
    (WP.mono (main_ok p) fun t ⟨hcs, hsp, hret, hP⟩ m u hm => ?_)
  · rw [hS.push, toNat_addN (by omega_using [hnw])]; omega_using []
  have hs0 : (entered xFr s).sp = base s xFr + BitVec.ofNat 64 16 := hS.frame
  -- The return address's slot and the frame, within the stack.
  obtain subQ : Region.Sub ⟨s.sp - 16, 16⟩ ⟨base s xFr, xStack⟩ := by
    rw [hS.push]; exact Offset.sub_base _ (by omega_using [hxs])
  obtain subR : Region.Sub (below s.sp (xFr + 16)) ⟨base s xFr, xStack⟩ := by
    show Region.Sub ⟨s.sp - BitVec.ofNat 64 (xFr + 16), xFr + 16⟩ _
    rw [Offset.sub_ofNat_eq s.sp (show xFr + 16 ≤ xFr + 32 by omega_using []),
      show xFr + 32 - (xFr + 16) = 16 from by omega_using []]
    exact Offset.sub_base _ (by omega_using [hxs])
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (popped .x30 (freed xFr t)).gpr r = s.gpr r
    have hfs : t.sp + BitVec.ofNat 64 xFr = s.sp - 16 := by rw [hsp]; exact push_eq s
    have hread : (freed xFr t).mem.read (freed xFr t).sp 8 = s.gpr .x30 := by
      have e : sA (allocated xFr (pushed .x30 s)) xFr = s.sp - 16 := push_eq s
      rw [e] at hret
      simp only [freed]
      rw [hfs, hret]
      exact read_write_self _ _ _
    show ((freed xFr t).write .x .x30 ((freed xFr t).mem.read (freed xFr t).sp 8)).gpr r = _
    rw [RegUpd.gpr_write]
    by_cases h30 : r = .x30
    · subst h30; simp only [ite_true, hread, BitVec.setWidth_eq]
    · simp only [h30, ite_false]
      exact hcs r hr h30
  · show t.sp + BitVec.ofNat 64 xFr + BitVec.ofNat 64 16 = s.sp
    rw [hsp, hs0, Offset.add_add, Offset.add_add, hS.sp, show 16 + (xFr + 16) = xFr + 32 from by omega_using []]
  · show bytesAt m (s.gpr .x4) w.H.D = Spec.Hmac.hmac _ _ _
    rw [hpl] at kp
    have e : bytesAt m (s.gpr .x4) w.H.D = bytesAt t.mem (s.gpr .x4) w.H.D :=
      Proof.Sha256.Stream.bytesAt_congr fun i hi => hm.bytes (R := ⟨s.gpr .x4, w.H.D⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact kp.symm.sub_right subR)
        (by show w.H.D ≤ 2 ^ 64; have := (s.gpr .x5).isLt; omega_using [this, hpl]) hi
    rw [e, ← entered_bytes (s := s) (p := s.gpr .x0) (n := (s.gpr .x1).toNat) (ks.symm.sub_right subQ)
        (Nat.le_of_lt (s.gpr .x1).isLt),
      ← entered_bytes (s := s) (p := s.gpr .x2) (n := (s.gpr .x3).toNat) (ki.symm.sub_right subQ)
        (Nat.le_of_lt (s.gpr .x3).isLt)]
    exact hP

/-! ## Constant time -/

/-- Code that leaks the same trace in both runs, with what each run gives. -/
theorem rel_wp {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun _ _ => True)
    (hw : ∀ s, P₁ s → WP isa c s G₁) (hw' : ∀ s, P₂ s → WP isa c s G₂) :
    RelCT isa (fun s s' => P₁ s ∧ P₂ s') c fun s s' => G₁ s ∧ G₂ s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The indirect call of the table's function `j`, whose address `a` both
runs load. -/
theorem tcall_rel {Φ₁ Φ₂ : State → Prop} {j : Nat} {ts : List (String × Prog isa)} {n : String}
    {c : Prog isa} {a : Addr} (hcl : Ck [.x22] (.block [.ldr .x .x16 .x22 (8 * j)]))
    (hag : ∀ s s', Φ₁ s → Φ₂ s' → s.sp = s'.sp ∧ ∀ r ∈ [Reg.x22], s.gpr r = s'.gpr r)
    (hld₁ : ∀ t, Φ₁ t → WP isa (.block [.ldr .x .x16 .x22 (8 * j)]) t fun u => Upd t u .x16 a)
    (hld₂ : ∀ t, Φ₂ t → WP isa (.block [.ldr .x .x16 .x22 (8 * j)]) t fun u => Upd t u .x16 a)
    (hf₁ : ∀ t, Φ₁ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hf₂ : ∀ t, Φ₂ t → ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hcall : RelCT isa (fun u u' => (∃ t, Φ₁ t ∧ Upd t u .x16 a) ∧ (∃ t', Φ₂ t' ∧ Upd t' u' .x16 a))
      (.call n c) fun _ _ => True) :
    RelCT isa (fun t t' => Φ₁ t ∧ Φ₂ t') (tcall .x22 j ts) fun _ _ => True := by
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

/-- The registers `XR` fixes that hold the pointers and lengths. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x22]

/-- The taint checks of the pieces of `vg_hkdf_extract` between the calls. -/
structure XChecks : Prop where
  pro : Ck [.x0, .x1, .x2, .x3, .x4, .x6] (.block extractPro)
  tl0 : Ck [.x22] (.block [.ldr .x .x16 .x22 (8 * 0)])
  tl1 : Ck [.x22] (.block [.ldr .x .x16 .x22 (8 * 1)])
  tl2 : Ck [.x22] (.block [.ldr .x .x16 .x22 (8 * 2)])
  ua : Ck pubRegs (.block extractUpd)
  fa : Ck pubRegs (.block extractFin)
  epi : Ck [] (.block extractEpi)

theorem xchecks : XChecks :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : MdHash) (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6], s₀.gpr r = s₀'.gpr r
  hi : s₀.syms w.H.hmacInitAnyN = s₀'.syms w.H.hmacInitAnyN
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.H.hmacFinN = s₀'.syms w.H.hmacFinN

/-- The loaded address of a table's function, as the table holds it. -/
theorem upd_val {t u : State} {d : Reg} {v v' : BitVec 64} (h : Upd t u d v) (e : v = v') : Upd t u d v' :=
  { h with gpr := h.gpr.trans e }

section
variable {w : MdHash} {f : Fns} {s₀ s₀' : State} (hp : Pre w f s₀) (hp' : Pre w f s₀')
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
theorem ag {t t' : State} (k : XR w s₀ t) (k' : XR w s₀' t') :
    t.sp = t'.sp ∧ ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  refine ⟨by rw [k.sp, k'.sp, hq.sp], fun r hr => ?_⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [k.x19, k'.x19]; exact hq.regs .x2 (by simp)
  · rw [k.x20, k'.x20]; exact hq.regs .x3 (by simp)
  · rw [k.x21, k'.x21]; exact hq.regs .x4 (by simp)
  · rw [k.x22, k'.x22]; exact hq.regs .x6 (by simp)

omit hp hp' in
theorem ag22 {t t' : State} (k : XR w s₀ t) (k' : XR w s₀' t') :
    t.sp = t'.sp ∧ ∀ r ∈ [Reg.x22], t.gpr r = t'.gpr r :=
  ⟨(ag hq k k').1, fun r hr => (ag hq k k').2 r (by simp at hr; subst hr; simp)⟩

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (extractMain f) fun _ _ => True := by
  have kc := xchecks
  have e0 := hq.regs .x0 (by simp); have e1 := hq.regs .x1 (by simp); have e2 := hq.regs .x2 (by simp)
  have e3 := hq.regs .x3 (by simp); have e4 := hq.regs .x4 (by simp)
  have esp := hq.sp
  unfold extractMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := XA w s₀) (G₂ := XA w s₀')
    (rs := [.x0, .x1, .x2, .x3, .x4, .x6]) (fun s s' hs hs' => by subst hs hs'; exact ⟨hq.sp, hq.regs⟩) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => XA w s₀ t ∧ XA w s₀' t') (tcall .x22 0 f.init)
      fun t t' => XI w s₀ t ∧ XI w s₀' t' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.hmacInitAnyN) kc.tl0 (fun t t' k k' => ag22 hq k.1 k'.1)
      (fun t k => WP.mono (tload hp k.1 (j := 0) (by decide)) fun u v => upd_val v hp.tmem.1)
      (fun t k => WP.mono (tload hp' k.1 (j := 0) (by decide)) fun u v => upd_val v (hp'.tmem.1.trans hq.hi.symm))
      (fun t k => by rw [k.1.sy]; exact hp.tok.i) (fun t k => by rw [k.1.sy, hq.hi]; exact hp'.tok.i)
      (Proof.Pbkdf2.Md.AArch64.Any.any_rel (n := w.H.hmacInitAnyN) w.ok w.hmacAny
        fun u u' ⟨⟨t, k, v⟩, ⟨t', k', v'⟩⟩ => ⟨init_args hp k v,
          by have := init_args hp' k' v'; simp only [sA, salt, saltLen] at this ⊢; rwa [← e0, ← e1, ← esp] at this,
          by rw [v.sp, v'.sp, k.1.sp, k'.1.sp, esp]⟩))
      (fun t k => init_ok hp k) (fun t k => init_ok hp' k)
  have r3 := rel_agree (P₁ := XI w s₀) (P₂ := XI w s₀') (G₁ := XUA w s₀) (G₂ := XUA w s₀') (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.ua (fun t k => updArgs_ok hp k) (fun t k => updArgs_ok hp' k)
  have r4 : RelCT isa (fun t t' => XUA w s₀ t ∧ XUA w s₀' t') (tcall .x22 1 f.upd)
      fun t t' => XU w s₀ t ∧ XU w s₀' t' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.updN) kc.tl1 (fun t t' k k' => ag22 hq k.1.1 k'.1.1)
      (fun t k => WP.mono (tload hp k.1.1 (j := 1) (by decide)) fun u v => upd_val v hp.tmem.2.1)
      (fun t k => WP.mono (tload hp' k.1.1 (j := 1) (by decide)) fun u v =>
        upd_val v (hp'.tmem.2.1.trans hq.up.symm))
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.u) (fun t k => by rw [k.1.1.sy, hq.up]; exact hp'.tok.u)
      (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel w.ok.stream fun u u' ⟨⟨t, k, v⟩, ⟨t', k', v'⟩⟩ => ⟨upd_args hp k v,
        by have := upd_args hp' k' v'; simp only [sA, ikm, ikmLen] at this ⊢; rwa [← e2, ← e3, ← esp] at this,
        by rw [v.other _ (by decide), v'.other _ (by decide), k.2.2.1, k'.2.2.1],
        by rw [v.sp, v'.sp, k.1.1.sp, k'.1.1.sp, esp]⟩))
      (fun t k => upd_ok hp k) (fun t k => upd_ok hp' k)
  have r5 := rel_agree (P₁ := XU w s₀) (P₂ := XU w s₀') (G₁ := XFA w s₀) (G₂ := XFA w s₀') (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.fa (fun t k => finArgs_ok hp k) (fun t k => finArgs_ok hp' k)
  have r6 : RelCT isa (fun t t' => XFA w s₀ t ∧ XFA w s₀' t') (tcall .x22 2 f.fin)
      fun t t' => XF w s₀ t ∧ XF w s₀' t' :=
    rel_wp (tcall_rel (a := s₀.syms w.H.hmacFinN) kc.tl2 (fun t t' k k' => ag22 hq k.1.1 k'.1.1)
      (fun t k => WP.mono (tload hp k.1.1 (j := 2) (by decide)) fun u v => upd_val v hp.tmem.2.2)
      (fun t k => WP.mono (tload hp' k.1.1 (j := 2) (by decide)) fun u v =>
        upd_val v (hp'.tmem.2.2.trans hq.hf.symm))
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.f) (fun t k => by rw [k.1.1.sy, hq.hf]; exact hp'.tok.f)
      (Proof.Pbkdf2.Md.AArch64.Pbk.hfin_rel w.ok (hF w) fun u u' ⟨⟨t, k, v⟩, ⟨t', k', v'⟩⟩ => ⟨fin_args hp k v,
        by have := fin_args hp' k' v'; simp only [sA, prk] at this ⊢; rwa [← e3, ← e4, ← esp] at this,
        by rw [v.sp, v'.sp, k.1.1.sp, k'.1.1.sp, esp]⟩))
      (fun t k => fin_ok hp k) (fun t k => fin_ok hp' k)
  have r7 := rel_agree (P₁ := XF w s₀) (P₂ := XF w s₀') (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [])
    (fun t t' k k' => ⟨by rw [k.1.sp, k'.1.sp, esp], fun r hr => absurd hr List.not_mem_nil⟩) kc.epi
    (fun t k => WP.mono (epi_ok hp k.1) fun _ _ => trivial) (fun t k => WP.mono (epi_ok hp' k.1) fun _ _ => trivial)
  exact ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ _ => trivial)

end

/-- `vg_hkdf_extract` is constant time: two runs whose public data agree
leak the same trace. -/
theorem extract_ct {w : MdHash} {f : Fns} {ns : List String} (hw : HOk w)
    (hns : ∀ n ∈ [w.H.hmacInitAnyN, w.H.updN, w.H.hmacFinN], n ∈ ns) :
    ConstantTime isa (extractR w f ns xStack).pre (extractR w f ns xStack).pub (extract f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_entered hw h; have hp' := pre_entered hw h'
  obtain ⟨qsp, q0, q1, q2, q3, q4, -, q6, qn⟩ := hpub
  have hq : PubEq w (entered xFr e) (entered xFr e') :=
    ⟨show e.sp - 16 - BitVec.ofNat 64 xFr = e'.sp - 16 - BitVec.ofNat 64 xFr by rw [qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact q0
      · exact q1
      · exact q2
      · exact q3
      · exact q4
      · exact q6, qn _ (hns _ (by simp)), qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (extract f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold extract framed
  refine RelCT.pushFrame (R := fun _ _ => True) (fun a b ⟨ha, hb⟩ => by rw [ha, hb, qsp]) ?_
  refine RelCT.alloc (R := fun _ _ => True) ((main_rel hp hp' hq).mono
    (fun x y ⟨u, v, ⟨p, q, ⟨hp₁, hq₁⟩, hu, hv⟩, hx, hy⟩ => ⟨by rw [hx, hu, hp₁], by rw [hy, hv, hq₁]⟩)
    fun _ _ h => h)

end VG.Proof.Hkdf.AArch64.Extract
