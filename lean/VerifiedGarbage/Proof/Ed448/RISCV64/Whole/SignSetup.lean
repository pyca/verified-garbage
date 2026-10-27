module

import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Spec.Ed448

/-!
# `vg_ed448_sign_cached` on RISC-V: the setup

The contract by register (`SignPre`): `out` in `a0`, `seed` in `a1`, `pk`
in `a2`, the context in `a3` (`ctxlen` in `a4`), the message in `a5` (`len`
in `a6`), `scratch` in `a7`, and the frame `F` (520 bytes) the stack
argument at `sp`. `F` is read into `t0` (`frame_ok`), the registers saved at
`448(F)`, the arguments moved to `s0`–`s2` and `s7`–`s11`, `pk` copied to
`384(F)`, and the first ten bytes of `dom4(0, C)` written at `F`
(`signSetup_ok`, `hdr_ok`): the invariant `Inv` holds from the entry state on
(`SInv`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots copyIn)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea copyIn_ok)
open VG.Spec.Ed448 (bytesAt)

/-! ## The regions -/

section
variable (s : State)

abbrev sF : Addr := stackArg s 0
abbrev oR : Region := ⟨s.gpr .a0, 114⟩
abbrev sdR : Region := ⟨s.gpr .a1, 57⟩
abbrev pkR : Region := ⟨s.gpr .a2, 57⟩
abbrev cxR : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev msR : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev scR : Region := ⟨s.gpr .a7, 8192⟩
abbrev fR : Region := ⟨sF s, 520⟩
/-- The stack argument. -/
abbrev aR : Region := ⟨stackArgAddr s 0, 8⟩

end

/-- The precondition, by register. -/
structure SignPre (s : State) : Prop where
  rd : s.rd = [sdR s, pkR s, cxR s, msR s, aR s]
  wr : s.wr = [oR s, scR s, fR s]
  oS : (oR s).Disjoint (sdR s)
  oP : (oR s).Disjoint (pkR s)
  oX : (oR s).Disjoint (cxR s)
  oM : (oR s).Disjoint (msR s)
  oC : (oR s).Disjoint (scR s)
  oF : (oR s).Disjoint (fR s)
  cS : (scR s).Disjoint (sdR s)
  cP : (scR s).Disjoint (pkR s)
  cX : (scR s).Disjoint (cxR s)
  cM : (scR s).Disjoint (msR s)
  cF : (scR s).Disjoint (fR s)
  fS : (fR s).Disjoint (sdR s)
  fP : (fR s).Disjoint (pkR s)
  fX : (fR s).Disjoint (cxR s)
  fM : (fR s).Disjoint (msR s)
  alC : (s.gpr .a7).toNat % 8 = 0
  alF : (sF s).toNat % 8 = 0
  spal : s.sp.toNat % 16 = 0
  sp : 1168 ≤ s.sp.toNat
  bO : (below s.sp 1168).Disjoint (oR s)
  bS : (below s.sp 1168).Disjoint (sdR s)
  bP : (below s.sp 1168).Disjoint (pkR s)
  bX : (below s.sp 1168).Disjoint (cxR s)
  bM : (below s.sp 1168).Disjoint (msR s)
  bC : (below s.sp 1168).Disjoint (scR s)
  bF : (below s.sp 1168).Disjoint (fR s)
  pk : bytesAt s.mem (s.gpr .a2) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .a1) 57)
  cl : (s.gpr .a4).toNat ≤ 255

/-- What the body may write. -/
abbrev signW (s : State) : List Region := [oR s, scR s, fR s, below s.sp 1168]

/-- The values in the registers. -/
def signV (s : State) : Reg → BitVec 64
  | .s0 => s.gpr .a0 | .s1 => s.gpr .a7 | .s2 => s.gpr .a1 | .s7 => s.gpr .a3 | .s8 => s.gpr .a4
  | .s9 => s.gpr .a5 | .s10 => s.gpr .a6 | .s11 => stackArg s 0 | _ => 0

abbrev SInv (s : State) : State → Prop := Inv s (sF s) 448 signRegs (signV s) (signW s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

/-- The inputs, while the body runs: none of them is in `signW`. -/
theorem sign_keep {s t : State} (hp : SignPre s) (h : SInv s t) {R : Region}
    (hR : R = sdR s ∨ R = pkR s ∨ R = cxR s ∨ R = msR s) :
    Spec.Sha3.bytesAt t.mem R.base R.len = Spec.Sha3.bytesAt s.mem R.base R.len := by
  refine bytes_keep h.frame (by
      rcases hR with rfl | rfl | rfl | rfl <;> first | (show (57 : Nat) < 2 ^ 64; decide) | exact BitVec.isLt _)
    fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hR with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl
  all_goals first
    | exact hp.oS.symm | exact hp.oP.symm | exact hp.oX.symm | exact hp.oM.symm
    | exact hp.cS.symm | exact hp.cP.symm | exact hp.cX.symm | exact hp.cM.symm
    | exact hp.fS.symm | exact hp.fP.symm | exact hp.fX.symm | exact hp.fM.symm
    | exact hp.bS.symm | exact hp.bP.symm | exact hp.bX.symm | exact hp.bM.symm

/-! ## The frame -/

/-- `F` read into `t0`. -/
theorem frame_ok {s : State} (hp : SignPre s) {Q : State → Prop}
    (k : ∀ u, Upd s u .t0 (sF s) → WP isa (.block []) u Q) : WP isa (.block signFrame) s Q := by
  unfold signFrame
  have ha : stackArgAddr s 0 = s.sp := by simp [stackArgAddr]
  refine wp_addSp (by decide) fun u₁ h₁ => ?_
  refine wp_ld (a := s.sp) (by decide) (by rw [h₁.gpr, BitVec.add_zero, BitVec.add_zero])
    (by omega_using [hp.spal]) (by rw [h₁.rd, h₁.wr, hp.rd]; exact ⟨aR s, by simp, by rw [← ha]; exact Region.contains_self _ _⟩)
    fun u₂ h₂ => k u₂ ⟨by rw [h₂.gpr, h₁.mem]; show _ = s.mem.readW (stackArgAddr s 0) 64; rw [ha],
      fun r hr => by rw [h₂.other r hr, h₁.other r hr], by rw [h₂.mem, h₁.mem], by rw [h₂.rd, h₁.rd],
      by rw [h₂.wr, h₁.wr], by rw [h₂.sp, h₁.sp]⟩

/-! ## The header of `dom4` -/

/-- `"SigEd448"`, the first eight bytes of `dom4`, as a doubleword. -/
abbrev sigWord : BitVec 64 := 0x3834346445676953

/-- The memory after the header is written. -/
abbrev hdrMem (m : Mem) (F : Addr) (c : Nat) : Mem :=
  ((m.writeW F sigWord).writeW (F + BitVec.ofNat 64 8) (0 : BitVec 8)).writeW (F + BitVec.ofNat 64 9)
    (BitVec.ofNat 8 c)

/-- The first ten bytes of `dom4(0, C)`, for a context of `c` bytes. -/
def hdrBytes (c : Nat) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c]

theorem dom4_eq (ctx : List Byte) : Spec.Ed448.dom4 0 ctx = hdrBytes ctx.length ++ ctx := by
  simp [Spec.Ed448.dom4, hdrBytes]

theorem sigWord_bytes : ∀ i < 8, sigWord.extractLsb' (8 * i) 8 =
    ("SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat))[i]?.getD 0 := by decide

theorem hdrMem_bytes (m : Mem) (F : Addr) (c : Nat) : bytesAt (hdrMem m F c) F 10 = hdrBytes c := by
  apply List.ext_getElem
  · simp [bytesAt, hdrBytes]
  · intro i hi _
    have hi' : i < 10 := by simpa [bytesAt] using hi
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    have ne : ∀ j, j < 10 → i ≠ j → F + BitVec.ofNat 64 i ≠ F + BitVec.ofNat 64 j := fun j hj h =>
      off_ne F (by omega) (by omega) h
    unfold hdrMem
    rw [Proof.Sha3.writeW8_apply, Proof.Sha3.writeW8_apply]
    by_cases h9 : i = 9
    · subst h9; simp [hdrBytes]
    by_cases h8 : i = 8
    · subst h8; simp [hdrBytes]
    rw [ite_eq_right (ne 9 (by decide) h9), ite_eq_right (ne 8 (by decide) h8)]
    have hi8 : i < 8 := by omega
    simp only [Mem.writeW, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), show i < 64 / 8 by omega, ↓reduceIte, BitVec.setWidth_eq]
    rw [sigWord_bytes i hi8]
    simp only [hdrBytes, List.getElem_append_left (by simp; omega : i < ("SigEd448".toList.map _).length)]
    rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some]

theorem hdrMem_frame (m : Mem) (F : Addr) (c : Nat) : Frame [⟨F, 10⟩] m (hdrMem m F c) := by
  have h : ∀ j, j + 1 ≤ 10 → (⟨F, 10⟩ : Region).Contains (F + BitVec.ofNat 64 j) (8 / 8) := fun j hj =>
    Offset.contains_base F (by omega) (by omega)
  refine (((Frame.refl _ _).writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ (h 8 (by decide))).writeW
    List.mem_cons_self _ (h 9 (by decide))
  simpa using Offset.contains_base F (d := 0) (n := 64 / 8) (k := 10) (by decide) (by decide)

theorem sig_value : (sext32 (0x38343464 : BitVec 32) <<< 32) ||| sext32 (0x45676953 : BitVec 32) = sigWord := by
  decide

/-- The header, from `c = ctxlen < 256`, at `F` in `f`, through `a5` and `a6`. -/
theorem hdr_ok {s : State} {f c : Reg} (hf5 : f ≠ .a5) (hf6 : f ≠ .a6) {F : Addr} {cl : Nat}
    (hF : s.gpr f = F) (hc : s.gpr c = BitVec.ofNat 64 cl) (hw : ∀ j < 10, InRegions s.wr (F + BitVec.ofNat 64 j) 1)
    (hw8 : InRegions s.wr F 8) (hal : F.toNat % 8 = 0) (hc5 : c ≠ .a5) (hc6 : c ≠ .a6) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, t.mem = hdrMem s.mem F cl → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      (∀ r, r ≠ .a5 → r ≠ .a6 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (hdr f c ++ is)) s Q := by
  unfold hdr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append_iff.mpr (WP.mono (ByteLoad.li32_ok (d := .a5) _) fun u₁ e₁ => ?_)
  subst e₁
  refine wp_sll (by decide) fun u₂ h₂ => ?_
  refine WP.block_append_iff.mpr (WP.mono (ByteLoad.li32_ok (d := .a6) _) fun u₃ e₃ => ?_)
  subst e₃
  refine wp_or fun u₄ h₄ => ?_
  have h₁ := Upd.write s .a5 (sext32 0x38343464)
  have h₃ := Upd.write u₂ .a6 (sext32 0x45676953)
  have g : ∀ r, r ≠ .a5 → r ≠ .a6 → u₄.gpr r = s.gpr r := fun r r5 r6 => by
    rw [h₄.other r r5, h₃.other r r6, h₂.other r r5, h₁.other r r5]
  have v : u₄.gpr .a5 = sigWord := by
    rw [h₄.gpr, h₃.other _ (by decide), h₃.gpr, h₂.gpr, h₁.gpr]; exact sig_value
  have wr₄ : u₄.wr = s.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  refine wp_sd (a := F) (by decide) (by rw [g f hf5 hf6, hF, BitVec.add_zero]) hal
    (by rw [wr₄]; exact hw8) fun u₅ h₅ => ?_
  refine wp_li (by decide) fun u₆ h₆ => ?_
  refine wp_sb (a := F + BitVec.ofNat 64 8) (by decide) (by rw [h₆.other _ hf5, h₅.gpr, g f hf5 hf6, hF])
    (by rw [h₆.wr, h₅.wr, wr₄]; exact hw 8 (by decide)) fun u₇ h₇ => ?_
  refine wp_sb (a := F + BitVec.ofNat 64 9) (by decide) (by rw [h₇.gpr, h₆.other _ hf5, h₅.gpr, g f hf5 hf6, hF])
    (by rw [h₇.wr, h₆.wr, h₅.wr, wr₄]; exact hw 9 (by decide)) fun t ht => ?_
  refine k t ?_ ?_ ?_ ?_ fun r r5 r6 => ?_
  · have e8 : (u₆.gpr .a5).setWidth 8 = (0 : BitVec 8) := by rw [h₆.gpr]; rfl
    have e9 : (u₇.gpr c).setWidth 8 = BitVec.ofNat 8 cl := by
      rw [h₇.gpr, h₆.other _ hc5, h₅.gpr, g c hc5 hc6, hc]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [ht.mem, h₇.mem, h₆.mem, h₅.mem, e9, e8, v, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  · rw [ht.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [ht.wr, h₇.wr, h₆.wr, h₅.wr, wr₄]
  · rw [ht.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  · rw [ht.gpr, h₇.gpr, h₆.other r r5, h₅.gpr, g r r5 r6]

/-! ## The setup -/

/-- `Inv` from a state that differs from `s` only in `t0`, which the slots do not hold. -/
theorem _root_.VG.Proof.Ed25519.RISCV64.Whole.Inv.rebase {s u t : State} {F : Addr} {o : Nat} {rs : List Reg}
    {v : Reg → BitVec 64} {W : List Region}
    (h : Inv u F o rs v W t) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hg : ∀ r, r ≠ .t0 → u.gpr r = s.gpr r) (hsl : ∀ p ∈ slots o rs, p.1 ≠ .t0)
    (hm : u.mem = s.mem) :
    Inv s F o rs v W t where
  rd := h.rd.trans hrd
  wr := h.wr.trans hwr
  sp := h.sp.trans hsp
  regs := h.regs
  pres r hr hn := (h.pres r hr hn).trans (hg r fun e => by revert hr; rw [e]; decide)
  saved p hp := by rw [h.saved p hp, hg _ (hsl p hp)]
  frame := hm ▸ h.frame

/-- After the setup: the invariant, the header of `dom4` at `F`, and the copy of `pk`. -/
structure S1 (s t : State) : Prop where
  inv : SInv s t
  hdr : bytesAt t.mem (sF s) 10 = hdrBytes (s.gpr .a4).toNat
  pk : bytesAt t.mem (sF s + BitVec.ofNat 64 384) 57 = bytesAt s.mem (s.gpr .a2) 57

theorem slot_sub (F : Addr) : Region.Sub (slotArea F 448 signRegs) ⟨F, 520⟩ := Offset.sub_base _ (by decide)

theorem slot_hdr (F : Addr) : (slotArea F 448 signRegs).Disjoint ⟨F, 10⟩ :=
  Offset.disjoint_base _ (by decide) (by decide)

theorem signSetup_eq : signSetup = saveRegs .t0 448 signRegs ++
    ([(.s0, .a0), (.s1, .a7), (.s2, .a1), (.s7, .a3), (.s8, .a4), (.s9, .a5), (.s10, .a6), (.s11, .t0)] :
      List (Reg × Reg)).map (fun p => mov p.1 p.2) ++ (copyIn .a2 .s11 384 57 ++ hdr .s11 .s8) := by
  simp only [signSetup, List.append_assoc]; rfl

theorem signSetup_ok {s u : State} (hp : SignPre s) (hu : Upd s u .t0 (sF s)) :
    WP isa (.block signSetup) u (S1 s) := by
  have hFw : (fR s) ∈ u.wr := by rw [hu.wr, hp.wr]; simp
  have hug : ∀ r, r ≠ .t0 → u.gpr r = s.gpr r := hu.other
  rw [signSetup_eq]
  refine setup_ok (v := signV s) (W := signW s) (by rw [hu.gpr]; exact hp.alF) (by decide) (by decide)
    (fun p hp' => by rw [hu.gpr]; exact in_base hFw (by revert p; decide) (by revert p; decide))
    ⟨fR s, by simp, by rw [hu.gpr]; exact slot_sub _⟩ rfl (by decide) (by decide) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hu.gpr.symm | exact (hug _ (by decide)).symm) fun t₁ h₁ g₁ => ?_
  rw [hu.gpr] at h₁
  have h₁' : SInv s t₁ := h₁.rebase hu.rd hu.wr hu.sp hug (by decide) hu.mem
  have g11 : t₁.gpr .s11 = sF s := h₁'.regs _ (by decide)
  have g8 : t₁.gpr .s8 = s.gpr .a4 := h₁'.regs _ (by decide)
  have g2 : t₁.gpr .a2 = s.gpr .a2 := by rw [g₁ _ (by decide), hug _ (by decide)]
  have hFw₁ : (fR s) ∈ t₁.wr := by rw [h₁'.wr, hp.wr]; simp
  have hP : (pkR s) ∈ t₁.rd := by rw [h₁'.rd, hp.rd]; simp
  -- `pk`, copied to `384(F)`.
  refine copyIn_ok (P := s.gpr .a2) (F := sF s) (o := 384) (n := 57) (by decide) (by decide) g2 g11 (by decide)
    (fun i hi => in_base (List.mem_append_left _ hP) (by omega) (by omega))
    (fun i hi => in_base hFw₁ (by omega) (by omega))
    (hp.fP.symm.sub_right (Offset.sub_base _ (by decide))) fun t₂ r₂ f₂ b₂ => ?_
  have h₂ : SInv s t₂ := h₁'.step signRegs_pres r₂.rd r₂.wr r₂.sp
    (fun r hr => r₂.gpr r fun e => by rw [List.mem_singleton] at e; revert hr; rw [e]; decide) f₂
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, Offset.sub_base _ (by decide)⟩)
    fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have hFw₂ : (fR s) ∈ t₂.wr := by rw [h₂.wr, hp.wr]; simp
  -- The header.
  refine hdr_ok (F := sF s) (cl := (s.gpr .a4).toNat) (by decide) (by decide)
    (by rw [h₂.regs _ (by decide)]; rfl) (by rw [h₂.regs _ (by decide)]; exact (ofNat_toNat _).symm)
    (fun j hj => in_base hFw₂ (by omega) (by omega))
    (by simpa using in_base (d := 0) (n := 8) hFw₂ (by decide) (by decide)) hp.alF (by decide) (by decide)
    fun t ht hrd hwr hsp hg => WP.block_nil ⟨?_, ?_, ?_⟩
  · refine h₂.step signRegs_pres hrd hwr hsp
      (fun r hr => hg r (fun e => by revert hr; rw [e]; decide) fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact slot_hdr _
  · rw [ht, hdrMem_bytes]
  · have hk := bytes_keep (W := [⟨sF s, 10⟩]) (ht ▸ hdrMem_frame _ _ _) (p := sF s + BitVec.ofNat 64 384) (n := 57)
      (by decide) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
    rw [show bytesAt t.mem (sF s + BitVec.ofNat 64 384) 57 =
        Spec.Sha3.bytesAt t.mem (sF s + BitVec.ofNat 64 384) 57 from rfl, hk]
    show Spec.Ed25519.bytesAt t₂.mem _ 57 = _
    rw [b₂]
    show Spec.Sha3.bytesAt t₁.mem (s.gpr .a2) 57 = Spec.Sha3.bytesAt s.mem (s.gpr .a2) 57
    refine bytes_keep h₁'.frame (by decide) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.oP.symm
    · exact hp.cP.symm
    · exact hp.fP.symm
    · exact hp.bP.symm

end VG.Proof.Ed448.RISCV64.Whole
