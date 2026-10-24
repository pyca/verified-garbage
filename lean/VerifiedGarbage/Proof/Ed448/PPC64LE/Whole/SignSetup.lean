module

import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Spec.Ed448

/-!
# `vg_ed448_sign_cached` on PPC64LE: the setup

The contract by register (`SignPre`): `out` in `r3`, `seed` in `r4`, `pk`
in `r5`, the context in `r6` (`ctxlen` in `r7`), the message in `r8` (`len`
in `r9`), `scratch` in `r10`, and the frame `F` (464 bytes) the stack
argument at `sp + 96`. `F` is read into `r12` (`frame_ok`), the registers
saved at `384(F)`, the arguments moved to `r20`–`r25` and `r28`–`r30` (`out`,
`F` and `scratch`, which the steps after the hashes use, to `r20`–`r22`, which
no function called saves and restores), and
the first ten bytes of `dom4(0, C)` written at `F` (`signSetup_ok`, `hdr_ok`):
the invariant `Inv` holds from the entry state on (`SInv`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea saveG)
open VG.Spec.Ed448 (bytesAt)

/-! ## The regions -/

section
variable (s : State)

abbrev sF : Addr := stackArg s 0
abbrev oR : Region := ⟨s.gpr .r3, 114⟩
abbrev sdR : Region := ⟨s.gpr .r4, 57⟩
abbrev pkR : Region := ⟨s.gpr .r5, 57⟩
abbrev cxR : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev msR : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev scR : Region := ⟨s.gpr .r10, 8192⟩
abbrev fR : Region := ⟨sF s, 464⟩
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
  sp : 48 ≤ s.sp.toNat
  bO : (below s.sp 48).Disjoint (oR s)
  bS : (below s.sp 48).Disjoint (sdR s)
  bP : (below s.sp 48).Disjoint (pkR s)
  bX : (below s.sp 48).Disjoint (cxR s)
  bM : (below s.sp 48).Disjoint (msR s)
  bC : (below s.sp 48).Disjoint (scR s)
  bF : (below s.sp 48).Disjoint (fR s)
  pk : bytesAt s.mem (s.gpr .r5) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .r4) 57)
  cl : (s.gpr .r7).toNat ≤ 255

/-- What the body may write. -/
abbrev signW (s : State) : List Region := [oR s, scR s, fR s, below s.sp 48]

/-- The values in the registers. -/
def signV (s : State) : Reg → BitVec 64
  | .r20 => s.gpr .r3 | .r23 => s.gpr .r4 | .r24 => s.gpr .r5 | .r25 => s.gpr .r6 | .r28 => s.gpr .r7
  | .r29 => s.gpr .r8 | .r30 => s.gpr .r9 | .r22 => s.gpr .r10 | .r21 => stackArg s 0 | _ => 0

abbrev SInv (s : State) : State → Prop := Inv s (sF s) 384 signRegs (signV s) (signW s)

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

theorem wp_oris {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (s.gpr n ||| imm.setWidth 64 <<< 16) → WP isa (.block is) s' Q) :
    WP isa (.block (.oris d n imm :: is)) s Q :=
  WP.cons exec_oris (k _ (Upd.write _ _ _))

/-- `F` read into `r12`. -/
theorem frame_ok {s : State} (hp : SignPre s) {Q : State → Prop}
    (k : ∀ u, Upd s u .r12 (sF s) → u.lr = s.lr → WP isa (.block []) u Q) : WP isa (.block signFrame) s Q := by
  unfold signFrame
  have hin : InRegions ((s.write .r12 (s.sp + BitVec.ofNat 64 0)).rd ++ (s.write .r12 (s.sp + BitVec.ofNat 64 0)).wr)
      ((s.write .r12 (s.sp + BitVec.ofNat 64 0)).gpr .r12 + BitVec.ofNat 64 96) 8 := by
    show InRegions (s.rd ++ s.wr) _ 8
    rw [show (s.write .r12 (s.sp + BitVec.ofNat 64 0)).gpr .r12 = s.sp + BitVec.ofNat 64 0 from
      (Upd.write _ _ _).gpr, BitVec.add_zero, hp.rd]
    exact ⟨aR s, by simp, Region.contains_self _ _⟩
  refine WP.cons (s' := s.write .r12 (s.sp + BitVec.ofNat 64 0)) (by
    show (if (0 : Nat) < 2 ^ 15 then some (s.write .r12 (s.sp + BitVec.ofNat 64 0)) else none) = _
    rw [ite_eq_left (by decide)]) (WP.cons (exec_load_d (by decide) (by decide) hin) (k _ ?_ rfl))
  have h₁ := Upd.write s .r12 (s.sp + BitVec.ofNat 64 0)
  have h₂ := Upd.write (s.write .r12 (s.sp + BitVec.ofNat 64 0)) .r12
    ((s.write .r12 (s.sp + BitVec.ofNat 64 0)).mem.readW
      ((s.write .r12 (s.sp + BitVec.ofNat 64 0)).gpr .r12 + BitVec.ofNat 64 96) 64)
  refine ⟨by rw [h₂.gpr, h₁.mem, h₁.gpr, BitVec.add_zero]; rfl, fun r hr => by rw [h₂.other r hr, h₁.other r hr],
    by rw [h₂.mem, h₁.mem], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr], by rw [h₂.sp, h₁.sp]⟩

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

theorem sig_value (x : BitVec 64) :
    (((((0x3834 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0x3464 : BitVec 16).setWidth 64) <<< 32 |||
      (0x4567 : BitVec 16).setWidth 64 <<< 16) ||| (0x6953 : BitVec 16).setWidth 64) = sigWord := by
  have := x; decide

/-- The header, from `r24 = ctxlen < 256`, at `F` in `r30`. -/
theorem hdr_ok {s : State} {f c : Reg} (hf0 : f ≠ .r0) (hf8 : f ≠ .r8) {F : Addr} {cl : Nat}
    (hF : s.gpr f = F) (hc : s.gpr c = BitVec.ofNat 64 cl) (hw : ∀ j < 10, InRegions s.wr (F + BitVec.ofNat 64 j) 1)
    (hw8 : InRegions s.wr F 8) (hc8 : c ≠ .r8) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.mem = hdrMem s.mem F cl → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      (∀ r, r ≠ .r8 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (hdr f c ++ is)) s Q := by
  unfold hdr
  simp only [List.cons_append, List.nil_append]
  refine wp_lis fun u₁ h₁ => wp_ori fun u₂ h₂ => wp_lsl (by decide) fun u₃ h₃ => wp_oris fun u₄ h₄ =>
    wp_ori fun u₅ h₅ => ?_
  have g : ∀ r, r ≠ .r8 → u₅.gpr r = s.gpr r := fun r hr => by
    rw [h₅.other r hr, h₄.other r hr, h₃.other r hr, h₂.other r hr, h₁.other r hr]
  have v : u₅.gpr .r8 = sigWord := by
    rw [h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr]; exact sig_value 0
  refine wp_stdd (a := F) hf0 (by decide) (by rw [g f hf8, hF, BitVec.add_zero])
    (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw8) fun u₆ h₆ => ?_
  refine wp_li (by decide) fun u₇ h₇ => ?_
  refine wp_stb (a := F + BitVec.ofNat 64 8) hf0 (by decide) (by rw [h₇.other _ hf8, h₆.gpr, g f hf8, hF])
    (by rw [h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 8 (by decide)) fun u₈ h₈ => ?_
  refine wp_stb (a := F + BitVec.ofNat 64 9) hf0 (by decide) (by rw [h₈.gpr, h₇.other _ hf8, h₆.gpr, g f hf8, hF])
    (by rw [h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 9 (by decide)) fun t ht => ?_
  refine k t ?_ ?_ ?_ ?_ fun r hr => ?_
  · have e8 : (u₇.gpr .r8).setWidth 8 = (0 : BitVec 8) := by rw [h₇.gpr]; rfl
    have e9 : (u₈.gpr c).setWidth 8 = BitVec.ofNat 8 cl := by
      rw [h₈.gpr, h₇.other _ hc8, h₆.gpr, g c hc8, hc]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [ht.mem, h₈.mem, h₇.mem, h₆.mem, e9, e8, v, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  · rw [ht.rd, h₈.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [ht.wr, h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  · rw [ht.sp, h₈.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  · rw [ht.gpr, h₈.gpr, h₇.other r hr, h₆.gpr, g r hr]

/-! ## The setup -/

/-- `Inv` from a state that agrees with `s` on what it records. -/
theorem _root_.VG.Proof.Ed25519.PPC64LE.Whole.Inv.rebase {s u t : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W : List Region}
    (h : Inv u F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.lr = s.lr) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hm : u.mem = s.mem) :
    Inv s F o rs v W t where
  rd := h.rd.trans hrd
  wr := h.wr.trans hwr
  sp := h.sp.trans hsp
  regs := h.regs
  pres r hr hn := (h.pres r hr hn).trans (hg r hr)
  saved p hp := by
    rw [h.saved p hp]
    obtain ⟨⟨r, i⟩, hm', rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, hlt, he⟩ := List.mem_zipIdx hm'
    have hm'' : r ∈ rs ++ [.r0] := by rw [he]; exact List.getElem_mem _
    simp only [saveG]
    by_cases h0 : r = .r0
    · simp only [h0, ↓reduceIte, hlr]
    · have hr : r ∈ rs := by
        rcases List.mem_append.mp hm'' with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') h0
      simp only [h0, ↓reduceIte, hg r (hrs r hr)]
  frame := hm ▸ h.frame

/-- After the setup: the invariant, and the header of `dom4` at `F`. -/
structure S1 (s t : State) : Prop where
  inv : SInv s t
  hdr : bytesAt t.mem (sF s) 10 = hdrBytes (s.gpr .r7).toNat

theorem slot_sub (F : Addr) : Region.Sub (slotArea F 384 signRegs) ⟨F, 464⟩ := Offset.sub_base _ (by decide)

theorem slot_hdr (F : Addr) : (slotArea F 384 signRegs).Disjoint ⟨F, 10⟩ :=
  Offset.disjoint_base _ (by decide) (by decide)

theorem signSetup_ok {s u : State} (hp : SignPre s) (hu : Upd s u .r12 (sF s)) (hlr : u.lr = s.lr) :
    WP isa (.block signSetup) u (S1 s) := by
  have hFw : (fR s) ∈ u.wr := by rw [hu.wr, hp.wr]; simp
  unfold signSetup
  refine (show WP isa (.block (saveRegs .r12 384 signRegs ++
      ([(.r20, .r3), (.r22, .r10), (.r23, .r4), (.r24, .r5), (.r25, .r6), (.r28, .r7), (.r29, .r8), (.r30, .r9),
        (.r21, .r12)] : List (Reg × Reg)).map (fun p => mov p.1 p.2) ++ hdr .r21 .r28)) u (S1 s) from ?_)
  refine setup_ok (v := signV s) (W := signW s) (by decide) (by decide) (by decide)
    (fun p hp' => by rw [hu.gpr]; exact in_base hFw (by revert p; decide) (by revert p; decide))
    ⟨fR s, by simp, by rw [hu.gpr]; exact slot_sub _⟩ rfl (by decide) (by decide) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hu.gpr.symm | exact (hu.other _ (by decide)).symm) fun t₁ h₁ => ?_
  rw [hu.gpr] at h₁
  have h₁' : SInv s t₁ := h₁.rebase signRegs_pres hu.rd hu.wr hu.sp hlr
    (fun r hr => hu.other r fun e => by revert hr; rw [e]; decide) hu.mem
  have g30 : t₁.gpr .r21 = sF s := h₁'.regs _ (by decide)
  have g24 : t₁.gpr .r28 = s.gpr .r7 := h₁'.regs _ (by decide)
  have hFw₁ : (fR s) ∈ t₁.wr := by rw [h₁'.wr, hp.wr]; simp
  refine hdr_ok (F := sF s) (cl := (s.gpr .r7).toNat) (by decide) (by decide) g30
    (by rw [g24, ofNat_toNat]) (fun j hj => in_base hFw₁ (by omega) (by omega))
    (by simpa using in_base (d := 0) (n := 8) hFw₁ (by decide) (by decide)) (by decide)
    fun t ht hrd hwr hsp hg => WP.block_nil ⟨?_, ?_⟩
  · refine h₁'.step signRegs_pres hrd hwr hsp (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact slot_hdr _
  · rw [ht, hdrMem_bytes]

end VG.Proof.Ed448.PPC64LE.Whole
