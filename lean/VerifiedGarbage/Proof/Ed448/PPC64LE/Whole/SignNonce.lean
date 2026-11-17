module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Spec.Ed448

/-! ### `Ed448.PPC64LE.Whole.SignSteps`, which this module and modules that import it used -/

section

/-! ### `Ed448.PPC64LE.Whole.SignSetup`, which this module and modules that import it used -/

section

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
      off_ne F (by omega_using [hi']) (by omega_using [hj]) h
    unfold hdrMem
    rw [Proof.Sha3.writeW8_apply, Proof.Sha3.writeW8_apply]
    by_cases h9 : i = 9
    · subst h9; simp [hdrBytes]
    by_cases h8 : i = 8
    · subst h8; simp [hdrBytes]
    rw [ite_eq_right (ne 9 (by decide) h9), ite_eq_right (ne 8 (by decide) h8)]
    have hi8 : i < 8 := by omega_using [hi', h9, h8]
    simp only [Mem.writeW, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi']), show i < 64 / 8 by omega_using [hi', h9, h8], ↓reduceIte, BitVec.setWidth_eq]
    rw [sigWord_bytes i hi8]
    simp only [hdrBytes, List.getElem_append_left (by simp; omega_using [hi', h9, h8] : i < ("SigEd448".toList.map _).length)]
    rw [List.getElem?_eq_getElem (by simp; omega_using [hi', h9, h8]), Option.getD_some]

theorem hdrMem_frame (m : Mem) (F : Addr) (c : Nat) : Frame [⟨F, 10⟩] m (hdrMem m F c) := by
  have h : ∀ j, j + 1 ≤ 10 → (⟨F, 10⟩ : Region).Contains (F + BitVec.ofNat 64 j) (8 / 8) := fun j hj =>
    Offset.contains_base F (by omega_using [hj]) (by omega_using [hj])
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
      omega_using []
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
    (by rw [g24, ofNat_toNat]) (fun j hj => in_base hFw₁ (by omega_using [hj]) (by omega_using [hj]))
    (by simpa using in_base (d := 0) (n := 8) hFw₁ (by decide) (by decide)) (by decide)
    fun t ht hrd hwr hsp hg => WP.block_nil ⟨?_, ?_⟩
  · refine h₁'.step signRegs_pres hrd hwr hsp (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact slot_hdr _
  · rw [ht, hdrMem_bytes]

end VG.Proof.Ed448.PPC64LE.Whole

end

end

/-!
# `vg_ed448_sign_cached` on PPC64LE: the steps

From the setup's invariant (`S1`): `SHAKE256(seed, 114)` into `136(F)`, its
first half pruned there (`S2`, `expand_ok`); the nonce `r` reduced into
`256(F)` and `R = [r]B` into the first half of `out` (`S3`, `nonce_ok`); the
challenge `k` into `320(F)` and `S = (r + k s) mod L` into the second half of
`out` (`S4`, `challenge_ok`). The pieces of the hashes (`pieceOk_of`) and the
regions written are those of `SignPre`.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea)
open VG.Spec.Ed448 (bytesAt)

theorem bytesAt_sha3 (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.bytesAt m p n = bytesAt m p n := rfl

theorem pieceOk_of {t : State} {sc : Addr} {p : Piece} {R : Region} (hR : p.R t.gpr = R) (hb : p.base ∈ preserved)
    (ho : p.off < 2 ^ 15) (hl : p.len.Ok) (hc : PPC64LE.Covers [R] (t.rd ++ t.wr))
    (hd : R.Disjoint ⟨sc, 8192⟩) (hb' : (below t.sp 48).Disjoint R) : PieceOk sc t p :=
  ⟨hb, ho, hl, hR ▸ hc, hR ▸ hd, hR ▸ hb'⟩

theorem cov_in {ws : List Region} {P : Addr} {k d n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : d + n ≤ k) :
    PPC64LE.Covers [⟨P + BitVec.ofNat 64 d, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, d, rfl, h⟩

theorem cov_in0 {ws : List Region} {P : Addr} {k n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : n ≤ k) :
    PPC64LE.Covers [⟨P, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, 0, by simp, by simpa using h⟩

theorem cov_rd {rd wr ws : List Region} (h : PPC64LE.Covers ws rd) : PPC64LE.Covers ws (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_left _ hr, hc⟩

theorem fsub {s : State} {d n : Nat} (h : d + n ≤ 464) : Region.Sub ⟨sF s + BitVec.ofNat 64 d, n⟩ (fR s) := Offset.sub_base _ h

theorem fslot {s : State} {d n : Nat} (h : d + n ≤ 384) : (slotArea (sF s) 384 signRegs).Disjoint ⟨sF s + BitVec.ofNat 64 d, n⟩ :=
  Offset.disjoint _ (.inr h) (by decide) (by omega_using [h])

theorem osub {s : State} {d n : Nat} (h : d + n ≤ 114) : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 d, n⟩ (oR s) :=
  Offset.sub_base _ h

section
variable {s : State} (hp : SignPre s)
include hp

/-! ## Regions of the frame and of `out` -/

theorem fsc {d n : Nat} (h : d + n ≤ 464) : Region.Disjoint ⟨sF s + BitVec.ofNat 64 d, n⟩ (scR s) :=
  hp.cF.symm.sub_left (fsub h)

theorem fbelow {d n : Nat} (h : d + n ≤ 464) : (below s.sp 48).Disjoint ⟨sF s + BitVec.ofNat 64 d, n⟩ :=
  hp.bF.sub_right (fsub h)

theorem oslot {d n : Nat} (h : d + n ≤ 114) :
    (slotArea (sF s) 384 signRegs).Disjoint ⟨s.gpr .r3 + BitVec.ofNat 64 d, n⟩ :=
  (hp.oF.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (osub h)

theorem cslot : (slotArea (sF s) 384 signRegs).Disjoint (scR s) := hp.cF.symm.sub_left (Offset.sub_base _ (by decide))

theorem bslot : (slotArea (sF s) 384 signRegs).Disjoint (below s.sp 48) := hp.bF.symm.sub_left (Offset.sub_base _ (by decide))

theorem fF {t : State} (h : SInv s t) : (fR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp
theorem fO {t : State} (h : SInv s t) : (oR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp
theorem fC {t : State} (h : SInv s t) : (scR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp

theorem kenv {t : State} (h : SInv s t) : KEnv (s.gpr .r10) t :=
  ⟨fC hp h, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

/-- A hash into `o(F)` keeps the invariant. -/
theorem SInv.hash {t t' : State} (h : SInv s t) {o : Nat} (ho : o + 114 ≤ 384)
    (hk : Kept ([⟨sF s + BitVec.ofNat 64 o, 114⟩] ++ kW (s.gpr .r10) t.sp) t t') : SInv s t' :=
  Inv.kept h signRegs_pres hk (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fR s, by simp, fsub (by omega_using [ho])⟩
    · exact ⟨scR s, by simp, fun _ h => h⟩
    · exact ⟨below s.sp 48, by simp, by rw [h.sp]; exact fun _ h => h⟩) fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fslot ho
    · exact cslot hp
    · rw [h.sp]; exact bslot hp

/-- Bytes of the frame apart from what a hash into `o(F)` writes. -/
theorem keep_hash {t t' : State} (h : SInv s t) {o d n : Nat} (hd : d + n ≤ o ∨ o + 114 ≤ d)
    (ho : o + 114 ≤ 464) (hdn : d + n ≤ 464)
    (hk : Kept ([⟨sF s + BitVec.ofNat 64 o, 114⟩] ++ kW (s.gpr .r10) t.sp) t t') :
    bytesAt t'.mem (sF s + BitVec.ofNat 64 d) n = bytesAt t.mem (sF s + BitVec.ofNat 64 d) n :=
  bytes_keep hk.frame (by omega_using [hdn]) fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ hd (by omega_using [hdn]) (by omega_using [ho])
    · exact fsc hp hdn
    · rw [h.sp]; exact (fbelow hp hdn).symm

end

/-! ## `s` and the prefix -/

/-- After `s` and the nonce's prefix. -/
structure S2 (s t : State) : Prop where
  inv : SInv s t
  hdr : bytesAt t.mem (sF s) 10 = hdrBytes (s.gpr .r7).toNat
  sc : Spec.Ed448.decodeLE (bytesAt t.mem (sF s + BitVec.ofNat 64 136) 57) =
    Spec.Ed448.prune (Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114)
  pre : bytesAt t.mem (sF s + BitVec.ofNat 64 193) 57 = (Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114).drop 57

theorem expand_ok {s t : State} (hp : SignPre s) (h : S1 s t) : WP isa signExpand t (S2 s) := by
  have g21 : t.gpr .r23 = s.gpr .r4 := h.inv.regs _ (by decide)
  have g29 : t.gpr .r22 = s.gpr .r10 := h.inv.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.inv.regs _ (by decide)
  have pk : PieceOk (s.gpr .r10) t ⟨.r23, 0, .imm 57⟩ :=
    pieceOk_of (R := sdR s) (by simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero]) (by decide)
      (by decide) (show 57 < 2 ^ 15 by decide)
      (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
      hp.cS.symm (by rw [h.inv.sp]; exact hp.bS)
  unfold signExpand
  refine WP.seq (WP.mono (hash_ok (sc := .r22) (f := .r21) (o := 136) (out := sF s + BitVec.ofNat 64 136)
    (by decide) (by decide) (by decide) g29 (by rw [g30]) (kenv hp h.inv) (by simp)
    (fun p hp' => by rw [List.mem_singleton.mp hp']; exact pk) (cov_in (fF hp h.inv) (by decide))
    (fsc hp (by decide)) (by rw [h.inv.sp]; exact fbelow hp (by decide))) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ := h.inv.hash hp (by decide) k₂
  have hh : bytesAt t₂.mem (sF s + BitVec.ofNat 64 136) 114 = Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114 := by
    have e := sign_keep hp h.inv (R := sdR s) (.inl rfl)
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes,
      Piece.addr, Len.val, g21, BitVec.add_zero, bytesAt_sha3] at d₂ e
    rw [d₂]; exact congrArg (Spec.Sha3.shake256 · 114) e
  refine prune_ok (f := .r21) (o := 136) (q := sF s + BitVec.ofNat 64 136) (is := []) (by decide) (by decide)
    (by decide) (by rw [h₂.regs _ (by decide)]; rfl)
    (fun j hj => by
      rw [h₂.wr, hp.wr, Offset.add_add]; exact in_base (P := sF s) (len := 464) (d := 136 + j) (by simp) (by omega_using [hj]) (by omega_using [hj]))
    fun u um usp urd uwr ug => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine h₂.step signRegs_pres urd uwr usp (fun r hr => ug r fun e => by revert hr; rw [e]; decide)
      (um ▸ pruned_frame _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, fsub (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact fslot (by decide)
  · have := keep_hash hp h.inv (o := 136) (d := 0) (n := 10) (by decide) (by decide) (by decide) k₂
    rw [BitVec.add_zero] at this
    rw [um, ← h.hdr, ← this]
    exact bytes_keep (pruned_frame _ _) (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.disjoint_base (sF s) (d := 136) (n := 57) (k := 10) (by decide) (by decide)).symm
  · rw [um, pruned_prune, hh]
  · rw [um, ← bytesAt_sha3, bytes_keep (pruned_frame _ _) (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint (sF s) (d := 193) (n := 57) (e := 136) (k := 57) (.inr (by decide)) (by decide) (by decide),
      show sF s + BitVec.ofNat 64 193 = sF s + BitVec.ofNat 64 136 + BitVec.ofNat 64 57 by rw [Offset.add_add],
      bytesAt_sha3, ← bytesAt_drop57, hh]

end VG.Proof.Ed448.PPC64LE.Whole

end

end

/-!
# `vg_ed448_sign_cached` on PPC64LE: the nonce and `R`

From `S2`: `H(dom4(0, C) ‖ prefix ‖ M)` into `16(F)`, reduced modulo `L`
into `256(F)` (`r`), and `R = [r]B` into the first half of `out`
(`nonce_ok`, `S3`). `dom4_hash` is the hash of the pieces the code absorbs.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea ArgsKeep args3_ok)
open VG.Spec.Ed448 (bytesAt)

section
variable (s : State)

/-- The inputs. -/
abbrev seedB : List Byte := bytesAt s.mem (s.gpr .r4) 57
abbrev ctxB : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev msgB : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev pkB : List Byte := bytesAt s.mem (s.gpr .r5) 57

/-- `SHAKE256(seed, 114)`, `r` and `R`. -/
abbrev hS : List Byte := Spec.Sha3.shake256 (seedB s) 114
abbrev rB : List Byte := Spec.Ed448.scalarReduce (Spec.Ed448.hash (ctxB s) ((hS s).drop 57 ++ msgB s))
abbrev RB : List Byte := Spec.Ed448.scalarBase (rB s)

end

/-- `dom4(0, C) ‖ x`, as the code absorbs it: the header, the context and `x`. -/
theorem dom4_hash (ctx x : List Byte) :
    Spec.Sha3.shake256 (hdrBytes ctx.length ++ ctx ++ x) 114 = Spec.Ed448.hash ctx x := by
  rw [Spec.Ed448.hash, dom4_eq, List.append_assoc]

/-- After `r` and `R`. -/
structure S3 (s t : State) : Prop where
  inv : SInv s t
  hdr : bytesAt t.mem (sF s) 10 = hdrBytes (s.gpr .r7).toNat
  sc : Spec.Ed448.decodeLE (bytesAt t.mem (sF s + BitVec.ofNat 64 136) 57) = Spec.Ed448.prune (hS s)
  r : bytesAt t.mem (sF s + BitVec.ofNat 64 256) 57 = rB s
  R : bytesAt t.mem (s.gpr .r3) 57 = RB s

section
variable {s : State} (hp : SignPre s)
include hp

theorem ctxPiece {t : State} (h : SInv s t) :
    PieceOk (s.gpr .r10) t ⟨.r25, 0, .reg .r28⟩ ∧ Piece.bytes t.mem t.gpr ⟨.r25, 0, .reg .r28⟩ = ctxB s := by
  have g23 : t.gpr .r25 = s.gpr .r6 := h.regs _ (by decide)
  have g24 : t.gpr .r28 = s.gpr .r7 := h.regs _ (by decide)
  have e : Piece.R t.gpr ⟨.r25, 0, .reg .r28⟩ = cxR s := by
    simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero]
  refine ⟨pieceOk_of e (by decide) (by decide) (show Reg.r28 ∈ preserved by decide)
    (by rw [h.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cX.symm (by rw [h.sp]; exact hp.bX), ?_⟩
  have := sign_keep hp h (R := cxR s) (.inr (.inr (.inl rfl)))
  simp only [Piece.bytes, Piece.addr, Len.val, g23, g24, BitVec.add_zero]
  exact this

theorem msgPiece {t : State} (h : SInv s t) :
    PieceOk (s.gpr .r10) t ⟨.r29, 0, .reg .r30⟩ ∧ Piece.bytes t.mem t.gpr ⟨.r29, 0, .reg .r30⟩ = msgB s := by
  have g25 : t.gpr .r29 = s.gpr .r8 := h.regs _ (by decide)
  have g28 : t.gpr .r30 = s.gpr .r9 := h.regs _ (by decide)
  have e : Piece.R t.gpr ⟨.r29, 0, .reg .r30⟩ = msR s := by
    simp only [Piece.R, Piece.addr, Len.val, g25, g28, BitVec.add_zero]
  refine ⟨pieceOk_of e (by decide) (by decide) (show Reg.r30 ∈ preserved by decide)
    (by rw [h.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cM.symm (by rw [h.sp]; exact hp.bM), ?_⟩
  have := sign_keep hp h (R := msR s) (.inr (.inr (.inr rfl)))
  simp only [Piece.bytes, Piece.addr, Len.val, g25, g28, BitVec.add_zero]
  exact this

/-- A piece of `F`. -/
theorem fPiece {t : State} (h : SInv s t) {d n : Nat} (hd : d < 2 ^ 15) (hn : n < 2 ^ 15) (hdn : d + n ≤ 464) :
    PieceOk (s.gpr .r10) t ⟨.r21, d, .imm n⟩ ∧
      Piece.bytes t.mem t.gpr ⟨.r21, d, .imm n⟩ = bytesAt t.mem (sF s + BitVec.ofNat 64 d) n := by
  have g30 : t.gpr .r21 = sF s := h.regs _ (by decide)
  have e : Piece.R t.gpr ⟨.r21, d, .imm n⟩ = ⟨sF s + BitVec.ofNat 64 d, n⟩ := by
    simp only [Piece.R, Piece.addr, Len.val, g30]
  refine ⟨pieceOk_of e (show Reg.r21 ∈ preserved by decide) hd hn (cov_right (cov_in (fF hp h) hdn)) (fsc hp hdn)
    (by rw [h.sp]; exact fbelow hp hdn), ?_⟩
  simp only [Piece.bytes, Piece.addr, Len.val, g30]; rfl

theorem fPiece0 {t : State} (h : SInv s t) :
    PieceOk (s.gpr .r10) t ⟨.r21, 0, .imm 10⟩ ∧
      Piece.bytes t.mem t.gpr ⟨.r21, 0, .imm 10⟩ = bytesAt t.mem (sF s) 10 := by
  have := fPiece hp h (d := 0) (n := 10) (by decide) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

/-- `scalar_reduce` of the hash at `16(F)` into `o(F)`. -/
theorem reduceF_ok {t : State} (h : SInv s t) {o : Nat} (ho : o + 57 ≤ 384) (ho' : 130 ≤ o) {rest : Prog isa}
    {Q : State → Prop}
    (k : ∀ t', SInv s t' →
      Frame [⟨sF s + BitVec.ofNat 64 o, 57⟩, scR s] t.mem t'.mem →
      bytesAt t'.mem (sF s + BitVec.ofNat 64 o) 57 =
        Spec.Ed448.scalarReduce (bytesAt t.mem (sF s + BitVec.ofNat 64 16) 114) → WP isa rest t' Q) :
    WP isa (.seq (.block [.addi .r3 .r21 o, .addi .r4 .r21 16, mov .r5 .r22])
      (.seq (.call "vg_ed448_scalar_reduce" Impl.Ed448.PPC64LE.scalarReduce) rest)) t Q := by
  have g29 : t.gpr .r22 = s.gpr .r10 := h.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.regs _ (by decide)
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by omega_using [ho]) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u hu a3 a4 a5 => ?_)
  rw [g30] at a3 a4
  rw [g29, BitVec.add_zero] at a5
  have hW : PPC64LE.Covers [⟨sF s + BitVec.ofNat 64 o, 57⟩, scR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in (fF hp h) (by omega_using [ho]) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, fC hp h, hc⟩
  refine WP.seq (reduce_call a3 a4 a5 (Offset.disjoint _ (.inr (by omega_using [ho'])) (by omega_using [ho]) (by omega_using [])) (fsc hp (by omega_using [ho]))
    (fsc hp (by decide)) (cov_app (cov_right (by rw [hu.wr]; exact cov_in (fF hp h) (by decide))) (cov_right hW)) hW
    fun t' rd' wr' sp' f' cs' r' => ?_)
  rw [hu.mem] at f' r'
  refine k t' (h.step signRegs_pres (rd'.trans hu.rd) (wr'.trans hu.wr) (sp'.trans hu.sp)
    (fun r hr => (cs' r hr).trans (hu.pres r hr)) f' (fun r hr => ?_) fun r hr => ?_) f' r'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fR s, by simp, fsub (by omega_using [ho])⟩
    · exact ⟨scR s, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fslot ho
    · exact cslot hp

end

theorem nonce_ok (hl : Proof.Ed448.BaseLadder2Ok) {s t : State} (hp : SignPre s) (h : S2 s t) : WP isa signNonce t (S3 s) := by
  obtain ⟨cP, cB⟩ := ctxPiece hp h.inv
  obtain ⟨mP, mB⟩ := msgPiece hp h.inv
  obtain ⟨hP, hB⟩ := fPiece0 hp h.inv
  obtain ⟨pP, pB⟩ := fPiece hp h.inv (d := 193) (n := 57) (by decide) (by decide) (by decide)
  have g29 : t.gpr .r22 = s.gpr .r10 := h.inv.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.inv.regs _ (by decide)
  unfold signNonce
  simp only [dom4Pieces, List.cons_append, List.nil_append]
  refine WP.seq (WP.mono (hash_ok (sc := .r22) (f := .r21) (o := 16) (out := sF s + BitVec.ofNat 64 16)
    (by decide) (by decide) (by decide) g29 (by rw [g30]) (kenv hp h.inv) (by simp) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl
      · exact hP
      · exact cP
      · exact pP
      · exact mP) (cov_in (fF hp h.inv) (by decide))
    (fsc hp (by decide)) (by rw [h.inv.sp]; exact fbelow hp (by decide))) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ := h.inv.hash hp (by decide) k₂
  have hh : bytesAt t₂.mem (sF s + BitVec.ofNat 64 16) 114 =
      Spec.Ed448.hash (ctxB s) ((hS s).drop 57 ++ msgB s) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, hB, cB, pB, mB,
      h.hdr, h.pre, bytesAt_sha3] at d₂
    rw [d₂, show (s.gpr .r7).toNat = (ctxB s).length by simp [bytesAt], ← List.append_assoc]
    exact dom4_hash _ _
  -- `r`.
  refine reduceF_ok hp h₂ (o := 256) (by decide) (by decide) fun t₃ h₃ f₃ r₃ => ?_
  rw [hh] at r₃
  -- `R`.
  have g20 : t₃.gpr .r20 = s.gpr .r3 := h₃.regs _ (by decide)
  have g29' : t₃.gpr .r22 = s.gpr .r10 := h₃.regs _ (by decide)
  have g30' : t₃.gpr .r21 = sF s := h₃.regs _ (by decide)
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u hu a3 a4 a5 => ?_)
  rw [g20, BitVec.add_zero] at a3
  rw [g30'] at a4
  rw [g29', BitVec.add_zero] at a5
  have hO57 : Region.Sub ⟨s.gpr .r3, 57⟩ (oR s) := Region.sub_prefix (by decide)
  have hW : PPC64LE.Covers [⟨s.gpr .r3, 57⟩, scR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in0 (fO hp h₃) (by decide) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, fC hp h₃, hc⟩
  refine base_call hl a3 a4 a5 ((hp.oF.sub_left hO57).sub_right (fsub (by decide)))
    (hp.oC.sub_left hO57) (fsc hp (by decide))
    (cov_app (cov_right (by rw [hu.wr]; exact cov_in (fF hp h₃) (by decide))) (cov_right hW)) hW
    fun t₄ rd₄ wr₄ sp₄ f₄ cs₄ b₄ => ?_
  rw [hu.mem] at f₄ b₄
  have h₄ : SInv s t₄ := h₃.step signRegs_pres (rd₄.trans hu.rd) (wr₄.trans hu.wr) (sp₄.trans hu.sp)
    (fun r hr => (cs₄ r hr).trans (hu.pres r hr)) f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨oR s, by simp, hO57⟩
      · exact ⟨scR s, by simp, fun _ h => h⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using oslot hp (d := 0) (n := 57) (by decide)
      · exact cslot hp
  -- What the steps keep.
  have kb : ∀ {d n : Nat}, d + n ≤ 464 → bytesAt t₄.mem (sF s + BitVec.ofNat 64 d) n =
      bytesAt t₃.mem (sF s + BitVec.ofNat 64 d) n := fun hdn =>
    bytes_keep f₄ (by omega_using [hdn]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hp.oF.sub_left hO57).sub_right (fsub hdn)).symm
      · exact fsc hp hdn
  have kr : ∀ {d n : Nat}, d + n ≤ 464 → (d + n ≤ 256 ∨ 313 ≤ d) →
      bytesAt t₃.mem (sF s + BitVec.ofNat 64 d) n = bytesAt t₂.mem (sF s + BitVec.ofNat 64 d) n :=
    fun hdn hd => bytes_keep f₃ (by omega_using [hdn]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hd]) (by omega_using [hdn]) (by omega_using [])
      · exact fsc hp hdn
  refine ⟨h₄, ?_, ?_, ?_, by rw [b₄, r₃]⟩
  · have a := kb (d := 0) (n := 10) (by decide)
    have b := kr (d := 0) (n := 10) (by decide) (by decide)
    have c := keep_hash hp h.inv (o := 16) (d := 0) (n := 10) (by decide) (by decide) (by decide) k₂
    rw [BitVec.add_zero] at a b c
    rw [a, b, c, h.hdr]
  · rw [kb (by decide), kr (by decide) (by decide),
      keep_hash hp h.inv (o := 16) (d := 136) (n := 57) (by decide) (by decide) (by decide) k₂, h.sc]
  · rw [kb (by decide), r₃]

end VG.Proof.Ed448.PPC64LE.Whole
