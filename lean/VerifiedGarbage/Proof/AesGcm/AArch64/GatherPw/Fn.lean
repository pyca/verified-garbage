module

public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.GatherPw.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM out of place from a list of slices, with the powers, AArch64: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_with_powers`
allocates its frame of 32 bytes, at `B + 2592` with `B` the base of the 2624
bytes of stack below the stack pointer (`sp = B + 2624`), keeps `tag` and
`pw`, the call's stack arguments, at `B + 2592` and `B + 2600`, and our
return address at `B + 2608` (`entered_wp`), gathers the slices to `dst`
as `vg_aes_gcm_seal_gather` does (`gather_wp`), and calls
`vg_aes_gcm_seal_with_powers` on them in place, with the powers, which
nothing before the call writes (`powers_gMem`); the call keeps our frame, so
the return address comes back from it (`sealGatherPw_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.GatherPw

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather VG.WriteBytes
open VG.Proof.AesGcm.AArch64.Gather (K Nn NL Ad AL Src Cnt Dst L Tg nR aR dsR lsR dR tgR gl pt gatherPost GatherPre
  gather_wp ldrSp_ok gatherRegs contains_off add_ofNat_sub_ofNat)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen Powers8Repr)
open VG.Proof.AesGcm.AArch64 (bytesAt_frame blockAt_frame covers_of_mem covers_cons covers_append covers_prefix)

/-- The entry, in the frame at `P`: our return address at `P + 16`, the
stack arguments at `P + 48` (`tag`) and `P + 56` (`pw`) at `P` and `P + 8`,
and the one at `P + 32` (`dst`) in `x11`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.sp = P)
    (w₁₆ : InRegions a.wr (P + BitVec.ofNat 64 16) 8) (w₀ : InRegions a.wr P 8)
    (w₈ : InRegions a.wr (P + BitVec.ofNat 64 8) 8)
    (r₄₈ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 48) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8)
    (r₃₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 32) 8) :
    WP isa (.block entryPw) a fun e =>
      e.mem = ((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).write P 8
          ((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).read (P + BitVec.ofNat 64 48) 8)).write
        (P + BitVec.ofNat 64 8) 8
          (((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).write P 8
            ((a.mem.write (P + BitVec.ofNat 64 16) 8 (a.gpr .x30)).read (P + BitVec.ofNat 64 48) 8)).read
              (P + BitVec.ofNat 64 56) 8) ∧
      e.gpr .x11 = e.mem.read (P + BitVec.ofNat 64 32) 8 ∧
      (∀ r, r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  subst hsp
  have e₀ : a.sp + BitVec.ofNat 64 0 = a.sp := BitVec.add_zero _
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [entryPw, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, sp_write, Option.bind_some,
      Option.map_some, BitVec.setWidth_eq, e₀, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul,
      Nat.reduceMod, and_self, w₁₆, w₀, w₈, r₄₈, r₅₆, r₃₂]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨rfl, by simp [State.write], fun r h₁ h₂ h₃ => by simp [State.write, h₁, h₂, h₃], rfl, rfl, rfl⟩

/-- `callArgsPw`: the stack arguments at `sp + 32` and `sp + 40` into `x6` and `x7`. -/
theorem callArgs_ok (a : State) (r₃₂ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 32) 8)
    (r₄₀ : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 40) 8) :
    WP isa (.block callArgsPw) a fun e => e.gpr .x6 = a.mem.read (a.sp + BitVec.ofNat 64 32) 8 ∧
      e.gpr .x7 = a.mem.read (a.sp + BitVec.ofNat 64 40) 8 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr ∧ e.v = a.v := by
  show WP isa (.block ([Instr.ldrSp .x6 32] ++ [Instr.ldrSp .x7 40])) a _
  refine WP.block_append (WP.mono (ldrSp_ok (t := .x6) a (by decide) r₃₂) fun e ⟨g₆, g, m, sp, rd, wr, v⟩ => ?_)
  refine WP.mono (ldrSp_ok (t := .x7) e (by decide) (by rw [rd, wr, sp]; exact r₄₀))
    fun e' ⟨g₇, g', m', sp', rd', wr', v'⟩ => ?_
  refine ⟨by rw [g' _ (by decide), g₆], by rw [g₇, m, sp], fun r h₁ h₂ => by rw [g' r h₂, g r h₁], by rw [m', m],
    by rw [sp', sp], by rw [rd', rd], by rw [wr', wr], by rw [v', v]⟩

theorem stackArgAddr_eq (s : State) {B : Addr} (hB : s.sp = B + BitVec.ofNat 64 2624) (i : Nat) :
    stackArgAddr s i = B + BitVec.ofNat 64 (2624 + 8 * i) := by
  rw [stackArgAddr, hB, Offset.add_ofNat_add_ofNat]

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 2624 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 2624

/-- The frame. -/
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 2592, 32⟩

/-- The memory after the entry: the return address at `Bs + 2608`, `tag` at
`Bs + 2592` and `pw` at `Bs + 2600`. -/
abbrev eMem : Mem :=
  ((s.mem.write (Bs s + BitVec.ofNat 64 2608) 8 (s.gpr .x30)).write (Bs s + BitVec.ofNat 64 2592) 8 (Tg s)).write
    (Bs s + BitVec.ofNat 64 2600) 8 (Pw s)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_aes_gcm_seal_with_powers` reads and writes. -/
abbrev rdC : List Region := [ctxR s, nR s, aR s, pwR s, ⟨Bs s + BitVec.ofNat 64 2592, 16⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 2624
  hBn : (Bs s).toNat + 2656 ≤ 2 ^ 64
  bk : (⟨Bs s, 2624⟩ : Region).Disjoint (ctxR s)
  bn : (⟨Bs s, 2624⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 2624⟩ : Region).Disjoint (aR s)
  bp : (⟨Bs s, 2624⟩ : Region).Disjoint (pwR s)
  bds : (⟨Bs s, 2624⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 2624⟩ : Region).Disjoint r
  bd : (⟨Bs s, 2624⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 2624⟩ : Region).Disjoint (tgR s)
  hargR : argsR s = ⟨Bs s + BitVec.ofNat 64 2624, 32⟩
  w₁ : 2624 ≤ s.sp.toNat
  hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  sig_split hs
  rename_i rd wr kd kt nd nt ad at_ dsd dst lsdt pd ptg dt darg targ bk bn ba bds bl bp barg bd bt ok on oa ods ol
    op od ot w₁ w₂ hR
  have hgl := hs
  clear hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 2624 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 2656 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega
  exact ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, pd, ptg, dt, darg, targ, bk, bn, ba, bds, bl, bp, barg,
    bd, bt, ok, on, oa, ods, ol, op, od, ot, w₁, w₂, hR, hgl⟩, hB, hBn, bk, bn, ba, bp, bds, bl, bd, bt,
    by simp only [argsR, stackArgAddr_eq s hB, Nat.mul_zero, Nat.add_zero], w₁, hR, hgl, ods⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2624) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2624⟩ :=
  Offset.sub_base _ h'

theorem frame_eMem (s : State) : Frame [FR s] s.mem (eMem s) :=
  (((Frame.refl _ _).write (List.mem_singleton_self _) _
    (contains_off _ (by decide) (by decide) (by decide))).write (List.mem_singleton_self _) _
    (by simp [Region.Contains])).write (List.mem_singleton_self _) _
    (contains_off _ (by decide) (by decide) (by decide))

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (2624 + 8 * i) := stackArgAddr_eq s h.hB i

theorem argIn : argsR s ∈ s.rd := by rw [h.pre.1]; simp

theorem inArg (d : Nat) (h₁ : 2624 ≤ d) (h₂ : d + 8 ≤ 2656) (rs : List Region) :
    InRegions (s.rd ++ rs) (Bs s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_append_left _ h.argIn, by rw [h.hargR]; exact contains_off _ h₁ (by omega) (by omega)⟩

theorem sa (i : Nat) : s.mem.read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.hA]; rfl

theorem sep (d e : Nat) (h₁ : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2656) (he : e + 8 ≤ 2656) :
    Mem.Sep (Bs s + BitVec.ofNat 64 d) 8 (Bs s + BitVec.ofNat 64 e) 8 :=
  Offset.sep _ h₁ (by have := h.hBn; omega) (by have := h.hBn; omega)

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 2624⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 2592 32 (by decide) x hc)

theorem eArg (i : Nat) (hi : i < 4) : (eMem s).read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [Mem.read_write_sep (h.sep _ 2600 (by omega) (by omega) (by decide)) (by decide),
    Mem.read_write_sep (h.sep _ 2592 (by omega) (by omega) (by decide)) (by decide),
    Mem.read_write_sep (h.sep _ 2608 (by omega) (by omega) (by decide)) (by decide)]
  exact h.sa i

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

theorem gArg (i : Nat) (hi : i < 4) : (gMem s).read (Bs s + BitVec.ofNat 64 (2624 + 8 * i)) 8 = stackArg s i := by
  rw [← h.eArg i hi]
  refine Frame.read h.frame_gMem (contains_off _ (Nat.le_refl _) (Nat.le_refl _) (by omega)) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, darg, -⟩ := h.pre
  rw [h.hargR] at darg
  exact (darg.sub_right (Offset.sub _ (show 2624 ≤ 2624 + 8 * i by omega) (by omega))).symm

/-- A doubleword of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd' : d + 8 ≤ 2624) :
    (gMem s).read (Bs s + BitVec.ofNat 64 d) 8 = (eMem s).read (Bs s + BitVec.ofNat 64 d) 8 :=
  Frame.read h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bd.symm.sub_right (stk_sub s d 8 hd') |>.symm) (by decide)

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  x11 : e.gpr .x11 = Dst s
  gpr : ∀ r, r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → e.gpr r = s.gpr r
  sp : e.sp = Bs s + BitVec.ofNat 64 2592
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (e.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem allocated_sp {s : State} (h : Lay s) : (allocated 32 s).sp = Bs s + BitVec.ofNat 64 2592 := by
  show s.sp - BitVec.ofNat 64 32 = _
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entryPw) (allocated 32 s) (Entered s) := by
  have asp := allocated_sp h
  have awr : (allocated 32 s).wr = FR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr : List Region) = _
    rw [show s.sp - BitVec.ofNat 64 32 = _ from asp]
  refine WP.mono (WP.preservedV (entry_ok (allocated 32 s) asp
      ⟨_, by rw [awr]; exact List.mem_cons_self .., Offset.contains_base _ (by decide) (by decide)⟩
      ⟨_, by rw [awr]; exact List.mem_cons_self .., by simp [Region.Contains]⟩
      ⟨_, by rw [awr]; exact List.mem_cons_self .., Offset.contains_base _ (by decide) (by decide)⟩
      (by rw [Offset.add_ofNat_add_ofNat]; exact h.inArg 2640 (by decide) (by decide) _)
      (by rw [Offset.add_ofNat_add_ofNat]; exact h.inArg 2648 (by decide) (by decide) _)
      (by rw [Offset.add_ofNat_add_ofNat]; exact h.inArg 2624 (by decide) (by decide) _)) (by lit_decide))
    fun e ⟨⟨me, x11e, ge, spe, rde, wre⟩, ve⟩ => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd] at me x11e
  change e.mem = (((s.mem.write (Bs s + BitVec.ofNat 64 2608) 8 (s.gpr .x30)).write (Bs s + BitVec.ofNat 64 2592) 8
      ((s.mem.write (Bs s + BitVec.ofNat 64 2608) 8 (s.gpr .x30)).read (Bs s + BitVec.ofNat 64 2640) 8)).write
    (Bs s + BitVec.ofNat 64 2600) 8
      (((s.mem.write (Bs s + BitVec.ofNat 64 2608) 8 (s.gpr .x30)).write (Bs s + BitVec.ofNat 64 2592) 8
        ((s.mem.write (Bs s + BitVec.ofNat 64 2608) 8 (s.gpr .x30)).read (Bs s + BitVec.ofNat 64 2640) 8)).read
          (Bs s + BitVec.ofNat 64 2648) 8)) at me
  rw [Mem.read_write_sep (h.sep 2648 2592 (by decide) (by decide) (by decide)) (by decide),
    Mem.read_write_sep (h.sep 2648 2608 (by decide) (by decide) (by decide)) (by decide),
    Mem.read_write_sep (h.sep 2640 2608 (by decide) (by decide) (by decide)) (by decide), h.sa 2, h.sa 3] at me
  refine ⟨me, ?_, ge, by rw [spe, asp], rde, by rw [wre, awr], ve⟩
  rw [x11e, me]
  exact h.eArg 0 (by decide)

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, pd, ptg, dt, darg, targ, bk, bn, ba, bds, bl, bp, barg,
    bd, bt, ok, on, oa, ods, ol, op, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) (Lay.hag h)
  rw [← he.mem] at hls
  exact { x6 := he.gpr _ (by decide) (by decide) (by decide)
          x7 := by rw [he.gpr _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
          x11 := he.x11
          hcnt := (s.gpr .x7).isLt
          dw := ods
          lt := (stackArg s 1).isLt
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) (Lay.hag h)]; exact hgl
          dsr := covers_of_mem (List.mem_append_left _ (by rw [he.rd]; show dsR s ∈ s.rd; rw [rd]; simp))
          lsr := fun r hr => covers_of_mem (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd]; show r ∈ s.rd; rw [rd]; simp [hr]))
          dw' := covers_of_mem (by rw [he.wr, wr]; simp)
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gMem s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → g.gpr r = s.gpr r
  sp : g.sp = Bs s + BitVec.ofNat 64 2592
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (g.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa gather e (Gathered s) := by
  refine WP.mono (WP.preservedV (gather_wp e (gatherPre_of h he)) (by lit_decide)) fun g ⟨⟨mg, kg⟩, vg⟩ => ?_
  rw [he.mem, Lay.hpt h] at mg
  exact ⟨mg, fun r hg h₁₁ h₁₆ h₁₇ => (kg.gpr r hg).trans (he.gpr r h₁₁ h₁₆ h₁₇), kg.sp.trans he.sp,
    kg.rd.trans he.rd, kg.wr.trans he.wr, fun r hr => (vg r hr).trans (he.v r hr)⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  x6 : c.gpr .x6 = Dst s
  x7 : c.gpr .x7 = stackArg s 1
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → r ∉ gatherRegs → r ≠ .x11 → r ≠ .x16 → r ≠ .x17 → c.gpr r = s.gpr r
  sp : c.sp = Bs s + BitVec.ofNat 64 2592
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (c.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgsPw) g (Ready s) := by
  refine WP.mono (callArgs_ok g
      (by rw [hg.sp, Offset.add_ofNat_add_ofNat, hg.rd, hg.wr]; exact h.inArg 2624 (by decide) (by decide) _)
      (by rw [hg.sp, Offset.add_ofNat_add_ofNat, hg.rd, hg.wr]; exact h.inArg 2632 (by decide) (by decide) _))
    fun c ⟨x6c, x7c, gc, mc, spc, rdc, wrc, vc⟩ => ?_
  rw [hg.sp, Offset.add_ofNat_add_ofNat, hg.mem] at x6c x7c
  exact ⟨mc.trans hg.mem, x6c.trans (h.gArg 0 (by decide)), x7c.trans (h.gArg 1 (by decide)),
    fun r h₆ h₇ hr h₁₁ h₁₆ h₁₇ => (gc r h₆ h₇).trans (hg.gpr r hr h₁₁ h₁₆ h₁₇), spc.trans hg.sp,
    rdc.trans hg.rd, wrc.trans hg.wr, fun r hr => by rw [vc]; exact hg.v r hr⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .x0 = s.gpr .x0 ∧ c.callEntry.gpr .x1 = s.gpr .x1 ∧ c.callEntry.gpr .x2 = s.gpr .x2 ∧
      c.callEntry.gpr .x3 = s.gpr .x3 ∧ c.callEntry.gpr .x4 = s.gpr .x4 ∧ c.callEntry.gpr .x5 = s.gpr .x5 ∧
      c.callEntry.gpr .x6 = Dst s ∧ c.callEntry.gpr .x7 = stackArg s 1 := by
  have cg (r : Reg) (h₀ : r ∉ linkRegs) (h₆ : r ≠ .x6) (h₇ : r ≠ .x7) (hg : r ∉ gatherRegs) (h₁₁ : r ≠ .x11)
      (h₁₆ : r ≠ .x16) (h₁₇ : r ≠ .x17) : c.callEntry.gpr r = s.gpr r := by
    rw [c.callEntry_gpr h₀, hc.gpr r h₆ h₇ hg h₁₁ h₁₆ h₁₇]
  exact ⟨cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    cg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [c.callEntry_gpr (by decide), hc.x6], by rw [c.callEntry_gpr (by decide), hc.x7]⟩

/-- `tag` and `pw`, the call's stack arguments. -/
theorem Ready.stackArgs {s c : State} (h : Lay s) (hc : Ready s c) (rd' wr' : List Region) :
    stackArg ((c.callEntry).withRegions rd' wr') 0 = Tg s ∧
      stackArg ((c.callEntry).withRegions rd' wr') 1 = Pw s := by
  have cTg : c.mem.read (Bs s + BitVec.ofNat 64 2592) 8 = Tg s := by
    rw [hc.mem, h.gFrame 2592 (by decide),
      Mem.read_write_sep (h.sep 2592 2600 (by decide) (by decide) (by decide)) (by decide)]
    exact read_write_self _ _ _
  have cPw : c.mem.read (Bs s + BitVec.ofNat 64 2600) 8 = Pw s := by
    rw [hc.mem, h.gFrame 2600 (by decide)]
    exact read_write_self _ _ _
  refine ⟨?_, ?_⟩
  · rw [← cTg, ← hc.sp]; simp [stackArg, stackArgAddr, Mem.readW]
  · rw [← cPw, show Bs s + BitVec.ofNat 64 2600 = c.sp + BitVec.ofNat 64 8 by
      rw [hc.sp, Offset.add_ofNat_add_ofNat]]
    simp [stackArg, stackArgAddr, Mem.readW]

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, pd, ptg, dt, darg, targ, -, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, op, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  obtain ⟨sa0, sa1⟩ := hc.stackArgs h (rdC s) (wrC s)
  have sad0 : stackArgAddr ((c.callEntry).withRegions (rdC s) (wrC s)) 0 = Bs s + BitVec.ofNat 64 2592 := by
    simp [stackArgAddr, hc.sp]
  have hPn : (Bs s + BitVec.ofNat 64 2592).toNat = (Bs s).toNat + 2592 := by
    have := h.hBn
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c0, c1, c2, c3, c4, c5, c6, c7, sa0, sa1, sad0, hc.sp, BitVec.add_sub_cancel]
    have stkArg : (⟨Bs s, 2592⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2592, 16⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 2592) (e := 2592) (k := 16) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    refine ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, pd, ptg, dt, (h.bd.sub_left (stk_sub s 2592 16 (by decide))).symm,
      (h.bt.sub_left (stk_sub s 2592 16 (by decide))).symm, h.bk.sub_left (Region.sub_prefix (by decide)),
      h.bn.sub_left (Region.sub_prefix (by decide)), h.ba.sub_left (Region.sub_prefix (by decide)),
      h.bp.sub_left (Region.sub_prefix (by decide)),
      h.bd.sub_left (Region.sub_prefix (by decide)), h.bt.sub_left (Region.sub_prefix (by decide)), stkArg,
      ok, on, oa, od, ot, op, by omega, by have := h.hBn; omega, hR⟩
  · have inRd {r : Region} (h' : r ∈ [ctxR s, nR s, aR s, pwR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp
    have hfr : Covers [FR s] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, wr]; exact List.mem_cons_of_mem _ h'))
    exact covers_append (covers_cons (inRd (r := ctxR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) (covers_cons (inRd (r := pwR s) (by simp))
        (covers_cons (covers_prefix hfr (by decide)) Proof.AesGcm.AArch64.covers_nil)))))
      (covers_cons (hw' (by simp)) (covers_cons (hw' (by simp)) Proof.AesGcm.AArch64.covers_nil))
  · rw [hc.wr, wr]
    exact covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp)) Proof.AesGcm.AArch64.covers_nil)

/-- After the call. -/
structure Called (s s' : State) : Prop where
  ra : s'.mem.read (Bs s + BitVec.ofNat 64 2608) 8 = s.gpr .x30
  out : encryptWith (ctxCiph (gMem s) (K s) (s.gpr .x1).toNat) (ctxH (gMem s) (K s)) 16
      (bytesAt (gMem s) (Nn s) (NL s)) (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)
  gpr : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = Bs s + BitVec.ofNat 64 2592
  rd : s'.rd = s.rd
  wr : s'.wr = FR s :: s.wr
  v : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- The memory the call finds, changed since the entry only in the frame and at `dst`. -/
theorem frame_gMem' {s : State} (h : Lay s) : Frame [FR s, dR s] s.mem (gMem s) :=
  ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
    (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))

/-- The powers of the hash subkey, kept until the call: neither they nor the
key context are written before it. -/
theorem powers_gMem {s : State} (h : Lay s) (hp : Powers8Repr s.mem (Pw s) (ctxH s.mem (K s))) :
    Powers8Repr (gMem s) (Pw s) (ctxH (gMem s) (K s)) := by
  obtain ⟨-, -, kd, -, -, -, -, -, -, -, -, pd, -⟩ := h.pre
  have hfc := frame_gMem' h
  have apart {r : Region} (h₁ : (⟨Bs s, 2624⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right (stk_sub s 2592 32 (by decide))
    · exact h₂
  obtain ⟨-, hh⟩ := ctx_frame hfc (apart h.bk kd) h.hR
  rw [hh]
  refine Proof.AesGcm.powers8Repr_congr (fun i hi => hfc _ fun r hr hcon => ?_) hp
  have hx : (pwR s).Contains (Pw s + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (show i + 1 ≤ 128 by omega) (by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, op, -⟩ := h.pre; omega)
  exact apart h.bp pd r hr _ hx hcon

theorem called_wp (F : SealPwFn) {s c : State} (h : Lay s)
    (hp : Powers8Repr s.mem (Pw s) (ctxH s.mem (K s))) (hc : Ready s c) :
    WP isa (.call F.fn.name F.fn.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc.callGpr
  obtain ⟨sa0, sa1⟩ := hc.stackArgs h (rdC s) (wrC s)
  have hdep := F.depth
  have hinv : Powers8Repr (c.callEntry.withRegions (rdC s) (wrC s)).mem
      (stackArg (c.callEntry.withRegions (rdC s) (wrC s)) 1)
      (ctxH (c.callEntry.withRegions (rdC s) (wrC s)).mem ((c.callEntry.withRegions (rdC s) (wrC s)).gpr .x0)) := by
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0, sa1, hc.mem]
    exact powers_gMem h hp
  refine WP.callFV (name := F.fn.name) F.verified.1 (F.pre _ hcp hinv) hcov hw
    (fun s' rd' wr' sp' fr' pres' presV' post' => ?_) (by omega)
  have hpost := F.post _ _ post' (by simp only [State.withRegions_gpr, c1]; exact h.hR)
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, c4, c5, c6, c7,
    sa0, hc.mem] at hpost
  have hpres : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ∉ gatherRegs ∧ r ≠ .x11 ∧
      r ≠ .x16 ∧ r ≠ .x17 := by decide
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.read (Bs s + BitVec.ofNat 64 2608) 8 = s.gpr .x30 := by
    have e : c.mem.read (Bs s + BitVec.ofNat 64 2608) 8 = s.gpr .x30 := by
      rw [hc.mem, h.gFrame 2608 (by decide),
        Mem.read_write_sep (h.sep 2608 2600 (by decide) (by decide) (by decide)) (by decide),
        Mem.read_write_sep (h.sep 2608 2592 (by decide) (by decide) (by decide)) (by decide)]
      exact read_write_self _ _ _
    rw [← e]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.symm.sub_right (stk_sub s 2608 8 (by decide)) |>.symm
    · exact h.bt.symm.sub_right (stk_sub s 2608 8 (by decide)) |>.symm
    · simp only [below, hc.sp, add_ofNat_sub_ofNat _ (show 16 * F.fn.code.aarch64Depth ≤ 2592 by omega)]
      exact Offset.disjoint _ (.inr (by omega)) (by decide) (by have := h.hBn; omega)
  exact ⟨ra, hpost, fun r hr h30 => by
      obtain ⟨h₆, h₇, hg, h₁₁, h₁₆, h₁₇⟩ := hpres r hr h30
      rw [pres' r hr h30, hc.gpr r h₆ h₇ hg h₁₁ h₁₆ h₁₇],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr, fun r hr => (presV' r hr).trans (hc.v r hr)⟩

/-- The return address back in `x30`, and the frame freed. -/
theorem ret_wp {s s' : State} (h : Lay s) (hc : Called s s') :
    WP isa (.block [.ldrSp .x30 16]) s' fun z => abiPreserved s (freed 32 z) ∧ gatherPost s (freed 32 z) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, pd, ptg, dt, darg, targ, -, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, op, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  refine WP.mono (ldrSp_ok (t := .x30) (k := 16) s' (by decide) ?_) fun z ⟨x30z, gz, mz, spz, rdz, wrz, vz⟩ => ?_
  · rw [hc.sp, hc.rd, hc.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), contains_off _ (by decide) (by decide) (by decide)⟩
  rw [hc.sp, Offset.add_ofNat_add_ofNat, hc.ra] at x30z
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · -- The callee-saved registers.
    show z.gpr r = s.gpr r
    by_cases h30 : r = .x30
    · subst h30; exact x30z
    · rw [gz r h30, hc.gpr r hr h30]
  · -- The stack pointer.
    show z.sp + BitVec.ofNat 64 32 = s.sp
    rw [spz, hc.sp, Offset.add_ofNat_add_ofNat, h.hB]
  · -- The callee-saved vector registers.
    show (z.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
    rw [vz]; exact hc.v r hr
  · -- The ciphertext and the tag.
    show encryptWith _ _ 16 _ _ _ = (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
    rw [mz]
    have hfc : Frame [FR s, dR s] s.mem (gMem s) := frame_gMem' h
    have apart {r : Region} (h₁ : (⟨Bs s, 2624⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right (stk_sub s 2592 32 (by decide))
      · exact h₂
    obtain ⟨hc', hh⟩ := ctx_frame hfc (apart h.bk kd) hR
    have hn : bytesAt (gMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
      bytesAt_frame hfc (apart h.bn nd) (by omega)
    have ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      bytesAt_frame hfc (apart h.ba ad) (by omega)
    have hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← Lay.hlen h]
      exact bytesAt_writeBytes_self _ _ _ (by rw [Lay.hlen h]; exact (stackArg s 1).isLt)
    have := hc.out
    rw [hc', hh, hn, ha, hd] at this
    exact this

theorem sealGatherPw_wp (F : SealPwFn) {s : State} (hs : gatherPre s)
    (hp : Powers8Repr s.mem (Pw s) (ctxH s.mem (K s))) :
    WP isa (sealGatherPw F.fn) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp F h hp hc) fun s' hs' => ?_)
  exact ret_wp h hs'

end VG.Proof.AesGcm.AArch64.GatherPw
