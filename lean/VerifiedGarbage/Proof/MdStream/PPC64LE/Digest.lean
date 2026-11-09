module

public import VerifiedGarbage.Impl.MdStream.PPC64LE.Digest
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Save
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Init
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.MdStream.DigestScratch

/-!
# The one-shot digest over any streaming hash function on PPC64LE: correct

`digestMain` (`Impl/MdStream/PPC64LE/Digest.lean`) saves our caller's
`r20`–`r25` after its buffers, hashes the message with the streaming `init`,
`update` and `finalize` (through their proofs, `HashOK.callInit_ok`,
`callUpd_ok` and `callFin_ok`) into its scratch space, laid out as HMAC's
`initLong`'s (`InitLong.lay`), copies the digest to `out` (`copy32_ok`) and
restores the registers (`correctMain`). `digestG` is the contract it is
verified against, with its working space as an argument: the functions it
calls use the 48 bytes below the frame it pushes (`correct`).
-/

@[expose] public section

namespace VG.Proof.MdStream.PPC64LE.Digest

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Impl.MdStream.PPC64LE.Digest (digestMain digest copyOut)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_addi contains_offset)
open VG.Proof.Hmac.Stream.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Init (cover_self cover_pre cover_off Regs)
open VG.Proof.Hmac.Stream.PPC64LE.InitLong (Lay lay wR_sub stR_sub dgR_sub svR_sub wI_st wI_dg wI_sv st_dg st_sv
  dg_sv)
open VG.Proof.Hmac.Stream.PPC64LE.Finalize (contains_start)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-! ## The contract -/

/-- `digest(data, len, out, scratch)`, with `Wi` bytes of scratch space and
`F` bytes of stack below the stack pointer. -/
def digestG (SH : StreamingHash) (Wi F : Nat) : Contract isa where
  pre s :=
    let data : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let out : Region := ⟨s.gpr .r5, SH.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r6, Wi⟩
    s.rd = [data] ∧ s.wr = [out, scratch] ∧
    data.Disjoint out ∧ data.Disjoint scratch ∧ out.Disjoint scratch ∧
    F ≤ s.sp.toNat ∧ (below s.sp F).Disjoint data ∧ (below s.sp F).Disjoint out ∧
    (below s.sp F).Disjoint scratch
  post s s' :=
    bytesAt s'.mem (s.gpr .r5) SH.digestBytes = SH.H.hash (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev dp : Addr := s₀.gpr .r3
abbrev dl : Nat := (s₀.gpr .r4).toNat
abbrev out : Addr := s₀.gpr .r5
abbrev scr : Addr := s₀.gpr .r6
abbrev dR : Region := ⟨dp s₀, dl s₀⟩
abbrev oR : Region := ⟨out s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, H.lbytes⟩
/-- The message. -/
abbrev M : List Byte := bytesAt s₀.mem (dp s₀) (dl s₀)

end

/-- `digestMain`'s precondition, with the stack pointer below its frame: the
functions it calls use the 48 bytes below it. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [oR H s₀, scR H s₀]
  d_o : (dR s₀).Disjoint (oR H s₀)
  d_s : (dR s₀).Disjoint (scR H s₀)
  o_s : (oR H s₀).Disjoint (scR H s₀)
  sp48 : 48 ≤ s₀.sp.toNat
  sd : (below s₀.sp 48).Disjoint (dR s₀)
  so : (below s₀.sp 48).Disjoint (oR H s₀)
  ss : (below s₀.sp 48).Disjoint (scR H s₀)

variable {H : Hash} (hH : HashOK H) {s₀ : State}

/-- Our variables in `r20`–`r24`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = scr s₀ + BitVec.ofNat 64 H.lst
  r21 : s.gpr .r21 = scr s₀
  r22 : s.gpr .r22 = out s₀
  r23 : s.gpr .r23 = dp s₀
  r24 : s.gpr .r24 = s₀.gpr .r4
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

theorem Vars.of_pres {s s' : State} (h : Vars (H := H) s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Vars (H := H) s₀ s' :=
  ⟨(hc _ (by decide)).trans h.r20, (hc _ (by decide)).trans h.r21, (hc _ (by decide)).trans h.r22,
    (hc _ (by decide)).trans h.r23, (hc _ (by decide)).trans h.r24,
    fun r hr => (hc r (untouched_pres r hr)).trans (h.un r hr)⟩

/-- `Vars` after code writing only `r3`–`r7`. -/
theorem Vars.of_keep {s s' : State} (h : Vars (H := H) s₀ s)
    (hc : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) :
    Vars (H := H) s₀ s' := by
  have k : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31, .r20,
      .r21, .r22, .r23, .r24], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.r20, (k _ (by simp)).trans h.r21, (k _ (by simp)).trans h.r22,
    (k _ (by simp)).trans h.r23, (k _ (by simp)).trans h.r24,
    fun r hr => (k r (by revert r; decide)).trans (h.un r hr)⟩

/-! ## Correctness -/

/-- `digestMain`: the digest is in `out`, and the callee-saved registers are
kept. -/
theorem correctMain (hp : Pre H s₀) :
    WP isa (digestMain H) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (out s₀) H.D = hH.SH.H.hash (M s₀) := by
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hW : H.W % 8 = 0 ∧ H.W ≤ 1024 := hH.dims.so
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  have hS : H.S = H.N + H.B := rfl
  have hD := hH.hFD64
  have hDF := hH.hDF
  have hl := lay hH
  have hdl : dl s₀ < 2 ^ 64 := (s₀.gpr .r4).isLt
  have := hp.sp48
  have hlst : H.lst + H.S ≤ H.lbytes := by
    have := hl.dgsv; rw [hl.lbytes, hl.lst]; rw [hl.ldg] at this; simp only [Hash.S] at *; omega_arith
  have hldg : H.ldg + H.FD ≤ H.lbytes := by have := hl.dgsv; rw [hl.lbytes]; omega_arith
  have hW' : H.W ≤ H.lbytes := by have := hl.dgsv; rw [hl.lbytes]; rw [hl.ldg] at this; omega_arith
  let all : List Region := [oR H s₀, scR H s₀, below s₀.sp 48]
  have msg_keep : ∀ m, Frame all s₀.mem m → bytesAt m (dp s₀) (dl s₀) = M s₀ := by
    intro m hf
    refine Proof.Sha256.Stream.bytesAt_congr fun i hi => hf.bytes (R := dR s₀) ?_ (by simp; omega_arith) hi
    simp only [all, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hp.d_o, hp.d_s, hp.sd.symm]
  have sfS : ∀ R : Region, Region.Sub R (scR H s₀) → R.Disjoint (oR H s₀) ∧ R.Disjoint (dR s₀) ∧
      (below s₀.sp 48).Disjoint R := fun R h =>
    ⟨hp.o_s.symm.sub_left h, hp.d_s.symm.sub_left h, hp.ss.sub_right h⟩
  have saved_st : ∀ {m m' : Mem}, Saved H.lsv (scr s₀) s₀.gpr m → ∀ {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 H.lsv, 48⟩ r) → Saved H.lsv (scr s₀) s₀.gpr m' :=
    fun h _ hf hd => saved_keep h hf hd
  unfold digestMain
  -- Save our caller's registers, and set up ours.
  refine WP.seq (save_ok hH.dims.lso (b := .r6) (by decide)
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [hp.wr], contains_offset
      (show d + 8 ≤ H.lbytes by have : d + 8 ≤ H.lsv + 48 := hd₂; rw [hl.lbytes]; omega_arith)
      (by have : d + 8 ≤ H.lsv + 48 := hd₂; have := hl.lsv; omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_addi (by rw [hl.lst]; omega_arith) fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have hr₇ : Regs s₀ s₇ :=
    ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
      by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]⟩
  have m₇ : s₇.mem = saveMem H.lsv s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have v₇ : Vars (H := H) s₀ s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · simp only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · rw [u₇.other r (by revert r; decide), u₆.other r (by revert r; decide), u₅.other r (by revert r; decide),
        u₄.other r (by revert r; decide), u₃.other r (by revert r; decide), u₂.other r (by revert r; decide), g₁]
  have h3₇ : s₇.gpr .r3 = scr s₀ + BitVec.ofNat 64 H.lst := by
    rw [u₇.gpr]; exact (u₇.other _ (by decide)).symm.trans v₇.r20
  have fS : Frame [⟨scr s₀, H.lsv + 48⟩] s₀.mem s₇.mem := by rw [m₇]; exact saveMem_frame hH.dims.lso _ _ _
  have f₇ : Frame all s₀.mem s₇.mem :=
    fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR H s₀, by simp [all], Region.sub_prefix (by rw [hl.lbytes])⟩
  have sv₇ : Saved H.lsv (scr s₀) s₀.gpr s₇.mem := by rw [m₇]; exact saveMem_saved hH.dims.lso _ _ _
  -- The streaming state.
  refine WP.seq (hH.callInit_ok (st := scr s₀ + BitVec.ofNat 64 H.lst) h3₇
      ⟨by rw [hr₇.sp]; omega_arith, by rw [hr₇.sp]; exact (sfS _ (stR_sub hl _)).2.2⟩
    (by rw [hr₇.rd, hr₇.wr, hp.rd, hp.wr]; exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact cover_off (R := scR H s₀) (by simp) (by exact hlst))
    (by rw [hr₇.wr, hp.wr]; exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact cover_off (R := scR H s₀) (by simp) (by exact hlst))
    fun s₈ rd₈ wr₈ sp₈ f₈ cs₈ hr₈ => ?_)
  rw [hr₇.sp] at f₈
  have g₈ : Regs s₀ s₈ := ⟨rd₈.trans hr₇.rd, wr₈.trans hr₇.wr, sp₈.trans hr₇.sp⟩
  have v₈ : Vars (H := H) s₀ s₈ := v₇.of_pres cs₈
  have f₈' : Frame all s₀.mem s₈.mem := f₇.trans (f₈.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR H s₀, by simp [all], stR_sub hl _⟩
    · exact ⟨below s₀.sp 48, by simp [all], fun _ h => h⟩)
  have sv₈ : Saved H.lsv (scr s₀) s₀.gpr s₈.mem := saved_st sv₇ f₈ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (st_sv hl _).symm
    · exact (hp.ss.sub_right (svR_sub hl _)).symm)
  -- Absorb the message into it.
  refine WP.seq (wp_mov fun s₉ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ =>
    wp_mov fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ => WP.block_nil ?_)
  have g₁₃ : Regs s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, g₈.rd], by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, g₈.wr],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, g₈.sp]⟩
  have m₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have v₁₃ : Vars (H := H) s₀ s₁₃ := v₈.of_keep fun r a b c d e => by
    rw [u₁₃.other r e, u₁₂.other r d, u₁₁.other r c, u₁₀.other r b, u₉.other r a]
  have dSW : Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 H.lst, H.S⟩ ⟨scr s₀, H.W⟩ :=
    (wI_st hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
  have dDS := (sfS _ (stR_sub hl _)).2.1.symm
  have dDW := (sfS _ (wR_sub hl _)).2.1.symm
  refine WP.seq (hH.callUpd_ok (st := scr s₀ + BitVec.ofNat 64 H.lst) (dat := dp s₀) (scr := scr s₀)
    (len := dl s₀)
    (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, v₈.r20])
    (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), v₈.r23])
    (by rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), v₈.r24])
    (by rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), v₈.r21])
    dSW dDS dDW (by rw [g₁₃.sp]; omega_arith)
    (by rw [g₁₃.sp]; exact (sfS _ (stR_sub hl _)).2.2)
    (by rw [g₁₃.sp]; exact hp.sd)
    (by rw [g₁₃.sp]; exact (sfS _ (wR_sub hl _)).2.2)
    (by
      rw [g₁₃.rd, g₁₃.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_self (by simp)
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    (by
      rw [g₁₃.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    fun s₁₄ rd₁₄ wr₁₄ sp₁₄ f₁₄ cs₁₄ hup₁₄ => ?_)
  rw [g₁₃.sp] at f₁₄
  have g₁₄ : Regs s₀ s₁₄ := ⟨rd₁₄.trans g₁₃.rd, wr₁₄.trans g₁₃.wr, sp₁₄.trans g₁₃.sp⟩
  have v₁₄ : Vars (H := H) s₀ s₁₄ := v₁₃.of_pres cs₁₄
  have hrM : hH.SH.Repr s₁₄.mem (scr s₀ + BitVec.ofNat 64 H.lst) (M s₀) := by
    have := hup₁₄ [] (by rw [m₁₃]; exact hr₈) (by
      rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr]; rfl)
    rwa [List.nil_append, m₁₃, msg_keep _ f₈'] at this
  have f₁₄' : Frame all s₀.mem s₁₄.mem := f₈'.trans (by
    rw [← m₁₃]
    exact f₁₄.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scR H s₀, by simp [all], stR_sub hl _⟩
      · exact ⟨scR H s₀, by simp [all], wR_sub hl _⟩
      · exact ⟨below s₀.sp 48, by simp [all], fun _ h => h⟩)
  have sv₁₄ : Saved H.lsv (scr s₀) s₀.gpr s₁₄.mem := saved_st (by rw [m₁₃]; exact sv₈) f₁₄ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (st_sv hl _).symm
    · exact (wI_sv hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
    · exact (hp.ss.sub_right (svR_sub hl _)).symm)
  -- The digest, into the scratch space.
  refine WP.seq (wp_mov fun s₁₅ u₁₅ => wp_mov fun s₁₆ u₁₆ => wp_addi (by rw [hl.ldg]; omega_arith) fun s₁₇ u₁₇ =>
    wp_mov fun s₁₈ u₁₈ => WP.block_nil ?_)
  have g₁₈ : Regs s₀ s₁₈ :=
    ⟨by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, g₁₄.rd], by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, g₁₄.wr],
      by rw [u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, g₁₄.sp]⟩
  have m₁₈ : s₁₈.mem = s₁₄.mem := by rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem]
  have v₁₈ : Vars (H := H) s₀ s₁₈ := v₁₄.of_keep fun r a b c d _ => by
    rw [u₁₈.other r d, u₁₇.other r c, u₁₆.other r b, u₁₅.other r a]
  have dSD : Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 H.lst, H.S⟩ ⟨scr s₀ + BitVec.ofNat 64 H.ldg, H.FD⟩ :=
    st_dg hl _
  have dGW : Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 H.ldg, H.FD⟩ ⟨scr s₀, H.W⟩ :=
    (wI_dg hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
  refine WP.seq (hH.callFin_ok (st := scr s₀ + BitVec.ofNat 64 H.lst) (o := scr s₀ + BitVec.ofNat 64 H.ldg)
    (scr := scr s₀)
    (by rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₅.gpr, v₁₄.r20])
    (by rw [u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), v₁₄.r21])
    (by rw [u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide), v₁₄.r21])
    dSD dSW dGW (by rw [g₁₈.sp]; omega_arith)
    (by rw [g₁₈.sp]; exact (sfS _ (stR_sub hl _)).2.2)
    (by rw [g₁₈.sp]; exact (sfS _ (dgR_sub hl _)).2.2)
    (by rw [g₁₈.sp]; exact (sfS _ (wR_sub hl _)).2.2)
    (by
      rw [g₁₈.rd, g₁₈.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_off (R := scR H s₀) (by simp) (by exact hldg)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    (by
      rw [g₁₈.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_off (R := scR H s₀) (by simp) (by exact hldg)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    fun s₁₉ rd₁₉ wr₁₉ sp₁₉ f₁₉ cs₁₉ hfin₁₉ => ?_)
  rw [g₁₈.sp] at f₁₉
  have g₁₉ : Regs s₀ s₁₉ := ⟨rd₁₉.trans g₁₈.rd, wr₁₉.trans g₁₈.wr, sp₁₉.trans g₁₈.sp⟩
  have v₁₉ : Vars (H := H) s₀ s₁₉ := v₁₈.of_pres cs₁₉
  have hdig : bytesAt s₁₉.mem (scr s₀ + BitVec.ofNat 64 H.ldg) H.D = hH.SH.H.hash (M s₀) := by
    rw [bytesAt_take _ _ hH.hDF, hfin₁₉ _ (by rw [m₁₈]; exact hrM) (by simp [bytesAt]; omega_arith) (by
      rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide), v₁₄.r24]
      simp [bytesAt]), hH.hashTake]
  have sv₁₉ : Saved H.lsv (scr s₀) s₀.gpr s₁₉.mem := saved_st (by rw [m₁₈]; exact sv₁₄) f₁₉ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact (st_sv hl _).symm
    · exact (dg_sv hl _).symm
    · exact (wI_sv hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
    · exact (hp.ss.sub_right (svR_sub hl _)).symm)
  -- The digest, into `out`.
  have hD44 : 4 * (H.D / 4) = H.D := by have := hH.hD4; omega_arith
  have e0 : out s₀ + BitVec.ofNat 64 0 = out s₀ := by simp
  have dOD : (oR H s₀).Disjoint ⟨scr s₀ + BitVec.ofNat 64 H.ldg, H.D⟩ :=
    hp.o_s.sub_right (fun a h => dgR_sub hl _ a (Region.sub_prefix hDF a h))
  unfold copyOut
  refine copy32_ok (src := .r21) (dst := .r22) (by decide) (by decide) (by decide) (by decide) H.ldg 0
    (H.D / 4) ⟨by rw [hl.ldg]; omega_arith, by omega_arith⟩ _ s₁₉ _
    (fun k hk => ⟨scR H s₀, by simp [g₁₉.rd, g₁₉.wr, hp.wr], by
      rw [v₁₉.r21, ← add_off]
      have := hl.lsv; have := hl.lbytes
      exact contains_offset (by omega_arith) (by omega_arith)⟩)
    (fun k hk => ⟨oR H s₀, by simp [g₁₉.wr, hp.wr], by
      rw [v₁₉.r22, e0]; exact contains_offset (by omega_arith) (by omega_arith)⟩)
    (by
      rw [v₁₉.r21, v₁₉.r22, e0, hD44]
      exact dOD.symm.sep (contains_start (Nat.le_refl _)) (contains_start (Nat.le_refl _)))
    fun s₂₀ g₂₀ rd₂₀ wr₂₀ sp₂₀ m₂₀ => ?_
  rw [v₁₉.r21, v₁₉.r22, e0, hD44] at m₂₀
  have g₂₀' : Regs s₀ s₂₀ := ⟨rd₂₀.trans g₁₉.rd, wr₂₀.trans g₁₉.wr, sp₂₀.trans g₁₉.sp⟩
  have v₂₀ : Vars (H := H) s₀ s₂₀ :=
    ⟨(g₂₀ _ (by decide)).trans v₁₉.r20, (g₂₀ _ (by decide)).trans v₁₉.r21, (g₂₀ _ (by decide)).trans v₁₉.r22,
      (g₂₀ _ (by decide)).trans v₁₉.r23, (g₂₀ _ (by decide)).trans v₁₉.r24,
      fun r hr => (g₂₀ r (by rintro rfl; exact absurd hr (by decide))).trans (v₁₉.un r hr)⟩
  have hout : bytesAt s₂₀.mem (out s₀) H.D = hH.SH.H.hash (M s₀) := by
    rw [← hdig, m₂₀]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₁₉.mem (out s₀)
      (bytesAt s₁₉.mem (scr s₀ + BitVec.ofNat 64 H.ldg) H.D)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega_arith)
    rwa [VG.Proof.Hmac.Common.bytesAt_length] at this
  have sv₂₀ : Saved H.lsv (scr s₀) s₀.gpr s₂₀.mem := by
    rw [m₂₀]
    refine saved_keep sv₁₉ (VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]; exact contains_start (Nat.le_refl _))) ?_
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.symm.sub_left (svR_sub hl _)
  -- Restore our caller's registers.
  refine restore_ok hH.dims.lso (scr := scr s₀) v₂₀.r21
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [g₂₀'.rd, g₂₀'.wr, hp.wr], contains_offset
      (show d + 8 ≤ H.lbytes by have : d + 8 ≤ H.lsv + 48 := hd₂; rw [hl.lbytes]; omega_arith)
      (by have : d + 8 ≤ H.lsv + 48 := hd₂; have := hl.lsv; omega_arith)⟩)
    s₀.gpr sv₂₀ fun s' hsv ho hmem _ _ hsp => ⟨preserved_of hsv fun r hr => ?_, by rw [hsp, g₂₀'.sp],
      by rw [hmem]; exact hout⟩
  rw [ho r (by simp only [Hash.savedAt, List.map_cons, List.map_nil]; revert r; decide)]
  exact v₂₀.un r hr

/-! ## The frame -/

include hH in
theorem digestMain_fdepth : (digestMain H).fdepth ≤ 1 := by
  have := hH.initFd
  have := hH.updFd
  have := hH.finFd
  simp only [digestMain, Hash.callInit, Hash.callUpd, Hash.callFin, Code.fdepth, Nat.max_le]
  omega_arith

include hH in
theorem digestMain_pf : pushFrames (digestMain H) = true := by
  simp [digestMain, Hash.callInit, Hash.callUpd, Hash.callFin, pushFrames, hH.initPf, hH.updPf, hH.finPf]

open VG.Proof.Hmac.Stream.PPC64LE.Init (inner inner_bytes) in
theorem pre_inner {s₀ : State} (hp : (digestG hH.SH H.lbytes 96).pre s₀) : Pre H (inner s₀) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hp
  rw [hH.hD] at *
  have sub : Region.Sub (below (s₀.sp - 48) 48) (below s₀.sp 96) := below_body s₀.sp 48
  exact ⟨h1, h2, h3, h4, h5, by show 48 ≤ (s₀.sp - 48).toNat; bv_omega, h7.sub_left sub,
    h8.sub_left sub, h9.sub_left sub⟩

open VG.Proof.Hmac.Stream.PPC64LE.Init (inner inner_bytes) in
/-- `digest`, with its frame. -/
theorem correct {s₀ : State} (hp : (digestG hH.SH H.lbytes 96).pre s₀) :
    WP isa (digest H) s₀ fun s' => abiPreserved s₀ s' ∧ (digestG hH.SH H.lbytes 96).post s₀ s' := by
  have hpi := pre_inner hH hp
  obtain ⟨h1, h2, _, _, _, h6, h7, h8, h9⟩ := hp
  have hsub : Region.Sub (below s₀.sp 48) (below s₀.sp 96) := below_sub (by omega_arith) (by omega_arith)
  refine WP.seq (Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by show 48 ≤ s₀.sp.toNat; omega_arith) (fun R hR => ?_) (WP.mono (correctMain hH hpi)
    fun s' ⟨hk, hsp, hpost⟩ => ?_) (by have := digestMain_fdepth hH; omega_arith) (digestMain_pf hH)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, h2] at hR
    have hf : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ (below s₀.sp 96) :=
      fun a h => hsub a (Proof.MdStream.PPC64LE.frame_sub s₀.sp a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact h8.sub_left hf
    · exact h9.sub_left hf
  · refine Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · show bytesAt _ (s₀.gpr .r5) hH.SH.digestBytes = _
      rw [hH.hD]
      have hM : M (inner s₀) = bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat :=
        Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          inner_bytes (R := ⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩) (h7.sub_left hsub)
            (s₀.gpr .r4).isLt hi
      rw [← hM]
      exact hpost

/-! ## The shared contracts -/

/-- The initial taint of `digest`: only the arguments are public. -/
theorem agree {s₁ s₂ : State}
    (h : s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨p3, p4, p5, p6, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying `digest`'s precondition, with a digest of `D` bytes,
an empty message and `sc` bytes of scratch space (none: the frame holds it). -/
def digestSat (D sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r5 => 0x20000 | .r6 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩]
  wr := [⟨0x20000, D⟩] ++ (if sc = 0 then [] else [⟨0x40000, sc⟩])

/-- `vg_<hash>_digest` with `scratch: *mut [u64; n]`, for a `D`-byte digest. -/
def digestScratchSig (D n : Nat) : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 D), ("scratch", .array true .u64 n)]

/-- `Spec.Sha256.digestContract` for `SH`'s digest, whatever `scratch` is,
with the 96 bytes of stack `digest` and its callees use. -/
def digestScratchContract (SH : StreamingHash) (n : Nat) : Contract isa :=
  (digestScratchSig SH.digestBytes n).contract PPC64LE.abi
    (post := fun data len out _scratch => Spec.Sha256.digestPost SH.digestBytes SH.H.hash PPC64LE.abi.ptrBits
      data len out)
    (stack := 96)

theorem digestImp (SH : StreamingHash) (n : Nat) (hs : ∃ s, (digestScratchContract SH n).pre s) :
    (digestG SH (8 * n) 96).Implies (digestScratchContract SH n) := by
  generic_implies [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, digestG, PPC64LE.abi,
    PPC64LE.argRegs] using hs

/-- `digest` with its working space in `scratch` (`n` doublewords, all of
it), given its constant time. -/
theorem digestScratch {n : Nat} (hn : 8 * n = H.lbytes)
    (ct : ConstantTime isa (digestG hH.SH H.lbytes 96).pre (digestG hH.SH H.lbytes 96).pub (digest H))
    (hs : ∃ s, (digestScratchContract hH.SH n).pre s) :
    Verified PPC64LE.target (digest H) (digestScratchContract hH.SH n) := by
  have imp := digestImp hH.SH n hs
  rw [hn] at imp
  have v : Verified PPC64LE.target (digest H) (digestG hH.SH H.lbytes 96) :=
    ⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := correct hH hs; exact ⟨t, s', he, h₁, h₂⟩, ct, imp.sat_left⟩
  exact v.of_implies imp

/-- `digest` in a frame of `bytes` bytes of its own, the first `n`
doublewords of which (its working space) it zeroes before returning. -/
theorem digestFrame {SH : StreamingHash} {n bytes : Nat}
    (h : Verified PPC64LE.target (digest H) (digestScratchContract SH n))
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * 8 + 32 ≤ bytes)
    (hsat : ∃ s, (Spec.Sha256.digestContract PPC64LE.abi SH.digestBytes SH.H.hash (96 + bytes)).pre s) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped bytes .r6 n (digest H))
      (Spec.Sha256.digestContract PPC64LE.abi SH.digestBytes SH.H.hash (96 + bytes)) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sha256.digestSig SH.digestBytes) (nm := "scratch") (e := .u64)
    (n := n) (post := Spec.Sha256.digestPost SH.digestBytes SH.H.hash PPC64LE.abi.ptrBits) (wa := false)
    (stack := 96) (bytes := bytes) (words := n) h (by exact (by decide : 3 < 8)) hb
    (by simp only [Elem.size]; omega) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Digest.digestPost_local _ _ _) (Digest.digestPostOut_local _ _ _) hsat rfl

end VG.Proof.MdStream.PPC64LE.Digest
