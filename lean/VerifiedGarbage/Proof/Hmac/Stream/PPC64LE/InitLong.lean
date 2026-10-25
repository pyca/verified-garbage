module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Save
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Init
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic

/-!
# HMAC over any streaming hash function on PPC64LE: `init` for a key longer than a block

`initLongMain` saves our caller's `r20`–`r25` after its buffers, hashes the
key with the streaming `init`, `update` and `finalize` into its scratch
space, calls HMAC's `init` (`Init.correct`) with the digest, whose
`blockKey` is the key's (`blockKey_digest`), and restores the registers
(`correctMain`). HMAC's `init` and its callees use the 96 bytes below the
stack pointer.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.InitLong

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_addi contains_offset)
open VG.Proof.Hmac.Stream.PPC64LE.Init (cover_self cover_pre cover_off covers_one Regs)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .r3
abbrev out : Addr := s₀.gpr .r4
abbrev kp : Addr := s₀.gpr .r5
abbrev kl : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev kR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, H.lbytes⟩
/-- The working space of HMAC's `init`. -/
abbrev wI : Region := ⟨scr s₀, H.W + 48⟩
/-- That of the streaming functions. -/
abbrev wR : Region := ⟨scr s₀, H.W⟩
/-- The streaming state the key is hashed in. -/
abbrev stR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.lst, H.S⟩
/-- Its digest. -/
abbrev dgR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.ldg, H.FD⟩
/-- The key's digest, its first `D` bytes. -/
abbrev dkR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.ldg, H.D⟩
/-- Our caller's registers. -/
abbrev svR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.lsv, 48⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (kp s₀) (kl s₀)

end

/-- `initLong`'s precondition, with the stack pointer below its frame: HMAC's
`init`, which it calls, and that function's callees use the 96 bytes below
it. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  kl_gt : H.B < kl s₀
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR H s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR H s₀)
  o_s : (outR H s₀).Disjoint (scR H s₀)
  k_i : (kR s₀).Disjoint (inR H s₀)
  k_o : (kR s₀).Disjoint (outR H s₀)
  k_s : (kR s₀).Disjoint (scR H s₀)
  sp96 : 96 ≤ s₀.sp.toNat
  si : (below s₀.sp 96).Disjoint (inR H s₀)
  so : (below s₀.sp 96).Disjoint (outR H s₀)
  sk : (below s₀.sp 96).Disjoint (kR s₀)
  ss : (below s₀.sp 96).Disjoint (scR H s₀)

variable {H : Hash} (hH : HashOK H) {s₀ : State}

/-- A key longer than a block and its digest make the same block key. -/
theorem blockKey_digest {k : List Byte} (hk : H.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hl := hH.hashLen k
  have := hH.hDB
  simp only [blockKey, hH.hB, hl, show ¬ (H.B < H.D) by omega_arith, ite_false, hk, ite_true]

/-- The layout of the scratch space. -/
structure Lay (H : Hash) : Prop where
  lst : H.lst = H.W + 48
  ldg : H.ldg = H.W + 48 + H.S
  dgsv : H.ldg + H.FD ≤ H.lsv
  lsv : H.lsv ≤ 1024
  lbytes : H.lbytes = H.lsv + 48

include hH in
theorem lay : Lay H := by
  have := hH.dims.lso
  exact ⟨rfl, rfl, by simp only [Hash.lsv]; omega_arith, this.2, rfl⟩

/-- `Vars` for `initLong`: our variables in `r20`–`r25`, and the callee-saved
registers we never write. -/
structure Vars (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = scr s₀ + BitVec.ofNat 64 H.lst
  r21 : s.gpr .r21 = scr s₀
  r22 : s.gpr .r22 = inn s₀
  r23 : s.gpr .r23 = out s₀
  r24 : s.gpr .r24 = s₀.gpr .r6
  r25 : s.gpr .r25 = kp s₀
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

theorem Vars.of_pres {s s' : State} (h : Vars (H := H) s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Vars (H := H) s₀ s' :=
  ⟨(hc _ (by decide)).trans h.r20, (hc _ (by decide)).trans h.r21, (hc _ (by decide)).trans h.r22,
    (hc _ (by decide)).trans h.r23, (hc _ (by decide)).trans h.r24, (hc _ (by decide)).trans h.r25,
    fun r hr => (hc r (untouched_pres r hr)).trans (h.un r hr)⟩

/-- `Vars` after code writing only `r3`–`r7`. -/
theorem Vars.of_keep {s s' : State} (h : Vars (H := H) s₀ s)
    (hc : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) :
    Vars (H := H) s₀ s' := by
  have k : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31, .r20,
      .r21, .r22, .r23, .r24, .r25], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.r20, (k _ (by simp)).trans h.r21, (k _ (by simp)).trans h.r22,
    (k _ (by simp)).trans h.r23, (k _ (by simp)).trans h.r24, (k _ (by simp)).trans h.r25,
    fun r hr => (k r (by revert r; decide)).trans (h.un r hr)⟩

/-! ## The scratch space -/

section
variable (hl : Lay H) (p : Addr)
include hl

theorem wI_sub : Region.Sub ⟨p, H.W + 48⟩ ⟨p, H.lbytes⟩ := Region.sub_prefix (by have := hl.dgsv; rw [hl.lbytes]; rw [hl.ldg] at this; omega_arith)
theorem wR_sub : Region.Sub ⟨p, H.W⟩ ⟨p, H.lbytes⟩ := Region.sub_prefix (by have := hl.dgsv; rw [hl.lbytes]; rw [hl.ldg] at this; omega_arith)
theorem stR_sub : Region.Sub ⟨p + BitVec.ofNat 64 H.lst, H.S⟩ ⟨p, H.lbytes⟩ :=
  Offset.sub_base p (by have := hl.dgsv; rw [hl.lbytes, hl.lst]; rw [hl.ldg] at this; simp only [Hash.S] at *; omega_arith)
theorem dgR_sub : Region.Sub ⟨p + BitVec.ofNat 64 H.ldg, H.FD⟩ ⟨p, H.lbytes⟩ :=
  Offset.sub_base p (by have := hl.dgsv; rw [hl.lbytes]; omega_arith)
theorem svR_sub : Region.Sub ⟨p + BitVec.ofNat 64 H.lsv, 48⟩ ⟨p, H.lbytes⟩ :=
  Offset.sub_base p (by rw [hl.lbytes])
theorem wI_st : Region.Disjoint ⟨p, H.W + 48⟩ ⟨p + BitVec.ofNat 64 H.lst, H.S⟩ :=
  Offset.base_disjoint p (by rw [hl.lst]) (by have := hl.lsv; have := hl.dgsv; rw [hl.ldg] at this; rw [hl.lst]; simp only [Hash.S] at *; omega_arith)
theorem wI_dg : Region.Disjoint ⟨p, H.W + 48⟩ ⟨p + BitVec.ofNat 64 H.ldg, H.FD⟩ :=
  Offset.base_disjoint p (by rw [hl.ldg]; omega_arith) (by have := hl.lsv; have := hl.dgsv; omega_arith)
theorem wI_sv : Region.Disjoint ⟨p, H.W + 48⟩ ⟨p + BitVec.ofNat 64 H.lsv, 48⟩ :=
  Offset.base_disjoint p (by have := hl.dgsv; rw [hl.ldg] at this; omega_arith) (by have := hl.lsv; omega_arith)
theorem st_dg : Region.Disjoint ⟨p + BitVec.ofNat 64 H.lst, H.S⟩ ⟨p + BitVec.ofNat 64 H.ldg, H.FD⟩ :=
  Offset.disjoint p (.inl (by rw [hl.ldg, hl.lst])) (by have := hl.lsv; have := hl.dgsv; rw [hl.ldg] at this; rw [hl.lst]; simp only [Hash.S] at *; omega_arith)
    (by have := hl.lsv; have := hl.dgsv; omega_arith)
theorem st_sv : Region.Disjoint ⟨p + BitVec.ofNat 64 H.lst, H.S⟩ ⟨p + BitVec.ofNat 64 H.lsv, 48⟩ :=
  Offset.disjoint p (.inl (by have := hl.dgsv; rw [hl.ldg] at this; rw [hl.lst]; simp only [Hash.S] at *; omega_arith))
    (by have := hl.lsv; have := hl.dgsv; rw [hl.ldg] at this; rw [hl.lst]; simp only [Hash.S] at *; omega_arith)
    (by have := hl.lsv; omega_arith)
theorem dg_sv : Region.Disjoint ⟨p + BitVec.ofNat 64 H.ldg, H.FD⟩ ⟨p + BitVec.ofNat 64 H.lsv, 48⟩ :=
  Offset.disjoint p (.inl hl.dgsv) (by have := hl.lsv; have := hl.dgsv; omega_arith) (by have := hl.lsv; omega_arith)

end

/-! ## Correctness -/

include hH in
theorem init_fdepth : H.init.fdepth ≤ 2 := by
  have := Init.initMain_fdepth hH
  simp only [Hash.init, Code.fdepth, Nat.max_le]
  omega_arith

include hH in
theorem init_pf : pushFrames H.init = true := by
  simp [Hash.init, pushFrames, Instr.isPush, Init.initMain_pf hH]

/-- `initLong` without its frame: the callee-saved registers are kept. -/
theorem correctMain (hp : Pre H s₀) :
    WP isa H.initLongMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      hH.SH.Repr s'.mem (inn s₀) (xorPad (blockKey hH.SH.H (K s₀)) ipad) ∧
      hH.SH.Repr s'.mem (out s₀) (xorPad (blockKey hH.SH.H (K s₀)) opad) := by
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hW : H.W % 8 = 0 ∧ H.W ≤ 1024 := hH.dims.so
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  have hB' : H.B ≤ 128 := by omega_arith
  have hS : H.S = H.N + H.B := rfl
  have hD := hH.hD64
  have hl := lay hH
  have hkB : kl s₀ < 2 ^ 64 := (s₀.gpr .r6).isLt
  have := hp.sp96
  have hsub : Region.Sub (below s₀.sp 48) (below s₀.sp 96) := below_sub (by omega_arith) (by omega_arith)
  have hlst : H.lst + H.S ≤ H.lbytes := by
    have := hl.dgsv; rw [hl.lbytes, hl.lst]; rw [hl.ldg] at this; simp only [Hash.S] at *; omega_arith
  have hW' : H.W ≤ H.lbytes := by have := hl.dgsv; rw [hl.lbytes]; rw [hl.ldg] at this; omega_arith
  let all : List Region := [inR H s₀, outR H s₀, scR H s₀, below s₀.sp 96]
  have key_keep : ∀ m, Frame all s₀.mem m → bytesAt m (kp s₀) (kl s₀) = K s₀ := by
    intro m hf
    refine Proof.Sha256.Stream.bytesAt_congr fun i hi => hf.bytes (R := kR s₀) ?_ (by simp; omega_arith) hi
    simp only [all, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [hp.k_i, hp.k_o, hp.k_s, hp.sk.symm]
  have dsv : ∀ R : Region, R ∈ all → R ≠ scR H s₀ → R.Disjoint (svR H s₀) := by
    simp only [all, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl) hne
    · exact hp.i_s.sub_right (svR_sub hl _)
    · exact hp.o_s.sub_right (svR_sub hl _)
    · exact absurd rfl hne
    · exact hp.ss.sub_right (svR_sub hl _)
  unfold Hash.initLongMain
  -- Save our caller's registers, and set up ours.
  refine WP.seq (save_ok hH.dims.lso (b := .r7) (by decide)
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [hp.wr], contains_offset
      (show d + 8 ≤ H.lbytes by have : d + 8 ≤ H.lsv + 48 := hd₂; rw [hl.lbytes]; omega_arith)
      (by have : d + 8 ≤ H.lsv + 48 := hd₂; have := hl.lsv; omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_addi (by rw [hl.lst]; omega_arith) fun s₇ u₇ => wp_mov fun s₈ u₈ => WP.block_nil ?_
  have hr₈ : Regs s₀ s₈ :=
    ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
      by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]⟩
  have m₈ : s₈.mem = saveMem H.lsv s₀.mem (scr s₀) s₀.gpr := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have v₈ : Vars (H := H) s₀ s₈ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · simp only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · rw [u₈.other r (by revert r; decide), u₇.other r (by revert r; decide), u₆.other r (by revert r; decide),
        u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), g₁]
  have h3₈ : s₈.gpr .r3 = scr s₀ + BitVec.ofNat 64 H.lst := by
    rw [u₈.gpr]; exact (u₈.other _ (by decide)).symm.trans v₈.r20
  have fS : Frame [⟨scr s₀, H.lsv + 48⟩] s₀.mem s₈.mem := by rw [m₈]; exact saveMem_frame hH.dims.lso _ _ _
  have f₈ : Frame all s₀.mem s₈.mem :=
    fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR H s₀, by simp [all], Region.sub_prefix (by rw [hl.lbytes])⟩
  have sv₈ : Saved H.lsv (scr s₀) s₀.gpr s₈.mem := by rw [m₈]; exact saveMem_saved hH.dims.lso _ _ _
  have sfS : ∀ R : Region, Region.Sub R (scR H s₀) → R.Disjoint (inR H s₀) ∧ R.Disjoint (outR H s₀) ∧
      R.Disjoint (kR s₀) ∧ (below s₀.sp 96).Disjoint R := fun R h =>
    ⟨hp.i_s.symm.sub_left h, hp.o_s.symm.sub_left h, hp.k_s.symm.sub_left h, hp.ss.sub_right h⟩
  have saved_st : ∀ {m m' : Mem}, Saved H.lsv (scr s₀) s₀.gpr m → ∀ {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint (svR H s₀) r) → Saved H.lsv (scr s₀) s₀.gpr m' := by
    intro m m' h rs hf hd p hp'
    rw [← h p hp']
    have ho := saved_offset hp'
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    exact (hd r hr).sub_left (Offset.sub (scr s₀) (show H.lsv ≤ p.2 from ho.1) (show p.2 + 8 ≤ H.lsv + 48 from ho.2))
  -- The streaming state the key is hashed in.
  refine WP.seq (hH.callInit_ok (st := scr s₀ + BitVec.ofNat 64 H.lst) h3₈
      ⟨by rw [hr₈.sp]; omega_arith, by rw [hr₈.sp]; exact ((sfS _ (stR_sub hl _)).2.2.2).sub_left hsub⟩
    (by rw [hr₈.rd, hr₈.wr, hp.rd, hp.wr]; exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact cover_off (R := scR H s₀) (by simp) (by exact hlst))
    (by rw [hr₈.wr, hp.wr]; exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact cover_off (R := scR H s₀) (by simp) (by exact hlst))
    fun s₉ rd₉ wr₉ sp₉ f₉ cs₉ hr₉ => ?_)
  rw [hr₈.sp] at f₉
  have g₉ : Regs s₀ s₉ := ⟨rd₉.trans hr₈.rd, wr₉.trans hr₈.wr, sp₉.trans hr₈.sp⟩
  have v₉ : Vars (H := H) s₀ s₉ := v₈.of_pres cs₉
  have f₉' : Frame all s₀.mem s₉.mem := f₈.trans (f₉.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR H s₀, by simp [all], stR_sub hl _⟩
    · exact ⟨below s₀.sp 96, by simp [all], hsub⟩)
  have sv₉ : Saved H.lsv (scr s₀) s₀.gpr s₉.mem := saved_st sv₈ f₉ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (st_sv hl _).symm
    · exact (hp.ss.sub_right (svR_sub hl _)).symm.sub_right hsub)
  -- Absorb the key into it.
  refine WP.seq (wp_mov fun s₁₀ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ =>
    wp_mov fun s₁₃ u₁₃ => wp_mov fun s₁₄ u₁₄ => WP.block_nil ?_)
  have g₁₄ : Regs s₀ s₁₄ :=
    ⟨by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, g₉.rd], by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, g₉.wr],
      by rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, g₉.sp]⟩
  have m₁₄ : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  have v₁₄ : Vars (H := H) s₀ s₁₄ := v₉.of_keep fun r a b c d e => by
    rw [u₁₄.other r e, u₁₃.other r d, u₁₂.other r c, u₁₁.other r b, u₁₀.other r a]
  have dSW : Region.Disjoint (stR H s₀) ⟨scr s₀, H.W⟩ :=
    (wI_st hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
  have dKS := (sfS _ (stR_sub hl _)).2.2.1.symm
  have dKW := (sfS _ (wR_sub hl _)).2.2.1.symm
  refine WP.seq (hH.callUpd_ok (st := scr s₀ + BitVec.ofNat 64 H.lst) (dat := kp s₀) (scr := scr s₀)
    (len := kl s₀)
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, v₉.r20])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), v₉.r25])
    (by rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), v₉.r24])
    (by rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), v₉.r21])
    dSW dKS dKW (by rw [g₁₄.sp]; omega_arith)
    (by rw [g₁₄.sp]; exact ((sfS _ (stR_sub hl _)).2.2.2).sub_left hsub)
    (by rw [g₁₄.sp]; exact hp.sk.sub_left hsub)
    (by rw [g₁₄.sp]; exact ((sfS _ (wR_sub hl _)).2.2.2).sub_left hsub)
    (by
      rw [g₁₄.rd, g₁₄.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_self (by simp)
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    (by
      rw [g₁₄.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    fun s₁₅ rd₁₅ wr₁₅ sp₁₅ f₁₅ cs₁₅ hup₁₅ => ?_)
  rw [g₁₄.sp] at f₁₅
  have g₁₅ : Regs s₀ s₁₅ := ⟨rd₁₅.trans g₁₄.rd, wr₁₅.trans g₁₄.wr, sp₁₅.trans g₁₄.sp⟩
  have v₁₅ : Vars (H := H) s₀ s₁₅ := v₁₄.of_pres cs₁₅
  have hrK : hH.SH.Repr s₁₅.mem (scr s₀ + BitVec.ofNat 64 H.lst) (K s₀) := by
    have := hup₁₅ [] (by rw [m₁₄]; exact hr₉) (by
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr]; rfl)
    rwa [List.nil_append, m₁₄, key_keep _ f₉'] at this
  have f₁₅' : Frame all s₀.mem s₁₅.mem := f₉'.trans (by
    rw [← m₁₄]
    exact f₁₅.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scR H s₀, by simp [all], stR_sub hl _⟩
      · exact ⟨scR H s₀, by simp [all], wR_sub hl _⟩
      · exact ⟨below s₀.sp 96, by simp [all], hsub⟩)
  have sv₁₅ : Saved H.lsv (scr s₀) s₀.gpr s₁₅.mem := saved_st (by rw [m₁₄]; exact sv₉) f₁₅ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (st_sv hl _).symm
    · exact (wI_sv hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
    · exact (hp.ss.sub_right (svR_sub hl _)).symm.sub_right hsub)
  -- The key's digest.
  refine WP.seq (wp_mov fun s₁₆ u₁₆ => wp_mov fun s₁₇ u₁₇ => wp_addi (by rw [hl.ldg]; omega_arith) fun s₁₈ u₁₈ =>
    wp_mov fun s₁₉ u₁₉ => WP.block_nil ?_)
  have g₁₉ : Regs s₀ s₁₉ :=
    ⟨by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, g₁₅.rd], by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, g₁₅.wr],
      by rw [u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, g₁₅.sp]⟩
  have m₁₉ : s₁₉.mem = s₁₅.mem := by rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem]
  have v₁₉ : Vars (H := H) s₀ s₁₉ := v₁₅.of_keep fun r a b c d _ => by
    rw [u₁₉.other r d, u₁₈.other r c, u₁₇.other r b, u₁₆.other r a]
  have dSD : Region.Disjoint (stR H s₀) (dgR H s₀) := st_dg hl _
  have dDW : Region.Disjoint (dgR H s₀) ⟨scr s₀, H.W⟩ :=
    (wI_dg hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
  refine WP.seq (hH.callFin_ok (st := scr s₀ + BitVec.ofNat 64 H.lst) (o := scr s₀ + BitVec.ofNat 64 H.ldg)
    (scr := scr s₀)
    (by rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, v₁₅.r20])
    (by rw [u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.other _ (by decide), v₁₅.r21])
    (by rw [u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.other _ (by decide), v₁₅.r21])
    dSD dSW dDW (by rw [g₁₉.sp]; omega_arith)
    (by rw [g₁₉.sp]; exact ((sfS _ (stR_sub hl _)).2.2.2).sub_left hsub)
    (by rw [g₁₉.sp]; exact ((sfS _ (dgR_sub hl _)).2.2.2).sub_left hsub)
    (by rw [g₁₉.sp]; exact ((sfS _ (wR_sub hl _)).2.2.2).sub_left hsub)
    (by
      rw [g₁₉.rd, g₁₉.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_off (R := scR H s₀) (by simp) (by have := hl.dgsv; rw [hl.lbytes] at *; show _ ≤ H.lbytes; rw [hl.lbytes]; omega_arith)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    (by
      rw [g₁₉.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by exact hlst)
      · exact cover_off (R := scR H s₀) (by simp) (by have := hl.dgsv; show _ ≤ H.lbytes; rw [hl.lbytes]; omega_arith)
      · exact cover_pre (R := scR H s₀) (by simp) (by exact hW'))
    fun s₂₀ rd₂₀ wr₂₀ sp₂₀ f₂₀ cs₂₀ hfin₂₀ => ?_)
  rw [g₁₉.sp] at f₂₀
  have g₂₀ : Regs s₀ s₂₀ := ⟨rd₂₀.trans g₁₉.rd, wr₂₀.trans g₁₉.wr, sp₂₀.trans g₁₉.sp⟩
  have v₂₀ : Vars (H := H) s₀ s₂₀ := v₁₉.of_pres cs₂₀
  have hdig : bytesAt s₂₀.mem (scr s₀ + BitVec.ofNat 64 H.ldg) H.D = hH.SH.H.hash (K s₀) := by
    rw [bytesAt_take _ _ hH.hDF, hfin₂₀ _ (by rw [m₁₉]; exact hrK) (by simp [bytesAt]; omega_arith) (by
      rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.other _ (by decide), v₁₅.r24]
      simp [bytesAt]), hH.hashTake]
  have f₂₀' : Frame all s₀.mem s₂₀.mem := f₁₅'.trans (by
    rw [← m₁₉]
    exact f₂₀.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scR H s₀, by simp [all], stR_sub hl _⟩
      · exact ⟨scR H s₀, by simp [all], dgR_sub hl _⟩
      · exact ⟨scR H s₀, by simp [all], wR_sub hl _⟩
      · exact ⟨below s₀.sp 96, by simp [all], hsub⟩)
  have sv₂₀ : Saved H.lsv (scr s₀) s₀.gpr s₂₀.mem := saved_st (by rw [m₁₉]; exact sv₁₅) f₂₀ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact (st_sv hl _).symm
    · exact (dg_sv hl _).symm
    · exact (wI_sv hl _).symm.sub_right (Region.sub_prefix (by omega_arith))
    · exact (hp.ss.sub_right (svR_sub hl _)).symm.sub_right hsub)
  -- HMAC's `init`'s arguments, and our caller's registers restored.
  refine WP.seq (wp_mov fun s₂₁ u₂₁ => wp_mov fun s₂₂ u₂₂ => wp_addi (by rw [hl.ldg]; omega_arith) fun s₂₃ u₂₃ =>
    wp_li (by omega_arith) fun s₂₄ u₂₄ => wp_mov fun s₂₅ u₂₅ => ?_)
  have g₂₅ : Regs s₀ s₂₅ :=
    ⟨by rw [u₂₅.rd, u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd, g₂₀.rd], by rw [u₂₅.wr, u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr, g₂₀.wr],
      by rw [u₂₅.sp, u₂₄.sp, u₂₃.sp, u₂₂.sp, u₂₁.sp, g₂₀.sp]⟩
  have m₂₅ : s₂₅.mem = s₂₀.mem := by rw [u₂₅.mem, u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem]
  have v₂₅ : Vars (H := H) s₀ s₂₅ := v₂₀.of_keep fun r a b c d e => by
    rw [u₂₅.other r e, u₂₄.other r d, u₂₃.other r c, u₂₂.other r b, u₂₁.other r a]
  have a3 : s₂₅.gpr .r3 = inn s₀ := by
    rw [u₂₅.other _ (by decide), u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.other _ (by decide),
      u₂₁.gpr, v₂₀.r22]
  have a4 : s₂₅.gpr .r4 = out s₀ := by
    rw [u₂₅.other _ (by decide), u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.gpr,
      u₂₁.other _ (by decide), v₂₀.r23]
  have a5 : s₂₅.gpr .r5 = scr s₀ + BitVec.ofNat 64 H.ldg := by
    rw [u₂₅.other _ (by decide), u₂₄.other _ (by decide), u₂₃.gpr, u₂₂.other _ (by decide),
      u₂₁.other _ (by decide), v₂₀.r21]
  have a6 : (s₂₅.gpr .r6).toNat = H.D := by
    rw [u₂₅.other _ (by decide), u₂₄.gpr]
    exact Proof.MdStream.PPC64LE.toNat_ofNat_lt (by omega_arith)
  have a7 : s₂₅.gpr .r7 = scr s₀ := by
    rw [u₂₅.gpr, u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.other _ (by decide),
      u₂₁.other _ (by decide), v₂₀.r21]
  refine restore_ok hH.dims.lso (scr := scr s₀) v₂₅.r21
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [g₂₅.rd, g₂₅.wr, hp.wr], contains_offset
      (show d + 8 ≤ H.lbytes by have : d + 8 ≤ H.lsv + 48 := hd₂; rw [hl.lbytes]; omega_arith)
      (by have : d + 8 ≤ H.lsv + 48 := hd₂; have := hl.lsv; omega_arith)⟩)
    s₀.gpr (by rw [m₂₅]; exact sv₂₀) fun s₂₆ hsv ho hmem hrd hwr hsp => ?_
  have hk : ∀ r ∈ preserved, s₂₆.gpr r = s₀.gpr r := preserved_of hsv fun r hr => by
    rw [ho r (by simp only [Hash.savedAt, List.map_cons, List.map_nil]; revert r; decide)]
    exact v₂₅.un r hr
  have g₂₆ : Regs s₀ s₂₆ := ⟨hrd.trans g₂₅.rd, hwr.trans g₂₅.wr, hsp.trans g₂₅.sp⟩
  have arg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], s₂₆.callEntry.gpr r = s₂₅.gpr r := by
    intro r hr
    rw [State.callEntry_gpr _ (by revert r; decide)]
    exact ho r (by simp only [Hash.savedAt, List.map_cons, List.map_nil]; revert r; decide)
  have c3 : s₂₆.callEntry.gpr .r3 = inn s₀ := by rw [arg _ (by simp), a3]
  have c4 : s₂₆.callEntry.gpr .r4 = out s₀ := by rw [arg _ (by simp), a4]
  have c5 : s₂₆.callEntry.gpr .r5 = scr s₀ + BitVec.ofNat 64 H.ldg := by rw [arg _ (by simp), a5]
  have c6 : (s₂₆.callEntry.gpr .r6).toNat = H.D := by rw [arg _ (by simp), a6]
  have c7 : s₂₆.callEntry.gpr .r7 = scr s₀ := by rw [arg _ (by simp), a7]
  have wIs := wI_sub hl (scr s₀)
  have dkS : Region.Sub (dkR H s₀) ⟨scr s₀, H.lbytes⟩ := fun a h => dgR_sub hl _ a (Region.sub_prefix hH.hDF a h)
  have dD := sfS _ dkS
  have dW := sfS _ wIs
  -- HMAC's `init` with the digest.
  refine WP.callF (k := initG hH.SH (H.W + 48) 96) (fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := Init.correct hH hs
      exact ⟨t, s', he, h₁, h₂⟩)
    (rd := [dkR H s₀]) (wr := [inR H s₀, outR H s₀, wI H s₀]) ?_ ?_ ?_ ?_
    (by have := init_fdepth hH; omega_arith) (init_pf hH)
  · simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c4, c5, c6, c7, hH.hS, hH.hB, g₂₆.sp]
    have := hH.hDB
    exact ⟨this, trivial, trivial, hp.i_o, hp.i_s.sub_right wIs, hp.o_s.sub_right wIs, dD.1, dD.2.1,
      ((wI_dg hl _).sub_right (Region.sub_prefix hH.hDF)).symm, by omega_arith, hp.si, hp.so, dD.2.2.2, dW.2.2.2⟩
  · rw [g₂₆.rd, g₂₆.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cover_off (R := scR H s₀) (by simp) (by have := hl.dgsv; have := c6; have := hH.hDF; show _ ≤ H.lbytes; rw [hl.lbytes]; omega_arith)
    · exact cover_self (by simp)
    · exact cover_self (by simp)
    · exact cover_pre (R := scR H s₀) (by simp) (by have := hl.dgsv; rw [hl.ldg] at this; show H.W + 48 ≤ H.lbytes; rw [hl.lbytes]; omega_arith)
  · rw [g₂₆.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cover_self (by simp)
    · exact cover_self (by simp)
    · exact cover_pre (R := scR H s₀) (by simp) (by have := hl.dgsv; rw [hl.ldg] at this; show H.W + 48 ≤ H.lbytes; rw [hl.lbytes]; omega_arith)
  · intro s₂₇ _ _ sp₂₇ _ cs₂₇ hpost
    simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6]
      at hpost
    rw [hmem, m₂₅, hdig, blockKey_digest hH (by simp [bytesAt]; exact hp.kl_gt)] at hpost
    exact ⟨fun r hr => (cs₂₇ r hr).trans (hk r hr), by rw [sp₂₇, g₂₆.sp], hpost⟩

/-! ## The frame -/

include hH in
theorem initLongMain_fdepth : H.initLongMain.fdepth ≤ 2 := by
  have := hH.initFd
  have := hH.updFd
  have := hH.finFd
  have := init_fdepth hH
  simp only [Hash.initLongMain, Hash.callInit, Hash.callUpd, Hash.callFin, Hash.callHmacInit, Code.fdepth, Nat.max_le]
  omega_arith

include hH in
theorem initLongMain_pf : pushFrames H.initLongMain = true := by
  simp [Hash.initLongMain, Hash.callInit, Hash.callUpd, Hash.callFin, Hash.callHmacInit, pushFrames,
    hH.initPf, hH.updPf, hH.finPf, init_pf hH]

open VG.Proof.Hmac.Stream.PPC64LE.Init (inner inner_bytes) in
theorem pre_inner {s₀ : State} (hp : (longG hH.SH H.lbytes 144).pre s₀) : Pre H (inner s₀) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hp
  rw [hH.hS] at h2 h3 h4 h5 h6 h7 h10 h11
  have sub : Region.Sub (below (s₀.sp - 48) 96) (below s₀.sp 144) := below_body s₀.sp 96
  exact ⟨by rw [hH.hB] at h0; exact h0, h1, h2, h3, h4, h5, h6, h7, h8,
    by show 96 ≤ (s₀.sp - 48).toNat; bv_omega, h10.sub_left sub, h11.sub_left sub, h12.sub_left sub,
    h13.sub_left sub⟩

open VG.Proof.Hmac.Stream.PPC64LE.Init (inner inner_bytes) in
/-- `initLong`, with its frame. -/
theorem correct {s₀ : State} (hp : (longG hH.SH H.lbytes 144).pre s₀) :
    WP isa H.initLong s₀ fun s' => abiPreserved s₀ s' ∧ (longG hH.SH H.lbytes 144).post s₀ s' := by
  have hpi := pre_inner hH hp
  obtain ⟨_, _, h2, _, _, _, _, _, _, h9, h10, h11, h12, h13⟩ := hp
  have hsub : Region.Sub (below s₀.sp 48) (below s₀.sp 144) := below_sub (by omega_arith) (by omega_arith)
  refine WP.seq (Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by show 48 ≤ s₀.sp.toNat; omega_arith) (fun R hR => ?_) (WP.mono (correctMain hH hpi)
    fun s' ⟨hk, hsp, hI, hO⟩ => ?_) (by have := initLongMain_fdepth hH; omega_arith) (initLongMain_pf hH)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, h2] at hR
    have hf : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ (below s₀.sp 144) :=
      fun a h => hsub a (Proof.MdStream.PPC64LE.frame_sub s₀.sp a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h10.sub_left hf
    · exact h11.sub_left hf
    · exact h13.sub_left hf
  · refine Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have hK : K (inner s₀) = bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat :=
        Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          inner_bytes (R := ⟨s₀.gpr .r5, (s₀.gpr .r6).toNat⟩) (h12.symm.sub_right hsub).symm
            (s₀.gpr .r6).isLt hi
      rw [hK] at hI hO
      exact ⟨hI, hO⟩

end VG.Proof.Hmac.Stream.PPC64LE.InitLong
