module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Save
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Init
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic

/-!
# HMAC over any streaming hash function on PPC64LE: `finalize`

`finalizeMain` saves our caller's `r20`–`r25`, finalizes the inner state
into `scratch[dig..dig + FD)` with the streaming `finalize`, copies the outer
state's hash value over the inner one's (the inner state then represents the
outer block, `HashOK.reloc`), absorbs the inner digest (the first `D` bytes)
with `update`, finalizes again into `scratch[dig..)`, copies the digest to
`out`, and restores the registers (`correctMain`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Finalize

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.MdStream.PPC64LE (mov)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_addi contains_offset)
open VG.Proof.Hmac.Stream.PPC64LE.Init (cover_self cover_pre cover_off covers_one hv_sub w_sub sv_sub w_sv
  Regs)
open VG.WriteBytes (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .r3
abbrev out : Addr := s₀.gpr .r4
abbrev mac : Addr := s₀.gpr .r6
abbrev scr : Addr := s₀.gpr .r7
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev macR : Region := ⟨mac s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, H.W + 48 + H.FD⟩
/-- Where `finalize` writes. -/
abbrev digR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.dig, H.FD⟩
/-- The digest, the first `D` bytes of it. -/
abbrev digD : Region := ⟨scr s₀ + BitVec.ofNat 64 H.dig, H.D⟩

end

/-- `finalize`'s precondition, with the stack pointer below its frame: its
callees' frames are in the 48 bytes below it. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [outR H s₀]
  wr : s₀.wr = [inR H s₀, macR H s₀, scR H s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_m : (inR H s₀).Disjoint (macR H s₀)
  i_s : (inR H s₀).Disjoint (scR H s₀)
  o_m : (outR H s₀).Disjoint (macR H s₀)
  o_s : (outR H s₀).Disjoint (scR H s₀)
  m_s : (macR H s₀).Disjoint (scR H s₀)
  sp48 : 48 ≤ s₀.sp.toNat
  si : (below s₀.sp 48).Disjoint (inR H s₀)
  so : (below s₀.sp 48).Disjoint (outR H s₀)
  sm : (below s₀.sp 48).Disjoint (macR H s₀)
  ss : (below s₀.sp 48).Disjoint (scR H s₀)

/-- Our variables in `r20`–`r23`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = inn s₀
  r21 : s.gpr .r21 = scr s₀
  r22 : s.gpr .r22 = out s₀
  r23 : s.gpr .r23 = mac s₀
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

variable {H : Hash} (hH : HashOK H) {s₀ : State}

theorem Vars.of_pres {s s' : State} (h : Vars s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Vars s₀ s' :=
  ⟨(hc _ (by decide)).trans h.r20, (hc _ (by decide)).trans h.r21, (hc _ (by decide)).trans h.r22,
    (hc _ (by decide)).trans h.r23, fun r hr => (hc r (untouched_pres r hr)).trans (h.un r hr)⟩

/-- `Vars` after code writing only `r3`–`r8`. -/
theorem Vars.of_keep {s s' : State} (h : Vars s₀ s)
    (hc : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) :
    Vars s₀ s' := by
  have k : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31, .r20,
      .r21, .r22, .r23], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.r20, (k _ (by simp)).trans h.r21, (k _ (by simp)).trans h.r22,
    (k _ (by simp)).trans h.r23, fun r hr => (k r (by revert r; decide)).trans (h.un r hr)⟩

theorem dig_sub (p : Addr) : Region.Sub ⟨p + BitVec.ofNat 64 H.dig, H.FD⟩ ⟨p, H.W + 48 + H.FD⟩ :=
  Offset.sub_base p (by simp [Hash.dig])

theorem digD_sub (hDF : H.D ≤ H.FD) (p : Addr) :
    Region.Sub ⟨p + BitVec.ofNat 64 H.dig, H.D⟩ ⟨p + BitVec.ofNat 64 H.dig, H.FD⟩ :=
  Region.sub_prefix hDF

theorem w_dig (hW : H.W ≤ 1024) (hD : H.FD ≤ 64) (p : Addr) :
    Region.Disjoint ⟨p, H.W⟩ ⟨p + BitVec.ofNat 64 H.dig, H.FD⟩ :=
  Offset.base_disjoint p (by simp [Hash.dig]) (by simp [Hash.dig]; omega)

theorem sv_dig (hW : H.W ≤ 1024) (hD : H.FD ≤ 64) (p : Addr) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p + BitVec.ofNat 64 H.dig, H.FD⟩ :=
  Offset.disjoint p (.inl (by simp [Hash.dig])) (by omega) (by simp [Hash.dig]; omega)

theorem w_sub' (p : Addr) : Region.Sub ⟨p, H.W⟩ ⟨p, H.W + 48 + H.FD⟩ := Region.sub_prefix (by omega)
theorem sv_sub' (p : Addr) : Region.Sub ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p, H.W + 48 + H.FD⟩ :=
  Offset.sub_base p (by omega)

theorem contains_start {p : Addr} {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The hypotheses of `finalize`'s postcondition. -/
def Hyp (s₀ : State) (k0 text : List Byte) : Prop :=
  k0.length = hH.SH.H.blockSize ∧ k0.length + text.length < 2 ^ 64 ∧
    hH.SH.Repr s₀.mem (inn s₀) (xorPad k0 ipad ++ text) ∧
    s₀.gpr .r5 = BitVec.ofNat 64 (hH.SH.H.blockSize + text.length) ∧
    hH.SH.Repr s₀.mem (out s₀) (xorPad k0 opad)

/-- `finalize` without its frame: the callee-saved registers are kept. -/
theorem correctMain (hp : Pre H s₀) :
    WP isa H.finalizeMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      ∀ k0 text, Hyp hH s₀ k0 text → bytesAt s'.mem (mac s₀) H.D = hmacBlockKey hH.SH.H k0 text := by
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hW : H.W % 8 = 0 ∧ H.W ≤ 1024 := hH.dims.so
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  have hB' : H.B ≤ 128 := by omega
  have hS : H.S = H.N + H.B := rfl
  have hD := hH.hD64
  have hFD := hH.hFD64
  have hDF := hH.hDF
  have hD4 := hH.hD4
  have hdig : H.dig = H.W + 48 := rfl
  have e0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => by simp
  -- Everything the code writes, and what it never writes.
  let all : List Region := [inR H s₀, macR H s₀, scR H s₀, below s₀.sp 48]
  have out_keep : ∀ m, Frame all s₀.mem m → ∀ i < H.S,
      m (out s₀ + BitVec.ofNat 64 i) = s₀.mem (out s₀ + BitVec.ofNat 64 i) := by
    intro m hf i hi
    refine hf.bytes (R := outR H s₀) ?_ (by simp only [Hash.S]; omega) hi
    simp only [all, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [hp.i_o.symm, hp.o_m, hp.o_s, hp.so.symm]
  have dsv : ∀ R ∈ all, R ≠ scR H s₀ → Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 H.W, 48⟩ R := by
    simp only [all, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl) hne
    · exact hp.i_s.symm.sub_left (sv_sub' _)
    · exact hp.m_s.symm.sub_left (sv_sub' _)
    · exact absurd rfl hne
    · exact hp.ss.symm.sub_left (sv_sub' _)
  unfold Hash.finalizeMain
  -- Save our caller's registers, and set up ours and `finalize`'s arguments.
  refine WP.seq (save_ok hH.dims.so (b := .r7) (by decide)
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [hp.wr], contains_offset
      (show d + 8 ≤ H.W + 48 + H.FD by have : d + 8 ≤ H.W + 48 := hd₂; omega)
      (by have : d + 8 ≤ H.W + 48 := hd₂; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_addi (by omega) fun s₇ u₇ => wp_mov fun s₈ u₈ => WP.block_nil ?_
  have hr₈ : Regs s₀ s₈ :=
    ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
      by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]⟩
  have m₈ : s₈.mem = saveMem H.W s₀.mem (scr s₀) s₀.gpr := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have v₈ : Vars s₀ s₈ := by
    refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · rw [u₈.other r (by revert r; decide), u₇.other r (by revert r; decide), u₆.other r (by revert r; decide),
        u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), g₁]
  have h3₈ : s₈.gpr .r3 = inn s₀ := by
    simp only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have h4₈ : s₈.gpr .r4 = s₀.gpr .r5 := by
    simp only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have h5₈ : s₈.gpr .r5 = scr s₀ + BitVec.ofNat 64 H.dig := by
    simp only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have h6₈ : s₈.gpr .r6 = scr s₀ := by
    simp only [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have fS : Frame [⟨scr s₀, H.W + 48⟩] s₀.mem s₈.mem := by rw [m₈]; exact saveMem_frame hH.dims.so _ _ _
  have f₈ : Frame all s₀.mem s₈.mem :=
    fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR H s₀, by simp [all], Region.sub_prefix (by omega)⟩
  have sv₈ : Saved H.W (scr s₀) s₀.gpr s₈.mem := by rw [m₈]; exact saveMem_saved hH.dims.so _ _ _
  have hrI₈ : ∀ k0 text, Hyp hH s₀ k0 text → hH.SH.Repr s₈.mem (inn s₀) (xorPad k0 ipad ++ text) :=
    fun k0 text h => hH.congr s₀.mem s₈.mem (inn s₀) _ (fun i hi => fS.bytes (R := inR H s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (Region.sub_prefix (by omega)))
      (by simp only [Hash.S]; omega) hi) h.2.2.1
  have hlen : ∀ k0 text, Hyp hH s₀ k0 text → (xorPad k0 ipad ++ text).length = H.B + text.length := by
    intro k0 text h; simp [xorPad, h.1, hH.hB]
  -- The inner digest into `scratch`.
  have dsDig : (inR H s₀).Disjoint (digR H s₀) := hp.i_s.sub_right (dig_sub _)
  have dsW : (inR H s₀).Disjoint ⟨scr s₀, H.W⟩ := hp.i_s.sub_right (w_sub' _)
  refine WP.seq (hH.callFin_ok (st := inn s₀) (o := scr s₀ + BitVec.ofNat 64 H.dig) (scr := scr s₀)
    h3₈ h5₈ h6₈ dsDig dsW (w_dig hW.2 hFD _).symm (by rw [hr₈.sp]; exact hp.sp48) (by rw [hr₈.sp]; exact hp.si)
    (by rw [hr₈.sp]; exact hp.ss.sub_right (dig_sub _)) (by rw [hr₈.sp]; exact hp.ss.sub_right (w_sub' _))
    (by
      rw [hr₈.rd, hr₈.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_self (by simp)
      · exact cover_off (R := scR H s₀) (by simp) (by simp [Hash.dig])
      · exact cover_pre (R := scR H s₀) (by simp) (by simp only; omega))
    (by
      rw [hr₈.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_self (by simp)
      · exact cover_off (R := scR H s₀) (by simp) (by simp [Hash.dig])
      · exact cover_pre (R := scR H s₀) (by simp) (by simp only; omega))
    fun s₉ rd₉ wr₉ sp₉ f₉ cs₉ hfin₉ => ?_)
  rw [hr₈.sp] at f₉
  have hr₉ : Regs s₀ s₉ := ⟨rd₉.trans hr₈.rd, wr₉.trans hr₈.wr, sp₉.trans hr₈.sp⟩
  have v₉ : Vars s₀ s₉ := v₈.of_pres cs₉
  have f₉' : Frame all s₀.mem s₉.mem := f₈.trans (f₉.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨inR H s₀, by simp [all], fun _ h => h⟩
    · exact ⟨scR H s₀, by simp [all], dig_sub _⟩
    · exact ⟨scR H s₀, by simp [all], w_sub' _⟩
    · exact ⟨below s₀.sp 48, by simp [all], fun _ h => h⟩)
  have sv₉ : Saved H.W (scr s₀) s₀.gpr s₉.mem := by
    refine saved_keep sv₈ f₉ fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.i_s.symm.sub_left (sv_sub' _)
    · exact sv_dig hW.2 hFD _
    · exact (w_sv hW.2 _).symm
    · exact hp.ss.symm.sub_left (sv_sub' _)
  have hdg₉ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₉.mem (scr s₀ + BitVec.ofNat 64 H.dig) H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) := by
    intro k0 text h
    rw [bytesAt_take _ _ hDF, hfin₉ _ (hrI₈ k0 text h) (by rw [hlen k0 text h, ← hH.hB, ← h.1]; exact h.2.1)
      (by rw [h4₈, hlen k0 text h, ← hH.hB]; exact h.2.2.2.1), hH.hashTake]
  -- The outer hash value over the inner one's.
  have hN4 : 4 * (H.N / 4) = H.N := by have := hH.hN4; omega
  refine WP.seq (copy32_ok (src := .r22) (dst := .r20) (by decide) (by decide) (by decide) (by decide) 0 0
    (H.N / 4) ⟨by omega, by omega⟩ _ s₉ _
    (fun k hk => ⟨outR H s₀, by simp [hr₉.rd, hr₉.wr, hp.rd], by
      rw [v₉.r22, e0]; exact contains_offset (by simp only [Hash.S]; omega) (by omega)⟩)
    (fun k hk => ⟨inR H s₀, by simp [hr₉.wr, hp.wr], by
      rw [v₉.r20, e0]; exact contains_offset (by simp only [Hash.S]; omega) (by omega)⟩)
    (by
      rw [v₉.r22, v₉.r20, e0, e0]
      exact hp.i_o.symm.sep (contains_start (by simp only [Hash.S]; omega))
        (contains_start (by simp only [Hash.S]; omega)))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ m₁₀ => ?_)
  rw [v₉.r20, v₉.r22, e0, e0, hN4] at m₁₀
  refine wp_mov fun s₁₁ u₁₁ => wp_li (by omega) fun s₁₂ u₁₂ => wp_addi (by omega) fun s₁₃ u₁₃ =>
    wp_li (by omega) fun s₁₄ u₁₄ => wp_mov fun s₁₅ u₁₅ => WP.block_nil ?_
  have hr₁₅ : Regs s₀ s₁₅ :=
    ⟨by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀, hr₉.rd],
      by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀, hr₉.wr],
      by rw [u₁₅.sp, u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀, hr₉.sp]⟩
  have m₁₅ : s₁₅.mem = s₁₀.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have v₁₅ : Vars s₀ s₁₅ := v₉.of_keep fun r a b c d e f => by
    rw [u₁₅.other r e, u₁₄.other r d, u₁₃.other r c, u₁₂.other r b, u₁₁.other r a, g₁₀ r f]
  have fC : Frame [inR H s₀] s₉.mem s₁₀.mem := by
    rw [m₁₀]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]; exact contains_start (by simp only [Hash.S]; omega))
  have f₁₅ : Frame all s₀.mem s₁₅.mem := by
    rw [m₁₅]; exact f₉'.trans (fC.mono (by simp [all]))
  have sv₁₅ : Saved H.W (scr s₀) s₀.gpr s₁₅.mem := by
    rw [m₁₅]
    exact saved_keep sv₉ fC (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (sv_sub' _))
  have hrO₁₅ : ∀ k0 text, Hyp hH s₀ k0 text → hH.SH.Repr s₁₅.mem (inn s₀) (xorPad k0 opad) := by
    intro k0 text h
    refine hH.reloc s₀.mem s₁₅.mem (out s₀) (inn s₀) _ (by simp [xorPad, h.1, hH.hB]) (fun i hi => ?_) h.2.2.2.2
    rw [m₁₅, m₁₀, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length]; exact hi)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega)]
    rw [show (bytesAt s₉.mem (out s₀) H.N).getD i 0 = s₉.mem (out s₀ + BitVec.ofNat 64 i) by
      simp [bytesAt, List.getD_eq_getElem?_getD, hi]]
    exact out_keep _ f₉' i (by simp only [Hash.S]; omega)
  have hdg₁₅ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₁₅.mem (scr s₀ + BitVec.ofNat 64 H.dig) H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) := by
    intro k0 text h
    rw [← hdg₉ k0 text h, m₁₅]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi => fC.bytes (R := digD H s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (dsDig.sub_right (digD_sub hDF _)).symm)
      (by show H.D ≤ 2 ^ 64; omega) hi
  -- Absorb the inner digest.
  have dDigW : Region.Disjoint (digD H s₀) ⟨scr s₀, H.W⟩ :=
    ((w_dig hW.2 hFD _).sub_right (digD_sub hDF _)).symm
  refine WP.seq (hH.callUpd_ok (st := inn s₀) (dat := scr s₀ + BitVec.ofNat 64 H.dig) (scr := scr s₀)
    (len := H.D)
    (by simp only [u₁₅.other, u₁₄.other, u₁₃.other, u₁₂.other, u₁₁.gpr, ne_eq, reduceCtorEq,
      not_false_eq_true]; rw [g₁₀ _ (by decide), v₉.r20])
    (by simp only [u₁₅.other, u₁₄.other, u₁₃.gpr, ne_eq, reduceCtorEq, not_false_eq_true]
        rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), g₁₀ _ (by decide), v₉.r21])
    (by rw [u₁₅.other _ (by decide), u₁₄.gpr]; exact Proof.MdStream.PPC64LE.toNat_ofNat_lt (by omega))
    (by rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), g₁₀ _ (by decide), v₉.r21])
    dsW (dsDig.sub_right (digD_sub hDF _)).symm dDigW (by rw [hr₁₅.sp]; exact hp.sp48)
    (by rw [hr₁₅.sp]; exact hp.si)
    (by rw [hr₁₅.sp]; exact hp.ss.sub_right (fun a h => dig_sub _ a (digD_sub hDF _ a h)))
    (by rw [hr₁₅.sp]; exact hp.ss.sub_right (w_sub' _))
    (by
      rw [hr₁₅.rd, hr₁₅.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_off (R := scR H s₀) (by simp) (by simp only [Hash.dig]; omega)
      · exact cover_self (by simp)
      · exact cover_pre (R := scR H s₀) (by simp) (by simp only; omega))
    (by
      rw [hr₁₅.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cover_self (by simp)
      · exact cover_pre (R := scR H s₀) (by simp) (by simp only; omega))
    fun s₁₆ rd₁₆ wr₁₆ sp₁₆ f₁₆ cs₁₆ hup₁₆ => ?_)
  rw [hr₁₅.sp] at f₁₆
  have hr₁₆ : Regs s₀ s₁₆ := ⟨rd₁₆.trans hr₁₅.rd, wr₁₆.trans hr₁₅.wr, sp₁₆.trans hr₁₅.sp⟩
  have v₁₆ : Vars s₀ s₁₆ := v₁₅.of_pres cs₁₆
  have h4₁₅ : s₁₅.gpr .r4 = BitVec.ofNat 64 H.B := by
    rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr]
  have hrI₁₆ : ∀ k0 text, Hyp hH s₀ k0 text →
      hH.SH.Repr s₁₆.mem (inn s₀) (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ text)) := by
    intro k0 text h
    have := hup₁₆ _ (hrO₁₅ k0 text h) (by rw [h4₁₅]; simp [xorPad, h.1, hH.hB])
    rwa [hdg₁₅ k0 text h] at this
  have sv₁₆ : Saved H.W (scr s₀) s₀.gpr s₁₆.mem := by
    refine saved_keep sv₁₅ f₁₆ fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.i_s.symm.sub_left (sv_sub' _)
    · exact (w_sv hW.2 _).symm
    · exact hp.ss.symm.sub_left (sv_sub' _)
  -- The outer hash, into `scratch`.
  refine WP.seq (wp_mov fun s₁₇ u₁₇ => wp_li (by omega) fun s₁₈ u₁₈ => wp_addi (by omega) fun s₁₉ u₁₉ =>
    wp_mov fun s₂₀ u₂₀ => WP.block_nil ?_)
  have hr₂₀ : Regs s₀ s₂₀ :=
    ⟨by rw [u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, hr₁₆.rd], by rw [u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, hr₁₆.wr],
      by rw [u₂₀.sp, u₁₉.sp, u₁₈.sp, u₁₇.sp, hr₁₆.sp]⟩
  have m₂₀ : s₂₀.mem = s₁₆.mem := by rw [u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem]
  have v₂₀ : Vars s₀ s₂₀ := v₁₆.of_keep fun r a b c d _ _ => by
    rw [u₂₀.other r d, u₁₉.other r c, u₁₈.other r b, u₁₇.other r a]
  refine WP.seq (hH.callFin_ok (st := inn s₀) (o := scr s₀ + BitVec.ofNat 64 H.dig) (scr := scr s₀)
    (by rw [u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.gpr, v₁₆.r20])
    (by rw [u₂₀.other _ (by decide), u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide), v₁₆.r21])
    (by rw [u₂₀.gpr, u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide), v₁₆.r21])
    dsDig dsW (w_dig hW.2 hFD _).symm (by rw [hr₂₀.sp]; exact hp.sp48) (by rw [hr₂₀.sp]; exact hp.si)
    (by rw [hr₂₀.sp]; exact hp.ss.sub_right (dig_sub _)) (by rw [hr₂₀.sp]; exact hp.ss.sub_right (w_sub' _))
    (by
      rw [hr₂₀.rd, hr₂₀.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_self (by simp)
      · exact cover_off (R := scR H s₀) (by simp) (by simp [Hash.dig])
      · exact cover_pre (R := scR H s₀) (by simp) (by simp only; omega))
    (by
      rw [hr₂₀.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cover_self (by simp)
      · exact cover_off (R := scR H s₀) (by simp) (by simp [Hash.dig])
      · exact cover_pre (R := scR H s₀) (by simp) (by simp only; omega))
    fun s₂₁ rd₂₁ wr₂₁ sp₂₁ f₂₁ cs₂₁ hfin₂₁ => ?_)
  rw [hr₂₀.sp] at f₂₁
  have hr₂₁ : Regs s₀ s₂₁ := ⟨rd₂₁.trans hr₂₀.rd, wr₂₁.trans hr₂₀.wr, sp₂₁.trans hr₂₀.sp⟩
  have v₂₁ : Vars s₀ s₂₁ := v₂₀.of_pres cs₂₁
  have hmac₂₁ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₂₁.mem (scr s₀ + BitVec.ofNat 64 H.dig) H.D = hmacBlockKey hH.SH.H k0 text := by
    intro k0 text h
    have hl : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ text)).length = H.B + H.D := by
      simp [xorPad, h.1, hH.hB, hH.hashLen]
    rw [bytesAt_take _ _ hDF, hfin₂₁ _ (by rw [m₂₀]; exact hrI₁₆ k0 text h) (by rw [hl]; omega)
      (by rw [hl, u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr]), ← hH.hashTake]
    rfl
  have sv₂₁ : Saved H.W (scr s₀) s₀.gpr s₂₁.mem := by
    refine saved_keep (by rw [m₂₀]; exact sv₁₆) f₂₁ fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.i_s.symm.sub_left (sv_sub' _)
    · exact sv_dig hW.2 hFD _
    · exact (w_sv hW.2 _).symm
    · exact hp.ss.symm.sub_left (sv_sub' _)
  -- The digest, into `out`.
  have hD44 : 4 * (H.D / 4) = H.D := by omega
  have dMD : (macR H s₀).Disjoint (digD H s₀) :=
    hp.m_s.sub_right (fun a h => dig_sub _ a (digD_sub hDF _ a h))
  refine copy32_ok (src := .r21) (dst := .r23) (by decide) (by decide) (by decide) (by decide) H.dig 0
    (H.D / 4) ⟨by omega, by omega⟩ _ s₂₁ _
    (fun k hk => ⟨scR H s₀, by simp [hr₂₁.rd, hr₂₁.wr, hp.wr], by
      rw [v₂₁.r21, ← add_off]; exact contains_offset (by simp only [Hash.dig]; omega) (by omega)⟩)
    (fun k hk => ⟨macR H s₀, by simp [hr₂₁.wr, hp.wr], by
      rw [v₂₁.r23, e0]; exact contains_offset (by omega) (by omega)⟩)
    (by
      rw [v₂₁.r21, v₂₁.r23, e0, hD44]
      exact dMD.symm.sep (contains_start (Nat.le_refl _)) (contains_start (Nat.le_refl _)))
    fun s₂₂ g₂₂ rd₂₂ wr₂₂ sp₂₂ m₂₂ => ?_
  rw [v₂₁.r21, v₂₁.r23, e0, hD44] at m₂₂
  have hr₂₂ : Regs s₀ s₂₂ := ⟨rd₂₂.trans hr₂₁.rd, wr₂₂.trans hr₂₁.wr, sp₂₂.trans hr₂₁.sp⟩
  have v₂₂ : Vars s₀ s₂₂ := v₂₁.of_keep fun r _ _ _ _ _ h => g₂₂ r h
  have hmac : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₂₂.mem (mac s₀) H.D = hmacBlockKey hH.SH.H k0 text := by
    intro k0 text h
    rw [← hmac₂₁ k0 text h, m₂₂]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₂₁.mem (mac s₀)
      (bytesAt s₂₁.mem (scr s₀ + BitVec.ofNat 64 H.dig) H.D)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega)
    rwa [VG.Proof.Hmac.Common.bytesAt_length] at this
  have sv₂₂ : Saved H.W (scr s₀) s₀.gpr s₂₂.mem := by
    rw [m₂₂]
    refine saved_keep sv₂₁ (VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]; exact contains_start (Nat.le_refl _))) ?_
    simp only [List.mem_singleton]; rintro r rfl; exact hp.m_s.symm.sub_left (sv_sub' _)
  -- Restore our caller's registers.
  refine restore_ok hH.dims.so (scr := scr s₀) v₂₂.r21
    (fun d hd₁ hd₂ => ⟨scR H s₀, by simp [hr₂₂.rd, hr₂₂.wr, hp.wr],
      contains_offset (show d + 8 ≤ H.W + 48 + H.FD by have : d + 8 ≤ H.W + 48 := hd₂; omega)
      (by have : d + 8 ≤ H.W + 48 := hd₂; omega)⟩)
    s₀.gpr sv₂₂ fun s' hsv ho hmem _ _ hsp => ⟨preserved_of hsv fun r hr => ?_, by rw [hsp, hr₂₂.sp],
      fun k0 text h => by rw [hmem]; exact hmac k0 text h⟩
  rw [ho r (by simp only [Hash.savedAt, List.map_cons, List.map_nil]; revert r; decide)]
  exact v₂₂.un r hr

/-! ## The frame -/

include hH in
theorem finalizeMain_fdepth : H.finalizeMain.fdepth ≤ 1 := by
  have := hH.finFd
  have := hH.updFd
  simp only [Hash.finalizeMain, Hash.callFin, Hash.callUpd, Code.fdepth, Nat.max_le]
  omega

include hH in
theorem finalizeMain_pf : pushFrames H.finalizeMain = true := by
  simp [Hash.finalizeMain, Hash.callFin, Hash.callUpd, pushFrames, hH.finPf, hH.updPf]

open VG.Proof.Hmac.Stream.PPC64LE.Init (inner inner_bytes) in
theorem pre_inner {s₀ : State} (hp : (finG hH.SH (H.W + 48 + H.FD) 96).pre s₀) : Pre H (inner s₀) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hp
  rw [hH.hS, hH.hD] at *
  have sub : Region.Sub (below (s₀.sp - 48) 48) (below s₀.sp 96) := below_body s₀.sp 48
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by show 48 ≤ (s₀.sp - 48).toNat; bv_omega, h10.sub_left sub,
    h11.sub_left sub, h12.sub_left sub, h13.sub_left sub⟩

open VG.Proof.Hmac.Stream.PPC64LE.Init (inner inner_bytes) in
/-- `finalize`, with its frame. -/
theorem correct {s₀ : State} (hp : (finG hH.SH (H.W + 48 + H.FD) 96).pre s₀) :
    WP isa H.finalize s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH (H.W + 48 + H.FD) 96).post s₀ s' := by
  have hpi := pre_inner hH hp
  obtain ⟨h1, h2, _, _, _, _, _, _, h9, h10, h11, h12, h13⟩ := hp
  have hsub : Region.Sub (below s₀.sp 48) (below s₀.sp 96) := below_sub (by omega) (by omega)
  refine WP.seq (Proof.MdStream.PPC64LE.WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by show 48 ≤ s₀.sp.toNat; omega) (fun R hR => ?_) (WP.mono (correctMain hH hpi)
    fun s' ⟨hk, hsp, hpost⟩ => ?_) (by have := finalizeMain_fdepth hH; omega) (finalizeMain_pf hH)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, h2] at hR
    have hf : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ (below s₀.sp 96) :=
      fun a h => hsub a (Proof.MdStream.PPC64LE.frame_sub s₀.sp a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h10.sub_left hf
    · exact h12.sub_left hf
    · exact h13.sub_left hf
  · refine Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · intro k0 text hk0 hl hI hc hO
      rw [hH.hD]
      refine hpost k0 text ⟨hk0, hl, ?_, hc, ?_⟩
      · refine hH.congr s₀.mem _ _ _ (fun i hi => ?_) hI
        exact inner_bytes (R := ⟨s₀.gpr .r3, H.S⟩) (by rw [← hH.hS]; exact h10.sub_left hsub)
          (by have h1 : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N; have h2 : H.B = 64 ∨ H.B = 128 := hH.dims.B
              simp only [Hash.S]; omega) hi
      · refine hH.congr s₀.mem _ _ _ (fun i hi => ?_) hO
        exact inner_bytes (R := ⟨s₀.gpr .r4, H.S⟩) (by rw [← hH.hS]; exact h11.sub_left hsub)
          (by have h1 : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N; have h2 : H.B = 64 ∨ H.B = 128 := hH.dims.B
              simp only [Hash.S]; omega) hi

end VG.Proof.Hmac.Stream.PPC64LE.Finalize
