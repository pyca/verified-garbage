module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Init
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc

/-!
# HMAC over any streaming hash function on RISC-V: `finalize`

`finalize` allocates its frame (`fr`, `fbytes` bytes: the inner digest, then
our caller's `ra` and `s7`–`s11` at `fso`), finalizes the inner state into
it with the streaming `finalize`, copies the outer state's hash value over
the inner one's a byte at a time (`copy8_ok`; the inner state then represents
the outer block, `HashOK.reloc`), absorbs the inner digest with `update`,
finalizes again into `out`, and restores the registers (`finalizeMain_ok`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Finalize

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_mv wp_addi wp_addSp wp_lbu wp_sb)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64.Init (Regs cover_self cover_pre hv_sub nv_pres)
open VG.WriteBytes (writeBytes writeBytes_nil)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## Copying bytes -/

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = bytesAt m p n ++ [m (p + BitVec.ofNat 64 n)] := by
  simp [bytesAt, List.range_succ]

/-- `n` bytes copied from `src` to `dst`, a byte at a time through `t1`. -/
theorem copy8_ok {src dst : Reg} (hs : src ≠ .t1) (hd : dst ≠ .t1) (n : Nat) (hn : n ≤ 2048) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 k) 1) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 k) 1) →
    Mem.Sep (s.gpr src) n (s.gpr dst) n →
    (∀ s', (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst) (bytesAt s.mem (s.gpr src) n) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (fun k => [.load .b .t1 src k, .store .b .t1 dst k]) ++ rest))
      s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by
      rw [VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_lbu (a := s.gpr src + BitVec.ofNat 64 n) (by omega) (by rw [g₁ _ hs])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_sb (a := s.gpr dst + BitVec.ofNat 64 n) (by omega) (by rw [u₂.other _ hd, g₁ _ hd])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ =>
      k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    have hrd : s₁.mem (s.gpr src + BitVec.ofNat 64 n) = s.mem (s.gpr src + BitVec.ofNat 64 n) := by
      rw [m₁]
      refine VG.Proof.Hmac.Common.writeBytes_other _ _ _ ?_
      rw [VG.Proof.Hmac.Common.bytesAt_length]
      intro hlt
      refine hsep (s.gpr src + BitVec.ofNat 64 n) ?_ (by omega)
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      ← m₁, hrd, m₁, bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega),
      VG.Proof.Hmac.Common.bytesAt_length]

theorem contains_start {p : Addr} {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

/-- The frame. -/
abbrev fr : Addr := s₀.sp
abbrev inn : Addr := s₀.gpr .a0
abbrev out : Addr := s₀.gpr .a1
abbrev mac : Addr := s₀.gpr .a3
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev macR : Region := ⟨mac s₀, H.D⟩
abbrev frR : Region := ⟨fr s₀, H.fbytes⟩
/-- The inner digest, at the start of the frame. -/
abbrev digR : Region := ⟨fr s₀, H.D⟩
abbrev stk : Region := below (fr s₀) H.F
abbrev svR : Region := ⟨fr s₀ + BitVec.ofNat 64 H.fso, 48⟩

end

/-- The state the frame's body starts in. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [outR H s₀]
  wr : s₀.wr = [frR H s₀, inR H s₀, macR H s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_m : (inR H s₀).Disjoint (macR H s₀)
  o_m : (outR H s₀).Disjoint (macR H s₀)
  f_i : (frR H s₀).Disjoint (inR H s₀)
  f_o : (frR H s₀).Disjoint (outR H s₀)
  f_m : (frR H s₀).Disjoint (macR H s₀)
  al : s₀.sp.toNat % 16 = 0
  spF : H.F ≤ s₀.sp.toNat
  top : s₀.sp.toNat + H.fbytes ≤ 2 ^ 64
  s_i : (stk H s₀).Disjoint (inR H s₀)
  s_o : (stk H s₀).Disjoint (outR H s₀)
  s_m : (stk H s₀).Disjoint (macR H s₀)

/-- Our variables in `s7`–`s10`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = inn s₀
  s8 : s.gpr .s8 = fr s₀
  s9 : s.gpr .s9 = out s₀
  s10 : s.gpr .s10 = mac s₀
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

variable {H : Hash} {s₀ : State}

theorem Vars.of_pres {s s' : State} (h : Vars s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Vars s₀ s' :=
  ⟨(hc _ (by decide)).trans h.s7, (hc _ (by decide)).trans h.s8, (hc _ (by decide)).trans h.s9,
    (hc _ (by decide)).trans h.s10, fun r hr => (hc r (nv_pres r hr)).trans (h.nv r hr)⟩

/-- `Vars` after code writing only `a0`–`a3` and `t1`. -/
theorem Vars.of_keep {s s' : State} (h : Vars s₀ s)
    (hc : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .t1 → s'.gpr r = s.gpr r) : Vars s₀ s' := by
  have k : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.s7, (k _ (by simp)).trans h.s8, (k _ (by simp)).trans h.s9,
    (k _ (by simp)).trans h.s10, fun r hr => (k r (by revert r; decide)).trans (h.nv r hr)⟩

theorem Pre.f_s (hp : Pre H s₀) : (frR H s₀).Disjoint (stk H s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spF; have := s₀.sp.isLt; omega_arith)

theorem dig_sub (hl : Lay H) : Region.Sub (digR H s₀) (frR H s₀) :=
  Region.sub_prefix (by have := hl.fso; have := hl.fbytes; omega_arith)

theorem sv_sub (hl : Lay H) : Region.Sub (svR H s₀) (frR H s₀) :=
  Offset.sub_base _ hl.fbytes.1

theorem dig_sv (hl : Lay H) : Region.Disjoint (digR H s₀) (svR H s₀) :=
  Offset.base_disjoint _ hl.fso.1 (by have := hl.fbytes; omega_arith)

/-- The hypotheses of `finalize`'s postcondition. -/
def Hyp (hH : HashOK H) (s₀ : State) (k0 text : List Byte) : Prop :=
  k0.length = hH.SH.H.blockSize ∧ k0.length + text.length < 2 ^ 64 ∧
    hH.SH.Repr s₀.mem (inn s₀) (xorPad k0 ipad ++ text) ∧
    s₀.gpr .a2 = BitVec.ofNat 64 (hH.SH.H.blockSize + text.length) ∧
    hH.SH.Repr s₀.mem (out s₀) (xorPad k0 opad)

/-- `finalize`'s postcondition, in its frame. -/
def Post (hH : HashOK H) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ s'.wr = s₀.wr ∧
    ∀ k0 text, Hyp hH s₀ k0 text → bytesAt s'.mem (mac s₀) H.D = hmacBlockKey hH.SH.H k0 text

/-- `finalizeMain`, with `saveAt` as `Spill`'s. -/
theorem finalizeMain_eq (H : Hash) : H.finalizeMain =
    .seq (.block (.addSp .t0 0 :: (Spill.saveCode .t0 (Hash.savedAt H.fso) ++
      [mov .s7 .a0, mov .s8 .t0, mov .s9 .a1, mov .s10 .a3, mov .a1 .a2, mov .a2 .t0])))
    (.seq H.callFin
    (.seq (.block ((List.range H.N).flatMap (fun k => [.load .b .t1 .s9 k, .store .b .t1 .s7 k]) ++
        [mov .a0 .s7, .li .a1 H.B, mov .a2 .s8, .li .a3 H.D]))
    (.seq H.callUpd
    (.seq (.block [mov .a0 .s7, .li .a1 (H.B + H.D), mov .a2 .s10])
    (.seq H.callFin
      (.block (Spill.restoreCode .s8 (restList H.fso)))))))) := by
  simp only [Hash.finalizeMain, saveAt_eq, restoreAt_eq, Hash.copyHV, List.cons_append]

variable (hH : HashOK H)
include hH

/-- `finalize`, in its frame. -/
theorem finalizeMain_ok (hp : Pre H s₀) : WP isa H.finalizeMain s₀ (Post hH s₀) := by
  have hl := hH.lay
  have hN := hl.N
  have hB := hl.B
  have hD := hl.D
  have hfso := hl.fso
  have hfb := hl.fbytes
  have hS : H.S = H.N + H.B := rfl
  have hal8 : (fr s₀).toNat % 8 = 0 := by show s₀.sp.toNat % 8 = 0; have := hp.al; omega
  have hwf : frR H s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self
  have hwi : inR H s₀ ∈ s₀.wr := by simp [hp.wr]
  have hwm : macR H s₀ ∈ s₀.wr := by simp [hp.wr]
  have hro : outR H s₀ ∈ s₀.rd := by simp [hp.rd]
  have i_d : (inR H s₀).Disjoint (digR H s₀) := hp.f_i.symm.sub_right (dig_sub hl)
  have s_d : (stk H s₀).Disjoint (digR H s₀) := hp.f_s.symm.sub_right (dig_sub hl)
  have sv_i : (svR H s₀).Disjoint (inR H s₀) := hp.f_i.sub_left (sv_sub hl)
  have sv_m : (svR H s₀).Disjoint (macR H s₀) := hp.f_m.sub_left (sv_sub hl)
  have sv_s : (svR H s₀).Disjoint (stk H s₀) := hp.f_s.sub_left (sv_sub hl)
  have hcovD : VG.Covers [digR H s₀] s₀.wr := cover_pre hwf (show H.D ≤ H.fbytes by omega)
  -- Writes outside the outer state, which keep it.
  have out_keep : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → (∀ r ∈ rs, (outR H s₀).Disjoint r) →
      ∀ i < H.S, m' (out s₀ + BitVec.ofNat 64 i) = m (out s₀ + BitVec.ofNat 64 i) :=
    fun hf hd i hi => hf.bytes (R := outR H s₀) hd (by show H.S ≤ 2 ^ 64; omega) hi
  rw [finalizeMain_eq]
  -- Save our caller's registers, and set up ours and `finalize`'s arguments.
  refine WP.seq (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  have t0₁ : s₁.gpr .t0 = fr s₀ := by rw [u₁.gpr, BitVec.add_zero]
  refine Spill.save_ok (by rw [t0₁]; exact hal8) (savedAt_off ⟨hfso.2, by omega⟩)
    (fun p hp' => ⟨frR H s₀, by rw [u₁.wr]; exact hwf,
      (by
        rw [t0₁]
        have := savedAt_in p hp'
        exact Offset.contains_base (k := H.fbytes) _ (by omega) (by omega))⟩) ?_
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  have r₈ : Regs s₀ s₈ := ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]; exact u₁.rd,
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact u₁.wr,
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]; exact u₁.sp⟩
  have v₈ : Vars s₀ s₈ :=
    ⟨by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; exact u₁.other _ (by decide),
      by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact t0₁,
      by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      fun r hr => by
        rw [u₈.other r (by revert r; decide), u₇.other r (by revert r; decide),
          u₆.other r (by revert r; decide), u₅.other r (by revert r; decide),
          u₄.other r (by revert r; decide), u₃.other r (by revert r; decide)]
        exact u₁.other r (by revert r; decide)⟩
  have a0₈ : s₈.gpr .a0 = inn s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide)
  have a1₈ : s₈.gpr .a1 = s₀.gpr .a2 := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₁.other _ (by decide)
  have a2₈ : s₈.gpr .a2 = fr s₀ := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]; exact t0₁
  have m₈ : s₈.mem = Spill.saveMem s₀.mem (fr s₀) s₁.gpr (Hash.savedAt H.fso) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, t0₁, u₁.mem]
  have f₈ : Frame [svR H s₀] s₀.mem s₈.mem := by
    rw [m₈]; exact Spill.saveMem_frame savedAt_in (by have := hp.top; omega) _ _ _
  have sv₈ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.fso) s₈.mem := by
    rw [m₈]
    intro p hp'
    rw [Spill.saveMem_saved (savedAt_fits ⟨hfso.2, by omega⟩) _ _ _ p hp']
    refine u₁.other _ ?_
    simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hlen : ∀ k0 text, Hyp hH s₀ k0 text → (xorPad k0 ipad ++ text).length = H.B + text.length := by
    intro k0 text h; simp [xorPad, h.1, hH.hB]
  have hrI₈ : ∀ k0 text, Hyp hH s₀ k0 text → hH.SH.Repr s₈.mem (inn s₀) (xorPad k0 ipad ++ text) :=
    fun k0 text h => hH.congr s₀.mem s₈.mem (inn s₀) _ (fun i hi => f₈.bytes (R := inR H s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact sv_i.symm)
      (by show H.S ≤ 2 ^ 64; omega) hi) h.2.2.1
  -- The inner digest, into the frame.
  refine WP.seq (hH.callFin_ok (st := inn s₀) (o := fr s₀) a0₈ a2₈ i_d (by rw [r₈.sp]; exact hp.al)
    (by rw [r₈.sp]; exact hp.spF) (by rw [r₈.sp]; exact hp.s_i) (by rw [r₈.sp]; exact s_d)
    (by rw [r₈.rd, r₈.wr]; exact (VG.Covers.pair (cover_self hwi) hcovD).right)
    (by rw [r₈.wr]; exact VG.Covers.pair (cover_self hwi) hcovD)
    fun s₉ rd₉ wr₉ sp₉ f₉ cs₉ hfin₉ => ?_)
  rw [r₈.sp] at f₉
  have r₉ : Regs s₀ s₉ := ⟨rd₉.trans r₈.rd, wr₉.trans r₈.wr, sp₉.trans r₈.sp⟩
  have v₉ := v₈.of_pres cs₉
  have hrs₉ : ∀ r ∈ [inR H s₀, digR H s₀] ++ [stk H s₀], (outR H s₀).Disjoint r ∧ (svR H s₀).Disjoint r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨hp.i_o.symm, sv_i⟩
    · exact ⟨hp.f_o.symm.sub_right (dig_sub hl), (dig_sv hl).symm⟩
    · exact ⟨hp.s_o.symm, sv_s⟩
  have sv₉ := sv₈.frame_in savedAt_in f₉ fun r hr => (hrs₉ r hr).2
  have hdg₉ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₉.mem (fr s₀) H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) := fun k0 text h =>
    hfin₉ _ (hrI₈ k0 text h) (by rw [hlen k0 text h, ← hH.hB, ← h.1]; exact h.2.1)
      (by rw [a1₈, hlen k0 text h, ← hH.hB]; exact h.2.2.2.1)
  -- The outer hash value over the inner one's.
  have e0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => by simp
  refine WP.seq (copy8_ok (src := .s9) (dst := .s7) (by decide) (by decide) H.N (by omega) _ s₉ _
    (fun k hk => ⟨outR H s₀, by rw [r₉.rd, r₉.wr]; exact List.mem_append_left _ hro, by
      rw [v₉.s9]; exact Offset.contains_base _ (show k + 1 ≤ H.S by omega) (by omega)⟩)
    (fun k hk => ⟨inR H s₀, by rw [r₉.wr]; exact hwi, by
      rw [v₉.s7]; exact Offset.contains_base _ (show k + 1 ≤ H.S by omega) (by omega)⟩)
    (by
      rw [v₉.s9, v₉.s7]
      exact hp.i_o.symm.sep (contains_start (show H.N ≤ H.S by omega))
        (contains_start (show H.N ≤ H.S by omega)))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ m₁₀ => ?_)
  rw [v₉.s7, v₉.s9] at m₁₀
  refine wp_mv fun s₁₁ u₁₁ => wp_li (by omega) fun s₁₂ u₁₂ => wp_mv fun s₁₃ u₁₃ =>
    wp_li (by omega) fun s₁₄ u₁₄ => WP.block_nil ?_
  have r₁₄ : Regs s₀ s₁₄ := ⟨by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀, r₉.rd],
    by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀, r₉.wr], by rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀, r₉.sp]⟩
  have m₁₄ : s₁₄.mem = s₁₀.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have v₁₄ : Vars s₀ s₁₄ := v₉.of_keep fun r a b c d e => by
    rw [u₁₄.other r d, u₁₃.other r c, u₁₂.other r b, u₁₁.other r a, g₁₀ r e]
  have fC : Frame [inR H s₀] s₉.mem s₁₀.mem := by
    rw [m₁₀]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]
      exact contains_start (show H.N ≤ H.S by omega))
  have sv₁₄ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.fso) s₁₄.mem := by
    rw [m₁₄]
    exact sv₉.frame_in savedAt_in fC (by simp only [List.mem_singleton]; rintro r rfl; exact sv_i)
  have hrO₁₄ : ∀ k0 text, Hyp hH s₀ k0 text → hH.SH.Repr s₁₄.mem (inn s₀) (xorPad k0 opad) := by
    intro k0 text h
    refine hH.reloc s₀.mem s₁₄.mem (out s₀) (inn s₀) _ (by simp [xorPad, h.1, hH.hB]) (fun i hi => ?_)
      h.2.2.2.2
    rw [m₁₄, m₁₀, VG.Proof.Hmac.Common.writeBytes_at _ _ _
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; exact hi)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega), VG.Proof.Hmac.Common.bytesAt_getD' _ _ hi,
      out_keep f₉ (fun r hr => (hrs₉ r hr).1) i (by omega)]
    exact out_keep f₈ (by simp only [List.mem_singleton]; rintro r rfl
                          exact hp.f_o.symm.sub_right (sv_sub hl)) i (by omega)
  have hdg₁₄ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₁₄.mem (fr s₀) H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) := by
    intro k0 text h
    rw [← hdg₉ k0 text h, m₁₄]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi => fC.bytes (R := digR H s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact i_d.symm)
      (by show H.D ≤ 2 ^ 64; omega) hi
  -- Absorb the inner digest.
  refine WP.seq (hH.callUpd_ok (st := inn s₀) (dat := fr s₀) (len := H.D)
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      g₁₀ _ (by decide), v₉.s7])
    (by rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀ _ (by decide), v₉.s8])
    (by rw [u₁₄.gpr, BitVec.toNat_ofNat]; omega)
    i_d.symm (by rw [r₁₄.sp]; exact hp.al) (by rw [r₁₄.sp]; exact hp.spF)
    (by rw [r₁₄.sp]; exact hp.s_i) (by rw [r₁₄.sp]; exact s_d)
    (by rw [r₁₄.rd, r₁₄.wr]; exact (VG.Covers.append_left hcovD (cover_self hwi)).right)
    (by rw [r₁₄.wr]; exact cover_self hwi)
    fun s₁₅ rd₁₅ wr₁₅ sp₁₅ f₁₅ cs₁₅ hup₁₅ => ?_)
  rw [r₁₄.sp] at f₁₅
  have r₁₅ : Regs s₀ s₁₅ := ⟨rd₁₅.trans r₁₄.rd, wr₁₅.trans r₁₄.wr, sp₁₅.trans r₁₄.sp⟩
  have v₁₅ := v₁₄.of_pres cs₁₅
  have a1₁₄ : s₁₄.gpr .a1 = BitVec.ofNat 64 H.B := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr]
  have hrI₁₅ : ∀ k0 text, Hyp hH s₀ k0 text →
      hH.SH.Repr s₁₅.mem (inn s₀) (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ text)) := by
    intro k0 text h
    have := hup₁₅ _ (hrO₁₄ k0 text h) (by rw [a1₁₄]; simp [xorPad, h.1, hH.hB])
    rwa [hdg₁₄ k0 text h] at this
  have sv₁₅ := sv₁₄.frame_in savedAt_in f₁₅ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [sv_i, sv_s])
  -- The MAC, into `out`.
  refine WP.seq (wp_mv fun s₁₆ u₁₆ => wp_li (by omega) fun s₁₇ u₁₇ => wp_mv fun s₁₈ u₁₈ => WP.block_nil ?_)
  have r₁₈ : Regs s₀ s₁₈ := ⟨by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, r₁₅.rd], by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, r₁₅.wr],
    by rw [u₁₈.sp, u₁₇.sp, u₁₆.sp, r₁₅.sp]⟩
  have m₁₈ : s₁₈.mem = s₁₅.mem := by rw [u₁₈.mem, u₁₇.mem, u₁₆.mem]
  have v₁₈ : Vars s₀ s₁₈ := v₁₅.of_keep fun r a b c _ _ => by
    rw [u₁₈.other r c, u₁₇.other r b, u₁₆.other r a]
  refine WP.seq (hH.callFin_ok (st := inn s₀) (o := mac s₀)
    (by rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, v₁₅.s7])
    (by rw [u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.other _ (by decide), v₁₅.s10])
    hp.i_m (by rw [r₁₈.sp]; exact hp.al) (by rw [r₁₈.sp]; exact hp.spF) (by rw [r₁₈.sp]; exact hp.s_i)
    (by rw [r₁₈.sp]; exact hp.s_m)
    (by rw [r₁₈.rd, r₁₈.wr]; exact (VG.Covers.pair (cover_self hwi) (cover_self hwm)).right)
    (by rw [r₁₈.wr]; exact VG.Covers.pair (cover_self hwi) (cover_self hwm))
    fun s₁₉ rd₁₉ wr₁₉ sp₁₉ f₁₉ cs₁₉ hfin₁₉ => ?_)
  rw [r₁₈.sp] at f₁₉
  have r₁₉ : Regs s₀ s₁₉ := ⟨rd₁₉.trans r₁₈.rd, wr₁₉.trans r₁₈.wr, sp₁₉.trans r₁₈.sp⟩
  have v₁₉ := v₁₈.of_pres cs₁₉
  have hmac₁₉ : ∀ k0 text, Hyp hH s₀ k0 text →
      bytesAt s₁₉.mem (mac s₀) H.D = hmacBlockKey hH.SH.H k0 text := by
    intro k0 text h
    have hl' : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ text)).length = H.B + H.D := by
      simp [xorPad, h.1, hH.hB, hH.hashLen]
    exact hfin₁₉ _ (by rw [m₁₈]; exact hrI₁₅ k0 text h) (by rw [hl']; omega)
      (by rw [hl', u₁₈.other _ (by decide), u₁₇.gpr])
  have sv₁₉ := (by rw [m₁₈]; exact sv₁₅ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.fso) s₁₈.mem).frame_in
    savedAt_in f₁₉ (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [sv_i, sv_m, sv_s])
  -- Restore our caller's registers.
  rw [← List.append_nil (Spill.restoreCode _ _)]
  refine Spill.restore_ok (B := fr s₀) hal8 v₁₉.s8
    (fun p hp' => savedAt_off ⟨hfso.2, by omega⟩ p (restList_mem.mp hp')) (restorable _)
    (fun p hp' => ⟨frR H s₀, by rw [r₁₉.rd, r₁₉.wr]; exact List.mem_append_right _ hwf,
      Offset.contains_base _ (by have := savedAt_in p (restList_mem.mp hp'); omega)
        (by have := savedAt_in p (restList_mem.mp hp'); omega)⟩)
    (sv₁₉.sub fun p hp' => restList_mem.mp hp') fun s' hs' => WP.block_nil ?_
  refine ⟨preserved_of (so := H.fso) (fun p hp' => hs'.gpr p (restList_mem.mpr hp')) fun r hr => ?_,
    hs'.gpr (.ra, H.fso) (by simp [restList]), by rw [hs'.sp, r₁₉.sp], by rw [hs'.wr, r₁₉.wr],
    fun k0 text h => by rw [hs'.mem]; exact hmac₁₉ k0 text h⟩
  rw [hs'.other r (by rw [restList_fst]; revert r; decide)]
  exact v₁₉.nv r hr

/-- The state the frame's body starts in, from `finalize`'s precondition. -/
theorem pre_alloc {s : State} (hp : (finG hH.SH (H.fbytes + H.F)).pre s) : Pre H (allocd H.fbytes s) := by
  have hl := hH.lay
  have hfb := hl.fbytes
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  rw [hH.hS, hH.hD] at *
  have hsp := toNat_sub (sp := s.sp) (n := H.fbytes) (by omega) (by omega)
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 H.fbytes, H.fbytes⟩ (below s.sp (H.fbytes + H.F)) :=
    Offset.sub_below s.sp (by omega) (by omega)
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 H.fbytes) H.F) (below s.sp (H.fbytes + H.F)) := by
    have := below_body' s.sp H.fbytes H.F
    rwa [Nat.add_comm H.F] at this
  have hsp' : (allocd H.fbytes s).sp = s.sp - BitVec.ofNat 64 H.fbytes := rfl
  refine ⟨h1, by show _ :: s.wr = _; rw [h2]; rfl, h3, h4, h5, h8.sub_left subF, h9.sub_left subF,
    h10.sub_left subF, ?_, ?_, ?_, h8.sub_left subS, h9.sub_left subS, h10.sub_left subS⟩
  · rw [hsp', hsp]; omega
  · rw [hsp', hsp]; omega
  · rw [hsp', hsp]; have := s.sp.isLt; omega

/-- HMAC's `finalize`. -/
theorem correct {s : State} (hp : (finG hH.SH (H.fbytes + H.F)).pre s) :
    WP isa H.finalize s fun s' => abiPreserved s s' ∧ (finG hH.SH (H.fbytes + H.F)).post s s' := by
  have hl := hH.lay
  have hfb := hl.fbytes
  have hsp : H.fbytes ≤ s.sp.toNat := by have := hp.2.2.2.2.2.2.1; omega
  refine WP.alloc ⟨by omega, hfb.2.1, hfb.2.2⟩ hsp
    (WP.mono (finalizeMain_ok hH (pre_alloc hH hp)) fun s' ⟨hk, hra, hsp', hwr, hmac⟩ => ?_)
  rw [freed_eq hwr hsp']
  refine ⟨⟨hk, rfl, hra⟩, fun k0 text hk0 hlt hI hc hO => ?_⟩
  rw [hH.hD]
  exact hmac k0 text ⟨hk0, hlt, hI, hc, hO⟩

end VG.Proof.Hmac.Stream.RISCV64.Finalize
