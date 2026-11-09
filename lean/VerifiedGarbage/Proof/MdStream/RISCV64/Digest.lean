module

public import VerifiedGarbage.Impl.MdStream.RISCV64.Digest
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Init
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The one-shot digest over any streaming hash function on RISC-V: correct

`digest` (`Impl/MdStream/RISCV64/Digest.lean`) allocates its frame
(`WP.alloc`), saves our caller's `ra` and `s7`–`s11` in it after the
streaming state, hashes the message with the streaming `init`, `update` and
`finalize` (through their proofs, `HashOK.callInit_ok`, `callUpd_ok` and
`callFin_ok`), which writes the digest to `out`, zeroes the streaming state
and restores the registers (`digestMain_ok`), as HMAC's `init` hashes a long
key (`Proof/Hmac/Stream/RISCV64/InitMain.lean`). `digestG` is the contract
it is verified against, with the bytes of stack it and its callees use; with
each hash function's constant time it is moved to
`Spec.Sha256.digestContract` (`verified`).
-/

@[expose] public section

namespace VG.Proof.MdStream.RISCV64.Digest

open VG.RISCV64
open VG.RISCV64.Steps (Upd wp_li wp_mv wp_addi wp_addSp)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.MdStream.RISCV64.Digest (dso dbytes wipe digestMain digest)
open VG.Proof.Hmac.Stream.RISCV64
open VG.Proof.Hmac.Stream.RISCV64.Init (cover_off cover_self cover_pre Regs)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-! ## The contract -/

/-- `digest(data, len, out)`, with `F` bytes of stack below the stack
pointer. -/
def digestG (SH : StreamingHash) (F : Nat) : Contract isa where
  pre s :=
    let data : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let out : Region := ⟨s.gpr .a2, SH.digestBytes⟩
    let stack : Region := below s.sp F
    s.rd = [data] ∧ s.wr = [out] ∧ data.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ F ≤ s.sp.toNat ∧ stack.Disjoint data ∧ stack.Disjoint out
  post s s' :=
    bytesAt s'.mem (s.gpr .a2) SH.digestBytes = SH.H.hash (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

/-! ## The frame -/

section
variable (H : Hash) (s₀ : State)

abbrev fr : Addr := s₀.sp
abbrev dp : Addr := s₀.gpr .a0
abbrev dl : Nat := (s₀.gpr .a1).toNat
abbrev out : Addr := s₀.gpr .a2
/-- The message. -/
abbrev M : List Byte := bytesAt s₀.mem (dp s₀) (dl s₀)
abbrev dR : Region := ⟨dp s₀, dl s₀⟩
abbrev oR : Region := ⟨out s₀, H.D⟩
abbrev frR : Region := ⟨fr s₀, dbytes H⟩
/-- The stack below the frame, where the callees' frames go. -/
abbrev stk : Region := below (fr s₀) H.F
/-- The streaming state. -/
abbrev stR : Region := ⟨fr s₀, H.S⟩
/-- Where our caller's registers are saved. -/
abbrev svR : Region := ⟨fr s₀ + BitVec.ofNat 64 (dso H), 48⟩
/-- What `wipe` zeroes. -/
abbrev wpR : Region := ⟨fr s₀, 8 * (dso H / 8)⟩

end

/-- The state the frame's body starts in. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [frR H s₀, oR H s₀]
  d_o : (dR s₀).Disjoint (oR H s₀)
  f_d : (frR H s₀).Disjoint (dR s₀)
  f_o : (frR H s₀).Disjoint (oR H s₀)
  al : s₀.sp.toNat % 16 = 0
  spF : H.F ≤ s₀.sp.toNat
  top : s₀.sp.toNat + dbytes H ≤ 2 ^ 64
  s_d : (stk H s₀).Disjoint (dR s₀)
  s_o : (stk H s₀).Disjoint (oR H s₀)

/-- The layout of the frame. -/
structure DLay (H : Hash) : Prop where
  so : H.S ≤ dso H ∧ dso H % 8 = 0
  fb : dso H + 48 ≤ dbytes H ∧ dbytes H < 2048 ∧ dbytes H % 16 = 0

theorem dlay {H : Hash} (hl : Lay H) : DLay H := by
  have hB := hl.B
  have hN := hl.N
  have hS : H.S = H.N + H.B := rfl
  refine ⟨?_, ?_⟩ <;> simp only [dso, dbytes, hS] <;> omega

variable {H : Hash} {s₀ : State}

section
variable (hl : DLay H)
include hl

omit hl in
theorem Pre.f_s (hp : Pre H s₀) : (frR H s₀).Disjoint (stk H s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spF; have := s₀.sp.isLt; omega_arith)

theorem sv_sub : Region.Sub (svR H s₀) (frR H s₀) := Offset.sub_base _ hl.fb.1

theorem st_sub : Region.Sub (stR H s₀) (frR H s₀) :=
  Region.sub_prefix (by have := hl.so; have := hl.fb; omega_arith)

theorem wp_sub : Region.Sub (wpR H s₀) (frR H s₀) :=
  Region.sub_prefix (by have := hl.so; have := hl.fb; omega_arith)

theorem st_sv : Region.Disjoint (stR H s₀) (svR H s₀) :=
  Offset.base_disjoint _ (by have := hl.so; omega_arith) (by have := hl.fb; omega_arith)

theorem wp_sv : Region.Disjoint (wpR H s₀) (svR H s₀) :=
  Offset.base_disjoint _ (by omega_arith) (by have := hl.fb; omega_arith)

end

/-- Our variables in `s8`–`s11`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) : Prop where
  s8 : s.gpr .s8 = fr s₀
  s9 : s.gpr .s9 = out s₀
  s10 : s.gpr .s10 = dp s₀
  s11 : s.gpr .s11 = s₀.gpr .a1
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

theorem Vars.of_pres {s s' : State} (h : Vars s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Vars s₀ s' :=
  ⟨(hc _ (by decide)).trans h.s8, (hc _ (by decide)).trans h.s9, (hc _ (by decide)).trans h.s10,
    (hc _ (by decide)).trans h.s11, fun r hr => (hc r (Init.nv_pres r hr)).trans (h.nv r hr)⟩

/-- `Vars` after code writing only `a0`–`a3`. -/
theorem Vars.of_keep {s s' : State} (h : Vars s₀ s)
    (hc : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) : Vars s₀ s' := by
  have k : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s8, .s9, .s10, .s11], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.s8, (k _ (by simp)).trans h.s9, (k _ (by simp)).trans h.s10,
    (k _ (by simp)).trans h.s11, fun r hr => (k r (by revert r; decide)).trans (h.nv r hr)⟩

/-- `digestMain`'s postcondition, in its frame. -/
def Post (hH : HashOK H) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ s'.wr = s₀.wr ∧
    bytesAt s'.mem (out s₀) H.D = hH.SH.H.hash (M s₀)

variable (hH : HashOK H)
include hH

omit hH in
/-- The saved registers survive writes in the streaming state, `out` and
below the frame. -/
theorem sv_keep (hp : Pre H s₀) (hl : DLay H) {m m' : Mem}
    (h : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt (dso H)) m) {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = stR H s₀ ∨ r = oR H s₀ ∨ r = stk H s₀) :
    Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt (dso H)) m' :=
  h.frame_in savedAt_in hf fun r hr => by
    rcases hrs r hr with rfl | rfl | rfl
    exacts [(st_sv hl).symm, hp.f_o.sub_left (sv_sub hl), hp.f_s.sub_left (sv_sub hl)]

/-- `digest`, in its frame. -/
theorem digestMain_ok (hp : Pre H s₀) : WP isa (digestMain H) s₀ (Post hH s₀) := by
  have hl₀ := hH.lay
  have hl := dlay hl₀
  have hD := hl₀.D
  have hdso := hl.so
  have hdb := hl.fb
  have hS : H.S < 2048 := by omega_arith
  have hal8 : (fr s₀).toNat % 8 = 0 := by show s₀.sp.toNat % 8 = 0; have := hp.al; omega_arith
  have hwf : frR H s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hwo : oR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hrd : dR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_singleton_self _
  have dS : (dR s₀).Disjoint (stR H s₀) := hp.f_d.symm.sub_right (st_sub hl)
  have sS : (stk H s₀).Disjoint (stR H s₀) := hp.f_s.symm.sub_right (st_sub hl)
  have oS : Region.Disjoint (stR H s₀) (oR H s₀) := hp.f_o.sub_left (st_sub hl)
  have dl_lt : dl s₀ < 2 ^ 64 := (s₀.gpr .a1).isLt
  have msg_keep : ∀ {m : Mem} {rs : List Region}, Frame rs s₀.mem m →
      (∀ r ∈ rs, r = stR H s₀ ∨ r = oR H s₀ ∨ r = stk H s₀ ∨ r = svR H s₀) →
      bytesAt m (dp s₀) (dl s₀) = M s₀ := by
    intro m rs hf hrs
    refine Proof.Sha256.Stream.bytesAt_congr fun i hi => hf.bytes (R := dR s₀) (fun r hr => ?_)
      (by show dl s₀ ≤ 2 ^ 64; omega_arith) hi
    rcases hrs r hr with rfl | rfl | rfl | rfl
    exacts [dS, hp.d_o, hp.s_d.symm, hp.f_d.symm.sub_right (sv_sub hl)]
  unfold digestMain
  rw [saveAt_eq, List.cons_append]
  -- Save our caller's registers, and set up ours.
  refine WP.seq (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  have t0₁ : s₁.gpr .t0 = fr s₀ := by rw [u₁.gpr, BitVec.add_zero]
  refine Spill.save_ok (by rw [t0₁]; exact hal8) (savedAt_off ⟨hdso.2, by omega_arith⟩)
    (fun p hp' => ⟨frR H s₀, by rw [u₁.wr, hp.wr]; exact List.mem_cons_self,
      (by
        rw [t0₁]
        have := savedAt_in p hp'
        exact Offset.contains_base (k := dbytes H) _ (by omega_arith) (by omega_arith))⟩) ?_
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => WP.block_nil ?_
  have r₇ : Regs s₀ s₇ := ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]; exact u₁.rd,
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact u₁.wr,
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]; exact u₁.sp⟩
  have v₇ : Vars s₀ s₇ :=
    ⟨by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr]; exact t0₁,
      by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide)]; exact u₁.other _ (by decide),
      fun r hr => by
        rw [u₇.other r (by revert r; decide), u₆.other r (by revert r; decide), u₅.other r (by revert r; decide),
          u₄.other r (by revert r; decide), u₃.other r (by revert r; decide)]
        exact u₁.other r (by revert r; decide)⟩
  have a0₇ : s₇.gpr .a0 = fr s₀ := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    exact t0₁
  have hm₇ : s₇.mem = Spill.saveMem s₀.mem (fr s₀) s₁.gpr (Hash.savedAt (dso H)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, t0₁, u₁.mem]
  have hf₇ : Frame [svR H s₀] s₀.mem s₇.mem := by
    rw [hm₇]; exact Spill.saveMem_frame savedAt_in (by have := hp.top; omega_arith) _ _ _
  have sv₇ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt (dso H)) s₇.mem := by
    rw [hm₇]
    intro p hp'
    rw [Spill.saveMem_saved (savedAt_fits ⟨hdso.2, by omega_arith⟩) _ _ _ p hp']
    refine u₁.other _ ?_
    simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  -- The streaming state's hash value.
  refine WP.seq (hH.callInit_ok (st := fr s₀) a0₇
    (by rw [r₇.rd, r₇.wr]; exact cover_pre (List.mem_append_right _ hwf) (show H.S ≤ dbytes H by omega_arith))
    (by rw [r₇.wr]; exact cover_pre hwf (show H.S ≤ dbytes H by omega_arith))
    fun s₈ rd₈ wr₈ sp₈ f₈ cs₈ hrS₈ => ?_)
  rw [r₇.sp] at f₈
  have r₈ : Regs s₀ s₈ := ⟨rd₈.trans r₇.rd, wr₈.trans r₇.wr, sp₈.trans r₇.sp⟩
  have v₈ := v₇.of_pres cs₈
  have hrs₈ : ∀ r ∈ [stR H s₀] ++ [stk H s₀], r = stR H s₀ ∨ r = oR H s₀ ∨ r = stk H s₀ := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inl rfl, .inr (.inr rfl)]
  have sv₈ := sv_keep hp hl sv₇ f₈ hrs₈
  have k₈ : bytesAt s₈.mem (dp s₀) (dl s₀) = M s₀ :=
    msg_keep (rs := [svR H s₀, stR H s₀, stk H s₀]) ((hf₇.mono (by simp)).trans (f₈.mono (by simp))) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [.inr (.inr (.inr rfl)), .inl rfl, .inr (.inr (.inl rfl))])
  -- Absorb the message.
  refine WP.seq (wp_mv fun s₉ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => wp_mv fun s₁₁ u₁₁ =>
    wp_mv fun s₁₂ u₁₂ => WP.block_nil ?_)
  have r₁₂ : Regs s₀ s₁₂ := ⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, r₈.rd],
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, r₈.wr], by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, r₈.sp]⟩
  have m₁₂ : s₁₂.mem = s₈.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have v₁₂ : Vars s₀ s₁₂ := v₈.of_keep fun r a b c d => by
    rw [u₁₂.other r d, u₁₁.other r c, u₁₀.other r b, u₉.other r a]
  have a1₁₂ : s₁₂.gpr .a1 = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr]; rfl
  refine WP.seq (hH.callUpd_ok (st := fr s₀) (dat := dp s₀) (len := dl s₀)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, v₈.s8])
    (by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), v₈.s10])
    (by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), v₈.s11])
    dS (by rw [r₁₂.sp]; exact hp.al) (by rw [r₁₂.sp]; exact hp.spF) (by rw [r₁₂.sp]; exact sS)
    (by rw [r₁₂.sp]; exact hp.s_d)
    (by
      rw [r₁₂.rd, r₁₂.wr]
      exact VG.Covers.append_left (cover_self (List.mem_append_left _ hrd))
        (cover_pre (List.mem_append_right _ hwf) (show H.S ≤ dbytes H by omega_arith)))
    (by rw [r₁₂.wr]; exact cover_pre hwf (show H.S ≤ dbytes H by omega_arith))
    fun s₁₃ rd₁₃ wr₁₃ sp₁₃ f₁₃ cs₁₃ hup => ?_)
  rw [r₁₂.sp, m₁₂] at f₁₃
  have r₁₃ : Regs s₀ s₁₃ := ⟨rd₁₃.trans r₁₂.rd, wr₁₃.trans r₁₂.wr, sp₁₃.trans r₁₂.sp⟩
  have v₁₃ := v₁₂.of_pres cs₁₃
  have sv₁₃ := sv_keep hp hl sv₈ f₁₃ hrs₈
  have hrS₁₃ : hH.SH.Repr s₁₃.mem (fr s₀) (M s₀) := by
    have := hup [] (by rw [m₁₂]; exact hrS₈) a1₁₂
    rwa [List.nil_append, m₁₂, k₈] at this
  -- The digest, into `out`.
  refine WP.seq (wp_mv fun s₁₄ u₁₄ => wp_mv fun s₁₅ u₁₅ => wp_mv fun s₁₆ u₁₆ => WP.block_nil ?_)
  have r₁₆ : Regs s₀ s₁₆ := ⟨by rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, r₁₃.rd], by rw [u₁₆.wr, u₁₅.wr, u₁₄.wr, r₁₃.wr],
    by rw [u₁₆.sp, u₁₅.sp, u₁₄.sp, r₁₃.sp]⟩
  have m₁₆ : s₁₆.mem = s₁₃.mem := by rw [u₁₆.mem, u₁₅.mem, u₁₄.mem]
  have v₁₆ : Vars s₀ s₁₆ := v₁₃.of_keep fun r a b c _ => by
    rw [u₁₆.other r c, u₁₅.other r b, u₁₄.other r a]
  have hcov : VG.Covers [stR H s₀, oR H s₀] s₀.wr :=
    VG.Covers.pair (cover_pre hwf (show H.S ≤ dbytes H by omega_arith)) (cover_self hwo)
  refine WP.seq (hH.callFin_ok (st := fr s₀) (o := out s₀)
    (by rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.gpr, v₁₃.s8])
    (by rw [u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), v₁₃.s9])
    oS (by rw [r₁₆.sp]; exact hp.al) (by rw [r₁₆.sp]; exact hp.spF) (by rw [r₁₆.sp]; exact sS)
    (by rw [r₁₆.sp]; exact hp.s_o) (by rw [r₁₆.rd, r₁₆.wr]; exact hcov.right) (by rw [r₁₆.wr]; exact hcov)
    fun s₁₇ rd₁₇ wr₁₇ sp₁₇ f₁₇ cs₁₇ hfin => ?_)
  rw [r₁₆.sp, m₁₆] at f₁₇
  have r₁₇ : Regs s₀ s₁₇ := ⟨rd₁₇.trans r₁₆.rd, wr₁₇.trans r₁₆.wr, sp₁₇.trans r₁₆.sp⟩
  have v₁₇ := v₁₆.of_pres cs₁₇
  have sv₁₇ := sv_keep hp hl sv₁₃ f₁₇ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr rfl)])
  have hdg : bytesAt s₁₇.mem (out s₀) H.D = hH.SH.H.hash (M s₀) :=
    hfin (M s₀) (by rw [m₁₆]; exact hrS₁₃) (by simp only [bytesAt, List.length_map, List.length_range]; exact dl_lt)
      (by
        rw [u₁₆.other _ (by decide), u₁₅.gpr, u₁₄.other _ (by decide), v₁₃.s11]
        simp only [bytesAt, List.length_map, List.length_range, dl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  -- Zero the streaming state, and restore our caller's registers.
  rw [show wipe H = .li .t1 0 :: stores (dso H / 8) from rfl, List.cons_append]
  refine wp_li (by decide) fun s₁₈ u₁₈ => ?_
  refine stores_ok (dso H / 8) (fr := fr s₀) hal8 (by omega_arith)
    (by rw [u₁₈.other _ (by decide)]; exact v₁₇.s8)
    (fun j hj => ⟨frR H s₀, by rw [u₁₈.wr, r₁₇.wr, hp.wr]; simp,
      Offset.contains_base _ (by omega_arith) (by have := hp.top; omega_arith)⟩)
    fun s₁₉ g₁₉ rd₁₉ wr₁₉ sp₁₉ f₁₉ => ?_
  rw [restoreAt_eq, ← List.append_nil (Spill.restoreCode _ _)]
  have sv₁₉ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt (dso H)) s₁₉.mem := by
    refine sv₁₇.frame_in savedAt_in (by rw [u₁₈.mem] at f₁₉; exact f₁₉) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact (wp_sv hl).symm
  refine Spill.restore_ok (B := fr s₀) hal8 (by rw [g₁₉, u₁₈.other _ (by decide)]; exact v₁₇.s8)
    (fun p hp' => savedAt_off ⟨hdso.2, by omega_arith⟩ p (restList_mem.mp hp')) (restorable _)
    (fun p hp' => ⟨frR H s₀, by rw [rd₁₉, wr₁₉, u₁₈.rd, u₁₈.wr, r₁₇.rd, r₁₇.wr, hp.wr]; simp,
      Offset.contains_base _ (by have := savedAt_in p (restList_mem.mp hp'); omega_arith)
        (by have := savedAt_in p (restList_mem.mp hp'); have := hp.top; omega_arith)⟩)
    (sv₁₉.sub fun p hp' => restList_mem.mp hp') fun s' hs' => WP.block_nil ?_
  have m' : Frame [wpR H s₀] s₁₇.mem s'.mem := by rw [hs'.mem, ← u₁₈.mem]; exact f₁₉
  refine ⟨preserved_of (so := dso H) (fun p hp' => hs'.gpr p (restList_mem.mpr hp')) fun r hr => ?_,
    hs'.gpr (.ra, dso H) (by simp [restList]), by rw [hs'.sp, sp₁₉, u₁₈.sp, r₁₇.sp],
    by rw [hs'.wr, wr₁₉, u₁₈.wr, r₁₇.wr], ?_⟩
  · rw [hs'.other r (by rw [restList_fst]; revert r; decide), g₁₉, u₁₈.other r (by revert r; decide)]
    exact v₁₇.nv r hr
  · rw [← hdg]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi => m'.bytes (R := oR H s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.f_o.symm.sub_right (wp_sub hl)))
      (by show H.D ≤ 2 ^ 64; omega_arith) hi

/-- The state the frame's body starts in, from `digest`'s precondition. -/
theorem pre_alloc {s : State} (hp : (digestG hH.SH (dbytes H + H.F)).pre s) : Pre H (allocd (dbytes H) s) := by
  have hl := dlay hH.lay
  have hdb := hl.fb
  have hF := hH.lay.F
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  rw [hH.hD] at h2 h3 h7
  have hsp := toNat_sub (sp := s.sp) (n := dbytes H) (by omega_arith) (by omega_arith)
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 (dbytes H), dbytes H⟩ (below s.sp (dbytes H + H.F)) :=
    Offset.sub_below s.sp (by omega_arith) (by omega_arith)
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 (dbytes H)) H.F) (below s.sp (dbytes H + H.F)) := by
    have := below_body' s.sp (dbytes H) H.F
    rwa [Nat.add_comm H.F] at this
  have hsp' : (allocd (dbytes H) s).sp = s.sp - BitVec.ofNat 64 (dbytes H) := rfl
  refine ⟨h1, by show _ :: s.wr = _; rw [h2]; rfl, h3, h6.sub_left subF, h7.sub_left subF, ?_, ?_, ?_,
    h6.sub_left subS, h7.sub_left subS⟩
  · rw [hsp', hsp]; omega_arith
  · rw [hsp', hsp]; omega_arith
  · rw [hsp', hsp]; have := s.sp.isLt; omega_arith

/-- `digest`. -/
theorem correct {s : State} (hp : (digestG hH.SH (dbytes H + H.F)).pre s) :
    WP isa (digest H) s fun s' => abiPreserved s s' ∧ (digestG hH.SH (dbytes H + H.F)).post s s' := by
  have hl := dlay hH.lay
  have hdb := hl.fb
  have hsp : dbytes H ≤ s.sp.toNat := by have := hp.2.2.2.2.1; omega_arith
  refine WP.alloc ⟨by omega_arith, hdb.2.1, hdb.2.2⟩ hsp
    (WP.mono (digestMain_ok hH (pre_alloc hH hp)) fun s' ⟨hk, hra, hsp', hwr, hO⟩ => ?_)
  rw [freed_eq hwr hsp']
  refine ⟨⟨hk, rfl, hra⟩, ?_⟩
  show bytesAt _ (s.gpr .a2) hH.SH.digestBytes = _
  rw [hH.hD]
  exact hO

/-! ## The shared contract -/

omit hH in
/-- The initial taint of `digest`: only the arguments are public. -/
theorem agree {s₁ s₂ : State}
    (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [p0, p1, p2]

omit hH in
theorem digestImp {SH : StreamingHash} {n : Nat}
    (hs : ∃ s, (Spec.Sha256.digestContract RISCV64.abi SH.digestBytes SH.H.hash (n + 1)).pre s) :
    (digestG SH (n + 1)).Implies (Spec.Sha256.digestContract RISCV64.abi SH.digestBytes SH.H.hash (n + 1)) := by
  generic_implies [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, digestG,
    RISCV64.abi, RISCV64.argRegs] using hs

/-- `digest` against `Spec.Sha256.digestContract`, given its constant time. -/
theorem verified
    (ct : ConstantTime isa (digestG hH.SH (dbytes H + H.F)).pre (digestG hH.SH (dbytes H + H.F)).pub (digest H))
    (hs : ∃ s, (Spec.Sha256.digestContract RISCV64.abi hH.SH.digestBytes hH.SH.H.hash (dbytes H + H.F)).pre s) :
    Verified RISCV64.target (digest H)
      (Spec.Sha256.digestContract RISCV64.abi hH.SH.digestBytes hH.SH.H.hash (dbytes H + H.F)) := by
  obtain ⟨n, hn⟩ : ∃ n, dbytes H + H.F = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by have := (dlay hH.lay).fb; omega_arith)).symm⟩
  rw [hn] at ct hs ⊢
  have imp := digestImp hs
  exact Verified.of_implies (⟨fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := correct hH (by rw [hn]; exact hs); rw [hn] at h₂; exact ⟨t, s', he, h₁, h₂⟩,
    ct, imp.sat_left⟩ : Verified RISCV64.target (digest H) (digestG hH.SH (n + 1))) imp

/-- A state satisfying `digest`'s precondition, with a digest of `D` bytes
and an empty message. -/
def digestSat (D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a2 => 0x20000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩]
  wr := [⟨0x20000, D⟩]

end VG.Proof.MdStream.RISCV64.Digest
