module

public import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Steps
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Common
import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMixLoops
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# scrypt on RISC-V: correctness

As on PPC64LE (`Proof/Scrypt/PPC64LE/Whole/Correct.lean`). PBKDF2-HMAC-SHA256
(any implementation correct under `pbkR sha256S 992`, using at most 992 bytes
of stack) is called by `pbk_call`; ROMix, by doublewords or by bytes, by
`romix_call`. Step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`), with
the doubleword ROMix if `b`, `v` and `scratch` are all 8-byte aligned
(`all_ok`); step 3 derives the key from them (`step3_ok`). `scrypt_ok` puts
the frame around it.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.Impl.Scrypt.RISCV64.Whole
open VG.Proof.Pbkdf2.Whole.RISCV64 (pbkR)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

/-- What `vg_scrypt` needs of the PBKDF2 it calls. -/
abbrev pbkK : Contract isa := pbkR Spec.Hmac.sha256S 992

/-- Correctness of the PBKDF2 called. -/
abbrev PbkOk (pbk : Prog isa) : Prop :=
  ∀ s, pbkK.pre s → ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s'

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.ce_sp {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).sp = L.B + BitVec.ofNat 64 992 := by
  rw [State.withRegions_sp, State.callEntry_sp, hc.sp]

theorem sub992 (B : Addr) : B + BitVec.ofNat 64 992 - BitVec.ofNat 64 992 = B := BitVec.add_sub_cancel _ _

theorem sv_stk (L : Lay) : Region.Sub L.SV L.STK := Offset.sub_base _ (by decide)

namespace Lay.Ok

variable (hL : L.Ok)
include hL


/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs,
    (hL.kp.symm.sub_right (sv_stk L)).sub_right hs]

/-- The 992 bytes the calls use miss every writable buffer. -/
theorem low_in {r : Region} (h : InBuf L r) : Region.Disjoint ⟨L.B, 992⟩ r := by
  have hnB := hL.nB
  have lo : Region.Sub ⟨L.B, 992⟩ L.STK := fun x hx => by
    simp only [Region.Contains] at hx ⊢; omega
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl | rfl
  · exact (hL.kb.sub_left lo).sub_right hs
  · exact (hL.kv.sub_left lo).sub_right hs
  · exact (hL.kc.sub_left lo).sub_right hs
  · exact (hL.ko.sub_left lo).sub_right hs
  · exact (Region.Disjoint.symm (Offset.disjoint_base _ (by decide) (by omega))).sub_right hs

end Lay.Ok

/-! ### PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt : Addr) (sl : BitVec 64) : List Region := [L.PW, ⟨salt, sl.toNat⟩]
abbrev pbkWr (out : Addr) (ol : BitVec 64) : List Region := [⟨out, ol.toNat⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt, sl.toNat⟩ R
  ow : InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr out ol)) := by
  have hnB := hL.nB
  have haB := hL.aB
  have t992 : (L.B + BitVec.ofNat 64 992).toNat = L.B.toNat + 992 := toNat_add_ofNat _ (by omega)
  have lo : Region.Sub ⟨L.B, 992⟩ L.STK := fun x hx => by
    simp only [Region.Contains] at hx ⊢; omega
  simp only [pbkK, pbkR, below, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr,
    hc.ce_sp, sub992, t992, gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a6 ∉ linkRegs),
    ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6]
  exact ⟨trivial, trivial, hL.pw_buf hr.ow, hr.so, by omega, by omega, hL.kp.sub_left lo, hr.ks.sub_left lo,
    hL.low_in hr.ow, hL.np, hr.ns, hr.no, by decide, hr.ol⟩

theorem pbk_sub {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr out ol, ∃ R ∈ L.regions, Within r R := by
  have hs := hr.sw
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · rcases hr.ow with h | h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h.trans (sv_within L)⟩

theorem pbk_wsub {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) : ∀ r ∈ pbkWr out ol, InBuf L r := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact hr.ow

theorem pbk_call (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.B, 992⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  refine call_ok hL hv hd hc (pbk_pre' hL hc ha hr) (pbk_sub hr) (pbk_wsub hr)
    fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [pbkK, pbkR, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a6 ∉ linkRegs), ha.a0, ha.a1, ha.a2, ha.a3,
    ha.a4, ha.a5, ha.a6] at h
  exact h

end

/-! ### ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, L.r.toNat * 128⟩, L.SV]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkAt L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

theorem scr_in (hL : L.Ok) : InBuf L ⟨L.scr, L.r.toNat * 128⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))

theorem blk_toNat (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  exact toNat_add_ofNat _ (by omega)

/-- The doubleword ROMix may run if `b`, `v` and `scratch` are aligned. -/
abbrev Aligned (L : Lay) (wide : Bool) : Prop :=
  wide = true → L.b.toNat % 8 = 0 ∧ L.v.toNat % 8 = 0 ∧ L.scr.toNat % 8 = 0

theorem romix_pre (hL : L.Ok) {t : State} {i : Nat} (hi : i < L.pp) {wide : Bool}
    (hal : Aligned L wide) (ha : RomixArgs L (blkAt L i) t) :
    (Proof.Scrypt.roMixRISCV64 wide).pre (t.callEntry.withRegions [] (romixWr L i)) := by
  have hnB := hL.nB
  have haB := hL.aB
  have tb := blk_toNat hL hi
  have t1072 : (L.B + BitVec.ofNat 64 1072).toNat = L.B.toNat + 1072 := toNat_add_ofNat _ (by omega)
  simp only [Proof.Scrypt.roMixRISCV64, State.withRegions_rd, State.withRegions_wr,
    gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs),
    ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, t1072]
  have kb := Within.sub (within_off L.b (blk_le hL hi))
  have ks := Within.sub (within_base L.scr (n := L.r.toNat * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  have sv := (sv_stk L)
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks,
    (hL.kb.symm.sub_left kb).sub_right sv, hL.vc.sub_right ks, hL.kv.symm.sub_right sv,
    (hL.kc.symm.sub_left ks).sub_right sv, by rw [tb]; have := blk_le hL hi; have := hL.nb; omega,
    hL.nv, by have := hL.nc; have := hL.slen; omega, by omega, hL.rpos, hL.vmod,
    Whole.valid_pow hL.valid, by omega, fun hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hal hw
  have e : 128 * L.r.toNat * i = 8 * (16 * L.r.toNat * i) := by simp only [Nat.mul_assoc]; omega
  exact ⟨by rw [tb, e]; omega, h2, h3⟩

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega)⟩
  · exact ⟨L.FR, by simp, sv_within L⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact scr_in hL
  · exact .inr (.inr (.inr (.inr (within_base _ (Nat.le_refl _)))))

theorem roMix_sdepth (wide : Bool) : sdepth (Impl.Scrypt.RISCV64.roMix wide) ≤ 992 := by
  cases wide <;> lit_decide

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) {wide : Bool}
    (hal : Aligned L wide) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide)) t fun t' => Ctx L g m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.B, 992⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkAt L i) (128 * L.r.toNat)) := by
  refine call_ok hL RoMix.roMix_correct (roMix_sdepth wide) hc (romix_pre hL hi hal ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [Proof.Scrypt.roMixRISCV64, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), ha.a0, ha.a1, ha.a3] at h
  exact h

end

/-! ## The password, the salt and the blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨blkAt L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega)

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String)
include hv hd

omit hv hd in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (ha : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hd name hL hc ha (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k :=
  WP.seq (WP.mono (pbk1Args_ok hc he) fun _ ⟨hc₁, _, ha₁⟩ => pbk1_call_ok hv hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's cur slot. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ (curR L) :=
  (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Offset.sub_base _ (by decide))

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :
    WP isa (.block cur0) t (Inv L g m₀ 0) :=
  WP.mono (cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', ⟨hb.trans (blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
      (by have := hL.blen_lt; have := blk_le hL hk; omega)⟩⟩

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

/-- The bytes of `b` left after block `i`, as the loop's condition reads them. -/
theorem left_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - blkAt L (i + 1) != 0) = decide (i + 1 ≠ L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [bne, Offset.ofNat_sub_ofNat_beq e₂ e₁, decide_not]
  refine congrArg (!·) (decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h).symm

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t) {wide : Bool}
    (hal : Aligned L wide) (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide)) t fun t' =>
      Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi hal ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hL.kept_buf (by decide) (by decide) (.inl rfl) (Within.sub (within_off _ (blk_le hL hi)))
    · exact hL.kept_buf (by decide) (by decide) (.inr (.inl rfl)) (Within.sub (within_base _ (Nat.le_refl _)))
    · exact hL.kept_buf (by decide) (by decide) (.inr (.inr (.inl rfl)))
        (Within.sub (within_base _ (by have := hL.slen; omega)))
    · exact Offset.disjoint _ (by decide) (by omega) (by omega)
    · exact Offset.disjoint_base _ (by decide) (by omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (sv_stk L)
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (fun x hx => by
              simp only [Region.Contains] at hx ⊢; omega))
          (by have := hL.blen_lt; have := blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hm : Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ InvB L m₀ (i + 1) t' ∧
      (t'.gpr .t0 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.mono (nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hx₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
        (by have := hL.blen_lt; have := blk_le hL hk; omega)⟩,
      by rw [hx₃, next_eq, left_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} {wide : Bool} (hal : Aligned L wide)
    (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide))
      (.block nextBlock))) t fun t' =>
        Inv L g m₀ (i + 1) t' ∧ (t'.gpr .t0 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.seq (WP.mono (romixArgs_ok hL h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (call_step hL hi hc₁ hal ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => WP.mono (next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} {wide : Bool} (hal : Aligned L wide) (h : Inv L g m₀ 0 t) :
    WP isa (romixLoop wide) t (Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi hal h) h

/-- Each of three doublewords is aligned if their OR is. -/
theorem al3 (a b c : BitVec 64) :
    ((a ||| b ||| c) &&& BitVec.ofInt 64 7 == 0) =
      decide (a.toNat % 8 = 0 ∧ b.toNat % 8 = 0 ∧ c.toNat % 8 = 0) := by
  have h1 := or_and7 (a ||| b) c
  have h2 := or_and7 (a ||| b) (a ||| b)
  rw [BitVec.or_self, or_and7 a b] at h2
  have e := decide_eq_decide.mp h2
  rw [h1]
  exact decide_eq_decide.mpr ⟨fun ⟨hp, hc⟩ => ⟨(e.mpr ⟨hp, hp⟩).1, (e.mpr ⟨hp, hp⟩).2, hc⟩,
    fun ⟨ha, hb, hc⟩ => ⟨(e.mp ⟨ha, hb⟩).1, hc⟩⟩

/-- ROMix on each block, by doublewords if `b`, `v` and `scratch` allow it. -/
theorem all_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) :
    WP isa romixAll t (Inv L g m₀ L.pp) := by
  refine WP.seq (WP.mono (alignBits_ok hL h.1) fun t₁ ⟨hc₁, hm₁, ht₁⟩ => ?_)
  have h₁ : Inv L g m₀ 0 t₁ := ⟨hc₁, by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩
  by_cases ha : L.b.toNat % 8 = 0 ∧ L.v.toNat % 8 = 0 ∧ L.scr.toNat % 8 = 0
  · refine WP.ite true (by rw [eval_zero, ht₁, al3, decide_eq_true ha]) (fun _ => ?_) fun h => by cases h
    exact loop_ok hL (fun _ => ha) h₁
  · refine WP.ite false (by rw [eval_zero, ht₁, al3, decide_eq_false ha]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hL (fun h => by cases h) h₁

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String)
include hv hd

omit hv hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hd in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (.inl (within_base _ (Nat.le_refl _))))), ?_,
    ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (pbk2Args_ok hL h.1) fun t₁ ⟨hc₁, hm₁, ha₁⟩ => ?_)
  refine WP.mono (pbk_call hv hd name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

/-- The frame's body after `setup` and before `restore`. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) {Q : State → Prop}
    (hQ : ∀ t', Ctx L g m₀ t' →
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) → WP isa (.block Impl.Scrypt.RISCV64.Whole.restore) t' Q) :
    WP isa (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixAll
      (.seq (pbkCall name pbk pbk2Args) (.block Impl.Scrypt.RISCV64.Whole.restore))))) t Q := by
  refine WP.seq (WP.mono (step1_ok hv hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (all_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (step3_ok hv hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => hQ t₄ hc₄ ?_)
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

end

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String)
include hv hd

/-- `vg_scrypt` meets `scryptRV` and the calling convention. -/
theorem scrypt_ok {s : State} (h : scryptRV.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ scryptRV.post s s' := by
  have hL := lay_ok h
  have h1248 : 1248 ≤ s.sp.toNat := h.1
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by simp only [locals]; omega) ?_
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, he⟩ => ?_)
  refine rest_ok hv hd name hL hc he fun u hu ho => WP.mono (restore_ok hL hu) fun v ⟨vra, vm, vsp, _, _, vg⟩ => ?_
  refine ⟨⟨fun r hr => vg r hr, ?_, vra⟩, ?_⟩
  · show v.sp + BitVec.ofNat 64 256 = s.sp
    rw [vsp, hu.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact lay_top s
  · show _ = some (bytesAt v.mem _ _)
    rw [vm]
    exact ho

end

end VG.Proof.Scrypt.RISCV64.Whole
