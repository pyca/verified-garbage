module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Callee
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Env
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesOcb.PPC64LE

/-!
# AES-OCB on PPC64LE: the calls of the block functions

Untrusted: everything here is checked by Lean. `callArgs ++ args` sets up a
call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` with the key
schedule of the key context, the rounds in `r28`, the `n` blocks at `D` that
`args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data, `dstD`)
and the working space at `W + 512` (`callBlocks_ok`); `encOne d` enciphers
the block at `W + d` (`encOne_ok`). As on AArch64
(`Proof/AesOcb/AArch64/Args.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem aesWith)
open VG.Proof.AesGcm.PPC64LE (Keeps covers_left covers_prefix)

/-- `n` blocks at `D` for a call: apart from the key context and the working
space at `W + 512`, and readable and writable. -/
structure Dst (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  scr : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

/-- Blocks of `W` below 512. -/
theorem dstW {K W : Addr} {s : State} (L : Lay K W) (P : Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    Dst K W s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [L.toNat_w (by omega)]; have := L.ww; omega
  k := L.k_w.sub_right (Lay.wSub (by omega))
  scr := L.w_w (.inl (by omega)) (by omega) (by decide)
  rd := covers_left (P.wC (by omega))
  wr := P.wC (by omega)

/-- Blocks of the data. -/
theorem dstD {K W : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W s D (16 * n)) : Dst K W s D n where
  wrap := h.wrap
  k := h.k
  scr := h.w.sub_right (Lay.wSub (by decide))
  rd := h.rd
  wr := h.wr

theorem Dst.of_eq {K W : Addr} {s s' : State} {D : Addr} {n : Nat} (h : Dst K W s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dst K W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, wr := by rw [hwr]; exact h.wr }

/-- What the arguments `args` of a call set: `r5` and `r6` (to `D` and `n`),
and nothing else. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .r5 = D ∧ s₁.gpr .r6 = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .r5 → r ≠ .r6 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) {d : Nat} (hd : d < 2 ^ 15) :
    ArgsOk [.addi .r5 .r31 d, .li .r6 1] s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨(s.write .r5 (s.gpr .r31 + BitVec.ofNat 64 d)).write .r6 (BitVec.ofNat 64 1), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, h31], gpr_write_self _ _ _,
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hd, ne_eq, reduceCtorEq, not_false_eq_true,
    and_self, ↓reduceIte, Nat.reduceLT, Nat.reducePow]

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D S : Addr}
    {R n : Nat} (h : BPost f s K D S R n s') (hk : Keeps s₀ s) (hg : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) :
    BPost f s₀ K D S R n s' where
  rd := by rw [h.rd, hk.rd]
  wr := by rw [h.wr, hk.wr]
  sp := by rw [h.sp, hk.sp]
  saved r hr := by rw [h.saved r hr, hg r hr]
  frame := by rw [← hk.mem]; exact h.frame
  out := by rw [← hk.mem]; exact h.out

theorem callArgs_run {s : State} :
    ∃ s₁, runBlock isa callArgs s = some s₁ ∧ s₁.gpr .r3 = s.gpr .r29 ∧ s₁.gpr .r4 = s.gpr .r28 ∧
      s₁.gpr .r7 = s.gpr .r31 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨((s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28)).write .r7 (s.gpr .r31 + BitVec.ofNat 64 512), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_of_ne _ _ (by decide), gpr_write_self],
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self], gpr_write_self _ _ _,
    fun r h3 h4 h7 => by rw [gpr_write_of_ne _ _ h7, gpr_write_of_ne _ _ h4, gpr_write_of_ne _ _ h3],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [callArgs, scrO, Impl.AesGcm.PPC64LE.mov, runBlock_cons, runStep_some, runBlock_nil, exec, ne_eq,
    reduceCtorEq, not_false_eq_true, and_self, ↓reduceIte, Nat.reduceLT, Nat.reducePow, BitVec.or_self,
    gpr_write_of_ne _ _ (show ¬Reg.r28 = .r3 by decide), gpr_write_of_ne _ _ (show ¬Reg.r31 = .r3 by decide),
    gpr_write_of_ne _ _ (show ¬Reg.r31 = .r4 by decide)]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31))
include L

/-- The arguments of a call, after `callArgs` and `args`. -/
theorem callArgs_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {s : State}
    (E : Env V sp s) {args : List Instr} {D : Addr} {k : Nat}
    (ha : ∀ s₁, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = s.gpr r) → Keeps s s₁ → ArgsOk args s₁ D k)
    (hD : Dst (V .r29) (V .r31) s D k) :
    WP isa (.block (callArgs ++ args)) s fun s₂ =>
      BCall s₂ (V .r29) D (V .r31 + BitVec.ofNat 64 512) R k ∧
        (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
  obtain ⟨s₁, run₁, r3₁, r4₁, r7₁, g₁, k₁⟩ := callArgs_run (s := s)
  obtain ⟨s₂, run₂, r5₂, r6₂, g₂, k₂⟩ := ha s₁ g₁ k₁
  have k₂' : Keeps s s₂ := k₁.trans k₂
  have hD₂ := hD.of_eq (s' := s₂) k₂'.rd k₂'.wr
  have hc : BCall s₂ (V .r29) D (V .r31 + BitVec.ofNat 64 512) R k :=
    { r3 := by rw [g₂ _ (by decide) (by decide), r3₁, E.r29]
      r4 := by rw [g₂ _ (by decide) (by decide), r4₁, E.r28, h28]
      r5 := r5₂, r6 := r6₂
      r7 := by rw [g₂ _ (by decide) (by decide), r7₁, E.r31]
      rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      ks := (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := hD.scr
      reads := Covers.cons (covers_prefix (by rw [k₂'.rd, k₂'.wr]; exact E.perm.k) (by decide))
        (Covers.cons hD₂.rd (Covers.cons (covers_left (by rw [k₂'.wr]; exact E.perm.wC (by decide)))
          Covers.nil))
      writes := Covers.cons hD₂.wr (Covers.cons (by rw [k₂'.wr]; exact E.perm.wC (by decide)) Covers.nil) }
  exact WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, hc,
    fun r h3 h4 h5 h6 h7 => by rw [g₂ r h5 h6, g₁ r h3 h4 h7], k₂'⟩⟩)

/-- A call of a block function, after `callArgs` and `args`. -/
theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R)
    {s : State} (E : Env V sp s) {args : List Instr} {D : Addr} {k : Nat}
    (ha : ∀ s₁, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = s.gpr r) → Keeps s s₁ → ArgsOk args s₁ D k)
    (hD : Dst (V .r29) (V .r31) s D k) :
    WP isa (.seq (.block (callArgs ++ args)) (.call name c)) s
      (BPost f s (V .r29) D (V .r31 + BitVec.ofNat 64 512) R k) :=
  WP.seq (WP.mono (callArgs_ok L hR h28 E ha hD) fun _ ⟨hc, g₂, k₂⟩ =>
    WP.mono (blk_call ok nf hc) fun _ h => h.congr k₂ fun r hr => g₂ r
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide))

/-- `encOne d`: the block at `W + d` enciphered. -/
theorem encOne_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {s : State}
    (E : Env V sp s) {d : Nat} (hd : d + 16 ≤ 512) :
    WP isa (encOne d) s (BPost Spec.Aes.cipher s (V .r29) (V .r31 + BitVec.ofNat 64 d)
      (V .r31 + BitVec.ofNat 64 512) R 1) :=
  callBlocks_ok L Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames hR h28 E
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E.r31]) (by omega))
    (dstW L E.perm (by omega))

end

/-- After a call: the environment. -/
theorem BPost.env {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {V : Reg → BitVec 64} {sp : Addr}
    {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost f s K D S R n s') (E : Env V sp s) : Env V sp s' :=
  E.of_saved h.saved h.sp h.rd h.wr

end VG.Proof.AesOcb.PPC64LE
