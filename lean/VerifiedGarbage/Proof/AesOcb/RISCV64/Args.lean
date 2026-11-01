module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesOcb.RISCV64

/-!
# AES-OCB on RISCV64: the calls of the block functions

Untrusted: everything here is checked by Lean. `callArgs ++ args` sets up a
call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` with the key
schedule of the key context, the rounds in `s3`, the `n` blocks at `D` that
`args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data, `dstD`)
and the working space at `W + 512` (`callBlocks_ok`); `encOne d` enciphers
the block at `W + d` (`encOne_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/Args.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem aesWith)
open VG.Proof.AesGcm.RISCV64 (Keeps covers_left covers_prefix)

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
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .a2 = D ∧ s₁.gpr .a3 = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .a2 → r ≠ .a3 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (hs0 : s.gpr .s0 = W) {d : Nat} (hd : d < 2048) :
    ArgsOk [.addi .a2 .s0 (d : Int), .li .a3 1] s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨(s.write .a2 (s.gpr .s0 + BitVec.ofNat 64 d)).write .a3 (BitVec.ofNat 64 1), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hs0], gpr_write_self _ _ _,
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl⟩⟩
  simp (disch := exact hd) only [runBlock_cons, runStep_some, ↓exec_addi_nat]
  rfl

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
    ∃ s₁, runBlock isa callArgs s = some s₁ ∧ s₁.gpr .a0 = s.gpr .s2 ∧ s₁.gpr .a1 = s.gpr .s3 ∧
      s₁.gpr .a4 = s.gpr .s0 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨((s.write .a0 (s.gpr .s2 + BitVec.ofNat 64 0)).write .a1 (s.gpr .s3 + BitVec.ofNat 64 0)).write .a4
    (s.gpr .s0 + BitVec.ofNat 64 512), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_of_ne _ _ (by decide), gpr_write_self, BitVec.add_zero],
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, BitVec.add_zero], gpr_write_self _ _ _,
    fun r h3 h4 h7 => by rw [gpr_write_of_ne _ _ h7, gpr_write_of_ne _ _ h4, gpr_write_of_ne _ _ h3],
    ⟨rfl, rfl, rfl, rfl⟩⟩
  rfl

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0))
include L

/-- The arguments of a call, after `callArgs` and `args`. -/
theorem callArgs_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {s : State}
    (E : Env V sp s) {args : List Instr} {D : Addr} {k : Nat}
    (ha : ∀ s₁, (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₁.gpr r = s.gpr r) → Keeps s s₁ → ArgsOk args s₁ D k)
    (hD : Dst (V .s2) (V .s0) s D k) :
    WP isa (.block (callArgs ++ args)) s fun s₂ =>
      BCall s₂ (V .s2) D (V .s0 + BitVec.ofNat 64 512) R k ∧
        (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
  obtain ⟨s₁, run₁, a0₁, a1₁, a4₁, g₁, k₁⟩ := callArgs_run (s := s)
  obtain ⟨s₂, run₂, a2₂, a3₂, g₂, k₂⟩ := ha s₁ g₁ k₁
  have k₂' : Keeps s s₂ := k₁.trans k₂
  have hD₂ := hD.of_eq (s' := s₂) k₂'.rd k₂'.wr
  have hc : BCall s₂ (V .s2) D (V .s0 + BitVec.ofNat 64 512) R k :=
    { a0 := by rw [g₂ _ (by decide) (by decide), a0₁, E.s2]
      a1 := by rw [g₂ _ (by decide) (by decide), a1₁, E.s3, hs3]
      a2 := a2₂, a3 := a3₂
      a4 := by rw [g₂ _ (by decide) (by decide), a4₁, E.s0]
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
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R)
    {s : State} (E : Env V sp s) {args : List Instr} {D : Addr} {k : Nat}
    (ha : ∀ s₁, (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₁.gpr r = s.gpr r) → Keeps s s₁ → ArgsOk args s₁ D k)
    (hD : Dst (V .s2) (V .s0) s D k) :
    WP isa (.seq (.block (callArgs ++ args)) (.call name c)) s
      (BPost f s (V .s2) D (V .s0 + BitVec.ofNat 64 512) R k) :=
  WP.seq (WP.mono (callArgs_ok L hR hs3 E ha hD) fun _ ⟨hc, g₂, k₂⟩ =>
    WP.mono (blk_call ok nf hc) fun _ h => h.congr k₂ fun r hr => g₂ r
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide))

/-- `encOne d`: the block at `W + d` enciphered. -/
theorem encOne_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {s : State}
    (E : Env V sp s) {d : Nat} (hd : d + 16 ≤ 512) :
    WP isa (encOne d) s (BPost Spec.Aes.cipher s (V .s2) (V .s0 + BitVec.ofNat 64 d)
      (V .s0 + BitVec.ofNat 64 512) R 1) :=
  callBlocks_ok L Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames hR hs3 E
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E.s0]) (by omega))
    (dstW L E.perm (by omega))

end

/-- After a call: the environment. -/
theorem BPost.env {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {V : Reg → BitVec 64} {sp : Addr}
    {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost f s K D S R n s') (E : Env V sp s) : Env V sp s' :=
  E.of_saved h.saved h.sp h.rd h.wr

end VG.Proof.AesOcb.RISCV64
