import VerifiedGarbage.Proof.AesOcb.AArch64.Callee

/-!
# AES-OCB on AArch64: the calls of the block functions

Untrusted: everything here is checked by Lean. `callBlocks b args` sets up
a call of `b` (`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`) with the
key schedule of the key context, the rounds in `x22`, the `n` blocks at `D`
that `args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data,
`dstD`) and the working space at `W + 512` (`callBlocks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (covers_left covers_cons covers_nil covers_append covers_off covers_prefix)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- The functions an instance calls. -/
def callees (v : BlocksImpl) : Callees := ⟨v.enc, v.dec, v.expand⟩

/-- `n` blocks at `D` for a call: apart from the key context and the working
space at `W + 512`, and readable and writable. -/
structure Dst (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  scr : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

theorem toNat_W {W : Addr} (hw : W.toNat + 2560 ≤ 2 ^ 64) {d : Nat} (hd : d < 2560) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Blocks of `W` below 512. -/
theorem dstW {K W : Addr} {s : State} (L : Lay K W) (P : Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    Dst K W s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [toNat_W L.ww (by omega)]; have := L.ww; omega
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

/-- What the arguments `args` of a call set: `x2` and `x3` (to `D` and `n`),
and nothing else. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .x2 = D ∧ s₁.gpr .x3 = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .x2 → r ≠ .x3 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
    s₁.wr = s.wr

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (d : Nat) (hd : d < 4096) :
    ArgsOk (oneBlock d) s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨_, by orun [oneBlock, h19, hd], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write]
  · simp [gpr_write, imm_lit 1 (by decide)]
  · simp [gpr_write, h1, h2]
  all_goals rfl

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D S : Addr}
    {R n : Nat} (h : BPost f s K D S R n s') (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s.gpr r = s₀.gpr r) (hsp : s.sp = s₀.sp) :
    BPost f s₀ K D S R n s' where
  rd := by rw [h.rd, hrd]
  wr := by rw [h.wr, hwr]
  sp := by rw [h.sp, hsp]
  saved r hr h30 := by rw [h.saved r hr h30, hg r hr h30]
  frame := by rw [← hm]; exact h.frame
  out := by rw [← hm]; exact h.out

/-- The arguments of a call of `b`, after `args`. -/
theorem callArgs_ok {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State}
    (E : Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {args : List Instr} {D' : Addr} {k : Nat} (ha : ArgsOk args s D' k) (hD : Dst K W s D' k) :
    WP isa (.block (args ++ [Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO])) s fun s₂ =>
      BCall s₂ K D' (W + BitVec.ofNat 64 512) R k ∧ s₂.mem = s.mem ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr ∧ ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s.gpr r := by
  obtain ⟨s₁, run₁, x2₁, x3₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := ha
  have h19 : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide), E.x19]
  have h20 : s₁.gpr .x20 = K := by rw [g₁ _ (by decide) (by decide), E.x20]
  have h22 : s₁.gpr .x22 = BitVec.ofNat 64 R := by rw [g₁ _ (by decide) (by decide), E.x22]
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 R ∧ s₂.gpr .x2 = D' ∧ s₂.gpr .x3 = BitVec.ofNat 64 k ∧
      s₂.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x4 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h20]
    · simp [gpr_write, h22]
    · simp [gpr_write, x2₁]
    · simp [gpr_write, x3₁]
    · simp [gpr_write, h19]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  have hD₂ := hD.of_eq (s' := s₂) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hc : BCall s₂ K D' (W + BitVec.ofNat 64 512) R k :=
    { x0 := x0₂, x1 := x1₂, x2 := x2₂, x3 := x3₂, x4 := x4₂, rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      ks := (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := hD.scr
      reads := covers_append (covers_cons (covers_prefix (by rw [rd₂, rd₁, wr₂, wr₁]; exact E.perm.k)
          (by decide)) covers_nil)
        (covers_cons hD₂.rd (covers_cons (covers_left (by rw [wr₂, wr₁]; exact E.perm.wC (by decide))) covers_nil))
      writes := covers_cons hD₂.wr (covers_cons (by rw [wr₂, wr₁]; exact E.perm.wC (by decide)) covers_nil) }
  refine WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], hc,
    by rw [m₂, m₁], by rw [sp₂, sp₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h30 => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [g₂ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    g₁ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State} (E : Env K W D R n SP s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {args : List Instr} {D' : Addr} {k : Nat} (ha : ArgsOk args s D' k) (hD : Dst K W s D' k) :
    WP isa (callBlocks b args) s (BPost f s K D' (W + BitVec.ofNat 64 512) R k) :=
  WP.seq (WP.mono (callArgs_ok L E hR ha hD) fun _ ⟨hc, m₂, sp₂, rd₂, wr₂, g₂⟩ =>
    WP.mono (blk_call ok nf hc) fun _ h => h.congr m₂ rd₂ wr₂ g₂ sp₂)

end VG.Proof.AesOcb.AArch64
