module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PreG
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.OnePass
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `seal_split` on x86-64: the whole groups in one pass

Untrusted: everything here is checked by Lean. For the texts `nTest` takes
(`1 ≤ ⌊sl / 256⌋ < ⌊n / 256⌋`), `prefixN` copies the bytes of `src` after its
last whole group to `dst` (the gathering's `copy`), and encrypts and absorbs
the `16 ⌊sl / 256⌋` blocks at `src` and then the `16 ⌊n / 256⌋` of the data
after them at `dst` by one loop `encN` (`StitchR.encN` or
`StitchZHTo.encN`, any meeting `EncNOk`, proven from the permissions it
needs, `regionModel.wp_narrow`): the first `256 ⌊n / 256⌋` bytes of the
plaintext, and the data from them on kept (`PPostG`). Other texts take
`prefix` (`prefixNOk`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Spec.Aes (bytesAt)

/-- A loop that encrypts and absorbs the `nb` blocks at `src` and then the
blocks at `dst` after them, `N` in all (`StitchR.NPost`), from a state that
the out-of-place loops could start from (`SPreTo`) with what `StitchR.NPre`
adds. -/
def EncNOk (np : Nat) (hpn : 8 ≤ np ∧ np ≤ 24) (c : Prog isa) : Prop :=
  ∀ {s₀ : State} {N : Nat}, Gcm.X86_64.Stitch.SPreTo (CtxMode.preparedN np hpn) s₀ → Gcm.X86_64.Stitch.nb s₀ % 16 = 0 →
    Gcm.X86_64.StitchR.NPre (CtxMode.preparedN np hpn) s₀ N → WP isa c s₀ (Gcm.X86_64.StitchR.NPost s₀ N)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Gcm (Ctr xorKs)

/-- `a - 1 < b - 1` unsigned, for `a ≤ b`: `1 ≤ a < b`. -/
theorem pred_lt_pred {a b : Nat} (hb : b < 2 ^ 64) (hab : a ≤ b) :
    (BitVec.ofNat 64 a - 1#64).toNat < (BitVec.ofNat 64 b - 1#64).toNat ↔ 1 ≤ a ∧ a < b := by
  have ha : a < 2 ^ 64 := by omega_arith
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  omega_arith

/-- `16 ⌊a / 256⌋` and `256 ⌊a / 256⌋`, by shifts. -/
theorem shr8shl4 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 8 <<< 4 = BitVec.ofNat 64 (16 * (a / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt (by omega_arith),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem shr8shl8 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 8 <<< 8 = BitVec.ofNat 64 (256 * (a / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, toNat_ofNat_of_lt ha, toNat_ofNat_of_lt (by omega_arith),
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

section
variable {Ctx W SP : Addr}

/-- `CF` if `1 ≤ ⌊sl / 256⌋ < ⌊n / 256⌋`. -/
theorem nTest_ok {n sl : Nat} (hn : n < 2 ^ 64) (hsl : sl ≤ n) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block SealSplit.nTest) s fun t => t.cf = some (decide (1 ≤ sl / 256 ∧ sl / 256 < n / 256)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have h₁ := Gather.shr_ofNat sl 8 (by omega_arith)
  have h₂ := Gather.shr_ofNat n 8 hn
  have i1 := imm_eq (n := 1) (by decide)
  unfold SealSplit.nTest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, hslot, hlen, h₁, h₂, i1], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, reduceCtorEq, ↓reduceIte,
      Nat.reducePow, pred_lt_pred (Nat.lt_of_le_of_lt (Nat.div_le_self n 256) hn) (Nat.div_le_div_right hsl)]
  · intro r ha hc; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, ha, hc]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- The bytes of `src` after its last whole group: their number and their
address and that of their copy. -/
theorem nCopyArgs_ok {D S : Addr} {sl : Nat} (hsl : sl < 2 ^ 64) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.nCopyArgs) s fun t => t.gpr .rcx = BitVec.ofNat 64 (sl - 256 * (sl / 256)) ∧
      t.gpr .rsi = S + BitVec.ofNat 64 (256 * (sl / 256)) ∧ t.gpr .rdi = D + BitVec.ofNat 64 (256 * (sl / 256)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have e8 := shr8shl8 hsl
  have esub : BitVec.ofNat 64 sl - BitVec.ofNat 64 (256 * (sl / 256)) = BitVec.ofNat 64 (sl - 256 * (sl / 256)) :=
    ofNat_sub (by omega_arith) hsl
  unfold SealSplit.nCopyArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, hslot, hdat, hsrc, e8, esub], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, esub]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hsrc]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hdat]
  · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c, d]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- The arguments of `encN`. -/
theorem nArgs_ok {R : Nat} {D S : Addr} {n sl : Nat} (hn : n < 2 ^ 64) (hsl : sl ≤ n) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block SealSplit.nArgs) s fun t => t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 R ∧
      t.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48 ∧
      t.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16 ∧ t.gpr .r8 = S ∧
      t.gpr .r9 = BitVec.ofNat 64 (16 * (sl / 256)) ∧ t.gpr .r10 = D ∧ t.gpr .rbx = D ∧
      t.gpr .rbp = BitVec.ofNat 64 (16 * (n / 256) - 16 * (sl / 256)) ∧ t.gpr .r11 = W + BitVec.ofNat 64 448 ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₄ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₅ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have e₁ := shr8shl4 (show sl < 2 ^ 64 by omega_arith)
  have e₂ := shr8shl4 hn
  have esub : BitVec.ofNat 64 (16 * (n / 256)) - BitVec.ofNat 64 (16 * (sl / 256)) =
      BitVec.ofNat 64 (16 * (n / 256) - 16 * (sl / 256)) :=
    ofNat_sub (by have := Nat.div_le_div_right (c := 256) hsl; omega_arith) (by omega_arith)
  unfold SealSplit.nArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r13, he.r14, he.r15, q₁, q₂, q₃, q₄, q₅, hR.1, hdat, hsrc, hslot, hlen, e₁, e₂, esub],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r13]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, hR.1]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, hsrc]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, e₁]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, hdat]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, hdat]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, e₁, e₂, esub]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, imm_eq, bScrO]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- `len` kept at `auxO`, and the data from `256 ⌊n / 256⌋` on as the data. -/
theorem nRest_ok {D : Addr} {n : Nat} (hn : n < 2 ^ 64) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block SealSplit.nRest) s fun t =>
      t.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧
      t.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 256 * (n / 256)) ∧
      t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      Frame [⟨W + BitVec.ofNat 64 200, 24⟩] s.mem t.mem ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have e8 := shr8shl8 hn
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 (256 * (n / 256)) = BitVec.ofNat 64 (n - 256 * (n / 256)) :=
    ofNat_sub (by omega_arith) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by have := he.perm; omega_arith) (by omega_arith)
  have p₁ := sep 216 208 (by decide) (by decide) (by decide)
  have p₂ := sep 216 200 (by decide) (by decide) (by decide)
  have p₃ := sep 208 200 (by decide) (by decide) (by decide)
  have p₄ := sep 200 208 (by decide) (by decide) (by decide)
  have p₅ := sep 200 216 (by decide) (by decide) (by decide)
  have hdat' : ((s.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 n)).writeW (W + BitVec.ofNat 64 208)
      (BitVec.ofNat 64 (n - 256 * (n / 256)))).readW (W + BitVec.ofNat 64 200) 64 = D := by
    rw [Mem.readW_writeW_sep p₄ (by decide), Mem.readW_writeW_sep p₅ (by decide), hdat]
  unfold SealSplit.nRest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₂, q₃, w₁, w₂, w₃, hlen, e8, esub, hdat'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mem_arithFlags, mem_setReg, mem_setFlags, Mem.readW_writeW_self64, BitVec.add_comm]
  · simp only [mem_arithFlags, mem_setReg, mem_setFlags]
    rw [Mem.readW_writeW_sep p₃ (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg, mem_setFlags]
    rw [Mem.readW_writeW_sep p₂ (by decide), Mem.readW_writeW_sep p₁ (by decide), Mem.readW_writeW_self64]
  · have c : ∀ d, 200 ≤ d → d + 8 ≤ 224 → (⟨W + BitVec.ofNat 64 200, 24⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by have := he.perm; omega_arith)
    simp only [mem_arithFlags, mem_setReg, mem_setFlags]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
  all_goals simp [rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags, wr_setReg, wr_setFlags]

end

/-- A prefix of a region covered is accessible. -/
theorem in_pre {rs : List Region} {p : Addr} {k n : Nat} (h : Covers [⟨p, n⟩] rs) (hk : k ≤ n) :
    InRegions rs p k :=
  h _ _ ⟨_, List.mem_singleton_self _, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩

/-- The bytes at `p + |xs|` after `xs` written at `p`, from `p` on. -/
theorem bytesAt_writeBytes_from (m : Mem) (p : Addr) (xs : List Byte) {k : Nat} (h : xs.length + k < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p (xs.length + k) = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) k := by
  rw [bytesAt_add, bytesAt_writeBytes_self _ _ _ (by omega_arith)]
  congr 1
  exact bytesAt_frame (writeBytes_frame' m (rfl : xs.length = xs.length)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base p (Nat.le_refl _) (by omega_arith)) (by omega_arith)

/-! ## The path of `nTest`'s texts, step by step -/

section
variable (Ctx W SP D S : Addr) (R n sl : Nat) (σ : State)

/-- Where the bytes of `src` after its last whole group start. -/
abbrev cOf (sl : Nat) : Nat := 256 * (sl / 256)

/-- After `nCopyArgs`. -/
structure NA (t : State) : Prop where
  rcx : t.gpr .rcx = BitVec.ofNat 64 (sl - cOf sl)
  rsi : t.gpr .rsi = S + BitVec.ofNat 64 (cOf sl)
  rdi : t.gpr .rdi = D + BitVec.ofNat 64 (cOf sl)
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → t.gpr r = σ.gpr r
  mem : t.mem = σ.mem
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- The memory after the copy. -/
abbrev nMemC : Mem := writeBytes σ.mem (D + BitVec.ofNat 64 (cOf sl)) (bytesAt σ.mem (S + BitVec.ofNat 64 (cOf sl)) (sl - cOf sl))

/-- After the copy. -/
structure NB (t : State) : Prop where
  mem : t.mem = nMemC D S sl σ
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r10 → t.gpr r = σ.gpr r
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- After `nArgs`: the loop's arguments. -/
structure NC (t : State) : Prop where
  rdi : t.gpr .rdi = Ctx
  rsi : t.gpr .rsi = BitVec.ofNat 64 R
  rdx : t.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
  rcx : t.gpr .rcx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16
  r8 : t.gpr .r8 = S
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (sl / 256))
  r10 : t.gpr .r10 = D
  rbx : t.gpr .rbx = D
  rbp : t.gpr .rbp = BitVec.ofNat 64 (16 * (n / 256) - 16 * (sl / 256))
  r11 : t.gpr .r11 = W + BitVec.ofNat 64 448
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t.gpr r = σ.gpr r
  mem : t.mem = nMemC D S sl σ
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

end

section
variable {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl s)
include h

/-- `nCopyArgs`. -/
theorem nA_ok {t : State} (g : ∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) (tm : t.mem = s.mem)
    (trd : t.rd = s.rd) (twr : t.wr = s.wr) : WP isa (.block SealSplit.nCopyArgs) t (NA D S sl s) := by
  have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => g r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
    trd twr
  refine WP.mono (nCopyArgs_ok (D := D) (S := S) (sl := sl) (by have := h.sl_le; have := h.data.ok.lt; omega_arith) he
    (by rw [tm]; exact h.dat) (by rw [tm]; exact h.src) (by rw [tm]; exact h.slen))
    fun t₁ ⟨cx, si, di, g₁, m₁, rd₁, wr₁⟩ => ⟨cx, si, di, fun r a b c d => by rw [g₁ r a b c d, g r a b],
      m₁.trans tm, rd₁.trans trd, wr₁.trans twr⟩

/-- The copy. -/
theorem nB_ok {t : State} (hA : NA D S sl s t) : WP isa SealGather.copy t (NB D S sl s) := by
  have hsl := h.sl_le
  have hn := h.data.ok.lt
  have hc : cOf sl ≤ sl := Nat.mul_div_le sl 256
  have cp : Short.CopyPre t (S + BitVec.ofNat 64 (cOf sl)) (D + BitVec.ofNat 64 (cOf sl)) (sl - cOf sl) :=
    ⟨hA.rsi, hA.rdi, hA.rcx, by simp only [cOf]; omega_arith,
      by rw [hA.rd, hA.wr]; exact covers_off' h.srcCov (by omega_arith) (by omega_arith),
      by rw [hA.wr]; exact covers_off' h.data.wr (by omega_arith) (by omega_arith),
      (h.sD.sub_left (Offset.sub_base S (by omega_arith))).sub_right (Offset.sub_base D (by omega_arith))⟩
  exact WP.mono (Gather.copy_ok cp) fun t₂ ⟨m₂, g₂, rd₂, wr₂⟩ =>
    ⟨by rw [m₂, hA.mem], fun r a b c d e f => by rw [g₂ r a e f, hA.gpr r a b c d], rd₂.trans hA.rd, wr₂.trans hA.wr⟩

omit h in
/-- What the copy keeps: all but `dst`'s bytes from `256 ⌊sl / 256⌋` to `sl`. -/
theorem nMemC_frame : Frame [⟨D + BitVec.ofNat 64 (cOf sl), sl - cOf sl⟩] s.mem (nMemC D S sl s) :=
  writeBytes_frame' _ (length_bytesAt _ _ _)

theorem cOf_sub : Region.Sub ⟨D + BitVec.ofNat 64 (cOf sl), sl - cOf sl⟩ ⟨D, n⟩ := by
  have := h.sl_le; have : cOf sl ≤ sl := Nat.mul_div_le sl 256
  exact Offset.sub_base D (by omega_arith)

/-- A slot of `W`, kept by the copy. -/
theorem nMemC_slot {d : Nat} (hd : d + 8 ≤ 2560) :
    (nMemC D S sl s).readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  (nMemC_frame (D := D) (S := S) (sl := sl) (s := s)).readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.data.ok.w.sub_left (cOf_sub h)).sub_right (Lay.wSub hd)).symm) (by decide)

/-- `nArgs`. -/
theorem nC_ok {t : State} (hB : NB D S sl s t) : WP isa (.block SealSplit.nArgs) t (NC Ctx W D S R n sl s) := by
  have ne : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r10 := by
    decide
  have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => have e := ne r hr
    hB.gpr r e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2) hB.rd hB.wr
  have sl₂ : ∀ d, d + 8 ≤ 2560 → t.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => by rw [hB.mem]; exact nMemC_slot h hd
  refine WP.mono (nArgs_ok (D := D) (S := S) h.data.ok.lt h.sl_le he
    ⟨by rw [sl₂ 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩ (by rw [sl₂ 200 (by decide)]; exact h.dat)
    (by rw [sl₂ 224 (by decide)]; exact h.src) (by rw [sl₂ 192 (by decide)]; exact h.slen)
    (by rw [sl₂ 208 (by decide)]; exact h.len)) fun t₃ ⟨di, si, dx, cx, r8, r9, r10, bx, bp, r11, g₃, m₃, rd₃, wr₃⟩ =>
      ⟨di, si, dx, cx, r8, r9, r10, bx, bp, r11, fun r hr => by
        rw [g₃ r hr]; have e := ne r hr; exact hB.gpr r e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2,
      m₃.trans hB.mem, rd₃.trans hB.rd, wr₃.trans hB.wr⟩

/-- The loop's start, from `nArgs`'s state. -/
theorem nLoop (hC : 1 ≤ sl / 256 ∧ sl / 256 < n / 256) {t : State} (hN : NC Ctx W D S R n sl s t) :
    Gcm.X86_64.Stitch.SPreTo (CtxMode.preparedN np hpn) t ∧ Gcm.X86_64.StitchR.NPre (CtxMode.preparedN np hpn) t (16 * (n / 256)) ∧
      Gcm.X86_64.Stitch.nb t % 16 = 0 := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have hwD := h.data.ok.wrap
  have hwS := h.sWrap
  have dR₂ := cOf_sub h
  have fr₂ := nMemC_frame (D := D) (S := S) (sl := sl) (s := s)
  generalize hCd : sl / 256 = C at hC
  generalize hGd : n / 256 = G at hC ⊢
  have hc : 256 * C ≤ sl := by subst hCd; omega_arith
  have hG : 256 * G ≤ n := by subst hGd; omega_arith
  have r9₃ := hN.r9
  have bp₃ := hN.rbp
  simp only [hCd, hGd] at r9₃ bp₃
  have ws : (W + BitVec.ofNat 64 448).toNat = W.toNat + 448 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 448) (by decide)]; have := L.ww; omega_arith
  have cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  have yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  have pW : Region.Sub ⟨W + BitVec.ofNat 64 448, 1024⟩ ⟨W, 2560⟩ := Lay.wSub (by decide)
  have sC : Region.Sub ⟨S, 16 * (16 * C)⟩ ⟨S, sl⟩ := Region.sub_prefix (by omega_arith)
  have dC : Region.Sub ⟨D, 16 * (16 * C)⟩ ⟨D, n⟩ := Region.sub_prefix (by omega_arith)
  have dG : Region.Sub ⟨D, 16 * (16 * G)⟩ ⟨D, n⟩ := Region.sub_prefix (by omega_arith)
  have kD : (⟨Ctx, (CtxMode.preparedN np hpn).len⟩ : Region).Disjoint ⟨D, n⟩ := h.ext.cd
  have hok : (CtxMode.preparedN np hpn).ok t.mem Ctx := by
    rw [hN.mem]
    exact (CtxMode.preparedN np hpn).frame fr₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact kD.sub_right dR₂) h.ext.w h.ext.ok
  have hnb : (t.gpr .r9).toNat = 16 * C := by rw [r9₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hR : (t.gpr .rsi).toNat = R := by
    rw [hN.rsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)]
  have pB : Region.Sub ⟨W + BitVec.ofNat 64 448, 1024⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
    Offset.sub _ (by decide) (by decide)
  refine ⟨?_, ?_, by show (t.gpr .r9).toNat % 16 = 0; rw [hnb]; omega_arith⟩
  · refine { rounds := by
               show (t.gpr .rsi).toNat = 10 ∨ (t.gpr .rsi).toNat = 12 ∨ (t.gpr .rsi).toNat = 14
               rw [hR]; exact h.rounds.2
             nb16 := by show 16 ≤ (t.gpr .r9).toNat; rw [hnb]; omega_arith
             k_in := ?_, c_in := ?_, y_in := ?_, s_in := ?_, o_in := ?_, p_in := ?_, k_c := ?_, k_y := ?_,
             k_o := ?_, k_p := ?_, s_c := ?_, s_y := ?_, s_o := ?_, s_p := ?_, o_c := ?_, o_y := ?_, o_p := ?_,
             p_c := ?_, p_y := ?_, c_y := ?_, wrap_s := ?_, wrap_o := ?_, wrap_k := ?_, wrap_p := ?_, ok := ?_ }
    all_goals simp only [Gcm.X86_64.Stitch.kp, Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.sp,
      Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.sR,
      Gcm.X86_64.Stitch.oR, Gcm.X86_64.Stitch.pR, Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR,
      hN.rdi, hN.rdx, hN.rcx, hN.r8, hN.r10, hN.r11, hnb, hN.rd, hN.wr]
    exacts [in_pre h.ext.cov (Nat.le_refl _),
      by rw [add_ofNat_assoc]; exact h.env.perm.wW (by decide),
      by rw [add_ofNat_assoc]; exact h.env.perm.wW (by decide),
      in_pre h.srcCov (by omega_arith), in_pre h.data.wr (by omega_arith), h.env.perm.wW (by decide),
      h.ext.cs.sub_right cb_sub, h.ext.cs.sub_right y_sub, kD.sub_right dC, h.ext.cw.sub_right pW,
      (h.sW.sub_left sC).sub_right cW, (h.sW.sub_left sC).sub_right yW, (h.sD.sub_left sC).sub_right dC,
      (h.sW.sub_left sC).sub_right pW, (h.data.ok.w.sub_left dC).sub_right cW,
      (h.data.ok.w.sub_left dC).sub_right yW, (h.data.ok.w.sub_left dC).sub_right pW,
      ((L.sb.sub_left cb_sub).sub_right pB).symm, ((L.sb.sub_left y_sub).sub_right pB).symm,
      Offset.disjoint _ (.inr (by decide)) (by have := L.sw; omega_arith) (by have := L.sw; omega_arith),
      by omega_arith, by omega_arith, h.ext.w, by rw [ws]; have := L.ww; omega_arith, hok]
  · refine { le := by show (t.gpr .r9).toNat ≤ _; rw [hnb]; omega_arith
             m16 := by omega_arith
             rbx := by show t.gpr .rbx = t.gpr .r10; rw [hN.rbx, hN.r10]
             rbp := by show t.gpr .rbp = BitVec.ofNat 64 (16 * G - (t.gpr .r9).toNat); rw [bp₃, hnb]
             o_in := ?_, k_o := ?_, o_c := ?_, o_y := ?_, o_p := ?_, wrap := ?_ }
    all_goals simp only [Gcm.X86_64.Stitch.kp, Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.op,
      Gcm.X86_64.Stitch.pp, Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.pR,
      Gcm.X86_64.StitchR.nR, hN.rdi, hN.rdx, hN.rcx, hN.r10, hN.r11, hN.wr]
    exacts [in_pre h.data.wr (by omega_arith), kD.sub_right dG, (h.data.ok.w.sub_left dG).sub_right cW,
      (h.data.ok.w.sub_left dG).sub_right yW, (h.data.ok.w.sub_left dG).sub_right pW, by omega_arith]

/-- The loop. -/
theorem nD_ok {c : Prog isa} (hE : EncNOk np hpn c) (hC : 1 ≤ sl / 256 ∧ sl / 256 < n / 256) {t : State} (hN : NC Ctx W D S R n sl s t) :
    WP isa c t (Gcm.X86_64.StitchR.NPost t (16 * (n / 256))) :=
  have L := nLoop h hC hN
  hE L.1 L.2.2 L.2.1

/-- `nRest` after the loop: what `prefixN` leaves. -/
theorem nE_ok (hC : 1 ≤ sl / 256 ∧ sl / 256 < n / 256) {t₃ s₄ : State} (hN : NC Ctx W D S R n sl s t₃)
    (hP : Gcm.X86_64.StitchR.NPost t₃ (16 * (n / 256)) s₄) :
    WP isa (.block SealSplit.nRest) s₄ (PPostG Ctx W SP D S R n sl (16 * (n / 256)) s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have hwD := h.data.ok.wrap
  have hwS := h.sWrap
  have dR₂ := cOf_sub h
  have fr₂ := nMemC_frame (D := D) (S := S) (sl := sl) (s := s)
  obtain ⟨hp, hnp, -⟩ := nLoop h hC hN
  have hnb : (t₃.gpr .r9).toNat = 16 * (sl / 256) := by
    rw [hN.r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hR : (t₃.gpr .rsi).toNat = R := by
    rw [hN.rsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases h.rounds.2 with h | h | h <;> subst h <;> decide)]
  generalize hCd : sl / 256 = C at hC hnb
  generalize hGd : n / 256 = G at hC hP hnp ⊢
  have hc : 256 * C ≤ sl := by subst hCd; omega_arith
  have hG : 256 * G ≤ n := by subst hGd; omega_arith
  have hsG : sl < 256 * G := by subst hCd; omega_arith
  simp only [cOf, hCd] at dR₂ fr₂
  have cW : Region.Sub (cbR W) ⟨W, 2560⟩ := fun a hc => st_w a (cb_sub a hc)
  have yW : Region.Sub (yR W) ⟨W, 2560⟩ := fun a hc => st_w a (y_sub a hc)
  have pW : Region.Sub ⟨W + BitVec.ofNat 64 448, 1024⟩ ⟨W, 2560⟩ := Lay.wSub (by decide)
  have pS : Region.Sub ⟨W + BitVec.ofNat 64 448, 1024⟩ (scR W) := Offset.sub _ (by decide) (by decide)
  have dG : Region.Sub ⟨D, 16 * (16 * G)⟩ ⟨D, n⟩ := Region.sub_prefix (by omega_arith)
  have kD : (⟨Ctx, (CtxMode.preparedN np hpn).len⟩ : Region).Disjoint ⟨D, n⟩ := h.ext.cd
  -- What the loop writes: the counter block, `Y`, the first `256 G` bytes at `dst` and the powers.
  have f₄ : Frame [cbR W, yR W, ⟨D, 16 * (16 * G)⟩, ⟨W + BitVec.ofNat 64 448, 1024⟩] (nMemC D S sl s) s₄.mem := by
    have := hP.frame
    simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.pR, Gcm.X86_64.StitchR.nR,
      Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp, hN.rdx, hN.rcx, hN.r10,
      hN.r11, hN.mem] at this
    exact this
  have g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [hP.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN.keep _ (by simp))
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := h.env.keep g₄ (hP.rd.trans hN.rd) (hP.wr.trans hN.wr)
  have k₄ : ∀ d, 128 ≤ d → d + 8 ≤ 448 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = (nMemC D S sl s).readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · show Region.Disjoint _ ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩
        rw [add_ofNat_assoc]; exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · show Region.Disjoint _ ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩
        rw [add_ofNat_assoc]; exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact ((h.data.ok.w.sub_left dG).sub_right (Lay.wSub (by omega_arith))).symm
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)) (by decide)
  refine WP.mono (nRest_ok (D := D) hn he₄ (by rw [k₄ 200 (by decide) (by decide), nMemC_slot h (by decide)]; exact h.dat)
    (by rw [k₄ 208 (by decide) (by decide), nMemC_slot h (by decide)]; exact h.len))
    fun s₅ ⟨dat₅, len₅, aux₅, f₅, g₅, rd₅, wr₅⟩ => ?_
  rw [hGd] at dat₅ len₅
  have e256 : 16 * (16 * G) = 256 * G := by omega_arith
  have dW200 : ∀ X : Region, X.Disjoint ⟨W, 2560⟩ → ∀ r ∈ [(⟨W + BitVec.ofNat 64 200, 24⟩ : Region)],
      X.Disjoint r := fun X hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hX.sub_right (Lay.wSub (by decide))
  -- The key, the counter block and `Y`, kept by the copy.
  have hc₂ : ciphOf (nMemC D S sl s) Ctx R = ciphOf s.mem Ctx R := ciph_frame fr₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.data.ctx.sub_right dR₂) h.rounds.2
  have dD₂ : ∀ X : Region, X.Disjoint ⟨D, n⟩ →
      ∀ r ∈ [(⟨D + BitVec.ofNat 64 (256 * C), sl - 256 * C⟩ : Region)], X.Disjoint r := fun X hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hX.sub_right dR₂
  have hcb₂ : blockAt (nMemC D S sl s) (cbA W) = blockAt s.mem (cbA W) :=
    blockAt_frame fr₂ (dD₂ _ (h.data.ok.w.sub_right cW).symm)
  have hy₂ : blockAt (nMemC D S sl s) (yA W) = blockAt s.mem (yA W) :=
    blockAt_frame fr₂ (dD₂ _ (h.data.ok.w.sub_right yW).symm)
  have hH₂ : blockAt (nMemC D S sl s) (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq]; exact blockAt_frame fr₂ (dD₂ _ (kD.sub_left (Offset.sub_base Ctx (by exact (by decide : (240 + 16 : Nat) ≤ 1024)))))
  -- The data from `256 G` on, kept by all three.
  have tl : bytesAt s₅.mem (D + BitVec.ofNat 64 (256 * G)) (n - 256 * G) =
      bytesAt s.mem (D + BitVec.ofNat 64 (256 * G)) (n - 256 * G) := by
    have dT : Region.Sub ⟨D + BitVec.ofNat 64 (256 * G), n - 256 * G⟩ ⟨D, n⟩ := Offset.sub_base D (by omega_arith)
    rw [bytesAt_frame f₅ (dW200 _ (h.data.ok.w.sub_left dT)) (by omega_arith),
      bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (h.data.ok.w.sub_left dT).sub_right cW
        · exact (h.data.ok.w.sub_left dT).sub_right yW
        · exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
        · exact (h.data.ok.w.sub_left dT).sub_right pW) (by omega_arith),
      bytesAt_frame fr₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)]
  have pt₂ : (splitPt s.mem D S n sl).drop (16 * (16 * G)) = bytesAt s.mem (D + BitVec.ofNat 64 (256 * G)) (n - 256 * G) := by
    simp only [splitPt]
    rw [List.drop_append, List.drop_eq_nil_of_le (by rw [length_bytesAt]; omega_arith), List.nil_append, length_bytesAt,
      List.drop_drop, bytesAt_drop' _ _ (by omega_arith), e256, show sl + (256 * G - sl) = 256 * G by omega_arith]
  refine { env := he₄.keep g₅ rd₅ wr₅
           rd := by rw [rd₅, hP.rd, hN.rd]
           wr := by rw [wr₅, hP.wr, hN.wr]
           le := by omega_arith
           frame := ?_, enc := ?_, ctr := ?_, y := ?_
           tail := by rw [pt₂, e256, tl]
           dat := by rw [e256]; exact dat₅
           len := by rw [e256]; exact len₅
           aux := aux₅ }
  · refine (fr₂.sub fun r hr => ?_).trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨D, n⟩, by simp, dR₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨D, n⟩, by simp, dG⟩
      · exact ⟨_, by simp, pS⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · -- The ciphertext.
    have b4 := Gcm.X86_64.StitchR.NPost.bytes hp hnp hP
    simp only [Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.sp, Gcm.X86_64.StitchZTo.oAddr, Gcm.X86_64.Stitch.ciph,
      Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.cb, Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.kp,
      Gcm.X86_64.Stitch.nr, hN.r10, hN.r8, hN.rdi, hN.rdx, hnb, hR, hN.mem] at b4
    have b5 : bytesAt s₅.mem D (16 * (16 * G)) = bytesAt s₄.mem D (16 * (16 * G)) :=
      bytesAt_frame f₅ (dW200 _ (h.data.ok.w.sub_left dG)) (by omega_arith)
    have pS₂ : bytesAt (nMemC D S sl s) S (16 * (16 * C)) = bytesAt s.mem S (256 * C) := by
      rw [show 16 * (16 * C) = 256 * C by omega_arith]
      exact bytesAt_frame fr₂ (dD₂ _ (h.sD.sub_left (Region.sub_prefix (by omega_arith)))) (by omega_arith)
    have pD₂ : bytesAt (nMemC D S sl s) (D + BitVec.ofNat 64 (16 * (16 * C))) (16 * (16 * G - 16 * C)) =
        bytesAt s.mem (S + BitVec.ofNat 64 (256 * C)) (sl - 256 * C) ++
          bytesAt s.mem (D + BitVec.ofNat 64 sl) (256 * G - sl) := by
      rw [show (nMemC D S sl s) = writeBytes s.mem (D + BitVec.ofNat 64 (256 * C))
          (bytesAt s.mem (S + BitVec.ofNat 64 (256 * C)) (sl - 256 * C)) by simp only [nMemC, cOf, hCd],
        show 16 * (16 * C) = 256 * C by omega_arith,
        show 16 * (16 * G - 16 * C) = (bytesAt s.mem (S + BitVec.ofNat 64 (256 * C)) (sl - 256 * C)).length +
          (256 * G - sl) by rw [length_bytesAt]; omega_arith,
        bytesAt_writeBytes_from _ _ _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, add_ofNat_assoc,
        show 256 * C + (sl - 256 * C) = sl by omega_arith]
    have pt₁ : (splitPt s.mem D S n sl).take (16 * (16 * G)) = bytesAt s.mem S (256 * C) ++
        (bytesAt s.mem (S + BitVec.ofNat 64 (256 * C)) (sl - 256 * C) ++
          bytesAt s.mem (D + BitVec.ofNat 64 sl) (256 * G - sl)) := by
      simp only [splitPt]
      rw [List.take_append, List.take_of_length_le (by rw [length_bytesAt]; omega_arith), length_bytesAt,
        bytesAt_drop' _ _ hsl, bytesAt_take' _ _ (by omega_arith), ← List.append_assoc, ← bytesAt_add,
        Nat.add_sub_cancel' hc, e256]
    rw [b5, b4, pS₂, pD₂, pt₁, hcb₂]
    show xorKs (ciphOf (nMemC D S sl s) Ctx R) _ 0 _ = _
    rw [hc₂]
  · -- The counter block.
    have c4 := hP.ctr
    simp only [Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.cb, hN.rdx, hN.mem] at c4
    have k5 : blockAt s₅.mem (cbA W) = blockAt s₄.mem (cbA W) := blockAt_frame f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ _
      rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    rw [k5, c4, hcb₂]
  · -- `Y`.
    have y4 := hP.y
    simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
      Gcm.X86_64.Stitch.op, hN.rcx, hN.rdi, hN.r10, hN.mem] at y4
    have k5 : blockAt s₅.mem (yA W) = blockAt s₄.mem (yA W) := blockAt_frame f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ _
      rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    have b5 : blocksAt s₅.mem D (16 * G) = blocksAt s₄.mem D (16 * G) := by
      rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq,
        bytesAt_frame f₅ (dW200 _ (h.data.ok.w.sub_left dG)) (by omega_arith)]
    rw [k5, y4, show blockAt (nMemC D S sl s) (Ctx + 240) = ctxH s.mem Ctx from hH₂, hy₂, b5]


/-- The texts `nTest` takes, from a state that `prefix` could start from but
for `rax`, `rcx` and the flags: the bytes of `src` after its last whole group
copied, and the first `256 ⌊n / 256⌋` bytes of the plaintext encrypted in one
pass. -/
theorem nPath_ok {c : Prog isa} (hE : EncNOk np hpn c) (hC : 1 ≤ sl / 256 ∧ sl / 256 < n / 256) {t : State}
    (g : ∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) (tm : t.mem = s.mem) (trd : t.rd = s.rd)
    (twr : t.wr = s.wr) :
    WP isa (.seq (.block SealSplit.nCopyArgs) (.seq SealGather.copy (.seq (.block SealSplit.nArgs)
      (.seq c (.block SealSplit.nRest))))) t
      (fun s' => PPostG Ctx W SP D S R n sl (16 * (n / 256)) s s') :=
  WP.seq (WP.mono (nA_ok h g tm trd twr) fun _ hA => WP.seq (WP.mono (nB_ok h hA) fun _ hB =>
    WP.seq (WP.mono (nC_ok h hB) fun _ hN => WP.seq (WP.mono (nD_ok h hE hC hN) fun _ hP => nE_ok h hC hN hP))))

end

/-- `PP` for a state that differs from one only in registers that `Env` does
not name. -/
theorem PP.of_eq {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s t : State} (h : PP M Ctx W SP D S R n sl s)
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP t) (tm : t.mem = s.mem) (trd : t.rd = s.rd) (twr : t.wr = s.wr) :
    PP M Ctx W SP D S R n sl t :=
  { h with env := he, rounds := by rw [tm]; exact h.rounds, dat := by rw [tm]; exact h.dat,
           len := by rw [tm]; exact h.len, src := by rw [tm]; exact h.src, slen := by rw [tm]; exact h.slen,
           data := (h.data.of_eq trd twr), srcCov := by rw [trd, twr]; exact h.srcCov,
           ext := h.ext.of_eq trd twr tm }

/-- `PPostG` from a state with the same memory and permissions. -/
theorem PPostG.of_eq {Ctx W SP D S : Addr} {R n sl q : Nat} {s t s' : State}
    (h : PPostG Ctx W SP D S R n sl q t s') (tm : t.mem = s.mem) (trd : t.rd = s.rd) (twr : t.wr = s.wr) :
    PPostG Ctx W SP D S R n sl q s s' := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m⟩ := h
  rw [tm] at e f g i j
  exact ⟨a, b.trans trd, c.trans twr, d, e, f, g, i, j, k, l, m⟩

/-- `prefixN` meets `PreOk`: in one pass for the texts `nTest` takes, by
`prefix` for the others. -/
theorem prefixNOk {c : Prog isa} (hE : EncNOk np hpn c) (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreOk (CtxMode.preparedN np hpn) (SealSplit.prefixN T.fn c)
    fun n sl => if 1 ≤ sl / 256 ∧ sl / 256 < n / 256 then 16 * (n / 256) else sl / 16 := by
  intro Ctx W SP D S R n sl s h
  unfold SealSplit.prefixN
  refine WP.seq (WP.mono (nTest_ok (n := n) (sl := sl) h.data.ok.lt h.sl_le h.env h.slen h.len)
    fun t ⟨cf, g, tm, trd, twr⟩ => ?_)
  refine WP.ite (decide (1 ≤ sl / 256 ∧ sl / 256 < n / 256)) (by simp only [eval, cf]) (fun hc => ?_) (fun hc => ?_)
  · have hc' := of_decide_eq_true hc
    simp only [hc', and_self, ↓reduceIte]
    exact nPath_ok h hE hc' g tm trd twr
  · have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) trd twr
    have hc' := of_decide_eq_false hc
    simp only [hc', ↓reduceIte]
    exact WP.mono (prefixOk T (h.of_eq he tm trd twr)) fun _ P => P.of_eq tm trd twr

end VG.Proof.AesGcm.X86_64.Split
