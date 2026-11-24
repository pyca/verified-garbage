module

public import VerifiedGarbage.Impl.AesXts.X86AesNi
public import VerifiedGarbage.Proof.AesCbc.X86.CT
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.AesXts.X86.Verified
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
public import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.AesXts.X86AesNi
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesXts.X86.Verified
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

-- separate module: the loops' and memory proofs cost more to check than their imports.

/-!
# XTS-AES with AES-NI on x86 (32-bit): one pass over the data

`Impl.AesXts.X86AesNi.encrypt` and `decrypt` meet the contract of the
whole-block functions (`modeX86 (xtsMode enc)`, `encrypt_ok`, `decrypt_ok`),
in constant time (`encrypt_ct`, `decrypt_ct`, by the taint analysis that
follows the SSE instructions, of the whole function), between the prologue
and the epilogue they share with them and with AES-CBC (`ends_wp`).

After `c` blocks (`Inv`), the first `c` blocks are XTS of the original ones
(`outB`), `xmm7` holds the tweak of block `c`, and the scratch buffer holds
the constant of the carries and, for decryption, the round keys through
`aesimc` (`DKeys`). A group of blocks (`group_ok`), six or one: each block is
loaded with its tweak XORed in, and the tweak stored (`fill_ok`: block `i`'s
is the tweak times `αⁱ`, by `lanes_ok` and, for the last two of six,
`last2_ok`), the rounds (`rounds_ok`, from `aes_ok` and `aesDec_ok` of
`vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`), and each
tweak XORed in again and the block stored (`xorOut_ok`), and the tweak after
them (`next_ok`); these are stated for any addresses of the blocks and the
tweaks that are apart. A block in an SSE register is its 16 bytes, the first
least significant (`bx`, `Proof/AesXts/X86/Steps.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.AesNi

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesXts.X86AesNi
open VG.Impl.CmacAes.X86 (argOp at_ setup restore)
open VG.Proof.CmacAes.X86 (wp_arg add0 arg_ofNat ea_at')
open VG.Proof.AesOcb.X86 (exec_bin exec_movd exec_pshufd)
open VG.Proof.AesCbc.X86
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86.Decrypt (x_ldm x_addi x_subi x_cmpi x_test x_load x_store)
open VG.Proof.Aes.X86.AesNi (Keys DKeys XFrame aes_ok aesDec_ok st st_ext getD_st getD_ofFn st_toList ea_at imcKeys_ok
  dKeys_of_imc ImcSetup ImcDone ImcInv byte_roundKey)
open VG.Proof.Aes.X86 (in_rd part_sub_reg addr_add reg32)
open VG.Proof.CmacAes.X86 (st_getD niKeys)
open VG.Impl.Aes.X86.AesNi (regs6)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesXts.X86 (exec_shift Signs signC carryOf dbl_carry bx alphaX bx_alphaX bx_xor bytesAt_bx)
open VG.Spec.Aes (bytesAt)

/-! ## The pieces of a group, for any addresses of its blocks and tweaks -/

theorem repeat_succ' {α : Type} (f : α → α) (a : α) : ∀ n, Nat.repeat f (n + 1) a = Nat.repeat f n (f a)
  | 0 => rfl
  | n + 1 => congrArg f (repeat_succ' f a n)

/-- The bytes of a tweak in a register times `αⁿ`. -/
theorem bx_repeat (x : BitVec 128) : ∀ n, bx (Nat.repeat alphaX n x) = Spec.Xts.next (bx x) n
  | 0 => rfl
  | n + 1 => by
    show bx (alphaX (Nat.repeat alphaX n x)) = Spec.Xts.mulAlpha (Spec.Xts.next (bx x) n)
    rw [bx_alphaX, bx_repeat x n]

/-- `signs`: the constant, and the top bits of the tweak's quadwords. -/
theorem signs_run (s : State) {P : Addr} (hP : addr (s.gpr .edx) cO = P) (hin : InRegions (s.rd ++ s.wr) P 16) :
    ∃ s', runBlock isa signs s = some s' ∧ s'.xmm .xmm4 = s.mem.readW P 128 ∧
      Signs (s.xmm .xmm7) 0 (s'.xmm .xmm5) ∧ s'.xmm .xmm7 = s.xmm .xmm7 ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [signs, runBlock_cons, runStep_some, runBlock_nil, exec, exec_shift, exec_pshufd, State.load128, ea_at',
      hP, hin, ↓reduceIte, Option.map_some]
    rfl, ?_, ?_, ?_, by rfl, by rfl, by rfl, by rfl⟩
  · simp only [xmm_setXmm_self, reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne]
  · simp only [xmm_setXmm_self, reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne]
    exact Signs.start _
  · simp only [reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne]

/-- `lane`: a block loaded with its tweak XORed in, and the tweak stored. -/
theorem lane_run {dA tA : Nat → Addr} (b : XReg) (hb : ¬ XReg.xmm7 = b) (j : Nat) (s : State)
    (hd : addr (s.gpr .esi) (16 * j) = dA j) (ht : addr (s.gpr .edx) (twO + 16 * j) = tA j)
    (hind : InRegions (s.rd ++ s.wr) (dA j) 16) (hint : InRegions s.wr (tA j) 16) :
    ∃ s', runBlock isa (lane b j) s = some s' ∧ s'.xmm b = s.mem.readW (dA j) 128 ^^^ s.xmm .xmm7 ∧
      (∀ r, ¬ r = b → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem.writeW (tA j) (s.xmm .xmm7) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [lane, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, State.load128, State.store128, ea_at',
      gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, hd, ht, hind, hint, ↓reduceIte, Option.map_some]
    rfl, ?_, fun r h => ?_, by rfl, ?_, by rfl, by rfl⟩
  · show ((s.setXmm b _).setXmm b _).xmm b = _
    simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ hb]; rfl
  · show ((s.setXmm b _).setXmm b _).xmm r = _
    simp only [xmm_setXmm_of_ne _ _ h]
  · simp only [xmm_setXmm_of_ne _ _ hb]

/-- `step`: the tweak times `α`, with the carries ahead. -/
theorem step_run {x : BitVec 128} {k : Nat} (hk : k < 8) (s : State) (h5 : Signs x k (s.xmm .xmm5))
    (h4 : s.xmm .xmm4 = signC) (h7 : s.xmm .xmm7 = Nat.repeat alphaX k x) :
    ∃ s', runBlock isa step s = some s' ∧ Signs x (k + 1) (s'.xmm .xmm5) ∧
      s'.xmm .xmm7 = Nat.repeat alphaX (k + 1) x ∧
      (∀ r, ¬ r = .xmm5 → ¬ r = .xmm6 → ¬ r = .xmm7 → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [step, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, exec_shift]
    rfl, ?_, ?_, fun r h₁ h₂ h₃ => ?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm]⟩
  · simp only [xmm_setXmm_self, reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne]
    exact h5.step
  · simp only [xmm_setXmm_self, reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne, eval_movdqa, h4, h7]
    rw [h5.red (by omega_arith)]
    exact dbl_carry x hk
  · simp only [xmm_setXmm_of_ne _ _ h₁, xmm_setXmm_of_ne _ _ h₂, xmm_setXmm_of_ne _ _ h₃]

/-- What the blocks `j … j + n - 1` of a group leave in memory, the tweaks of
the block `j` on being `x` times `αʲ` on: the tweaks, at `tA`, in `T`. -/
structure Tweaks (tA : Nat → Addr) (T : Region) (x : BitVec 128) (j n : Nat) (m m' : Mem) : Prop where
  frame : Frame [T] m m'
  tw : ∀ i < n, m'.readW (tA (j + i)) 128 = Nat.repeat alphaX (j + i) x
  keep : ∀ a, (∀ i < n, Mem.Sep a 16 (tA (j + i)) 16) → m'.readW a 128 = m.readW a 128

/-- `lanes`: the blocks from block `j` on, each with its tweak XORed in. -/
theorem lanes_ok {dA tA : Nat → Addr} {T : Region} {x : BitVec 128} : ∀ (rs : List XReg) (j : Nat) (s : State),
    j + rs.length < 8 → rs.Nodup → (∀ r ∈ rs, ¬ r = .xmm4 ∧ ¬ r = .xmm5 ∧ ¬ r = .xmm6 ∧ ¬ r = .xmm7) →
    Signs x j (s.xmm .xmm5) → s.xmm .xmm4 = signC → s.xmm .xmm7 = Nat.repeat alphaX j x →
    (∀ i < rs.length, addr (s.gpr .esi) (16 * (j + i)) = dA (j + i)) →
    (∀ i < rs.length, addr (s.gpr .edx) (twO + 16 * (j + i)) = tA (j + i)) →
    (∀ i < rs.length, InRegions (s.rd ++ s.wr) (dA (j + i)) 16) →
    (∀ i < rs.length, InRegions s.wr (tA (j + i)) 16) → (∀ i < rs.length, T.Contains (tA (j + i)) 16) →
    (∀ i < rs.length, ∀ i' < rs.length, i ≠ i' → Mem.Sep (tA (j + i)) 16 (tA (j + i')) 16) →
    (∀ i < rs.length, ∀ i' < rs.length, Mem.Sep (dA (j + i)) 16 (tA (j + i')) 16) →
    WP isa (.block (lanes rs j)) s fun s' =>
      (∀ i (h : i < rs.length), s'.xmm rs[i] = s.mem.readW (dA (j + i)) 128 ^^^ Nat.repeat alphaX (j + i) x) ∧
      Signs x (j + rs.length) (s'.xmm .xmm5) ∧ s'.xmm .xmm4 = signC ∧
      s'.xmm .xmm7 = Nat.repeat alphaX (j + rs.length) x ∧
      (∀ r, ¬ r = .xmm5 → ¬ r = .xmm6 → ¬ r = .xmm7 → r ∉ rs → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Tweaks tA T x j rs.length s.mem s'.mem
  | [], _, s, _, _, _, h5, h4, h7, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), h5, h4, h7, fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩⟩
  | b :: bs, j, s, hj, hnd, hr, h5, h4, h7, hd, ht, hind, hint, hT, hsep, hdt => by
    obtain ⟨b4, b5, b6, b7⟩ := hr b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have e (i : Nat) : j + 1 + i = j + (i + 1) := by omega_using []
    have l0 : 0 < (b :: bs).length := Nat.succ_pos _
    have hj' : j + (bs.length + 1) < 8 := hj
    obtain ⟨s₁, run₁, hv₁, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ := lane_run (dA := dA) (tA := tA) b (fun h => b7 h.symm) j s
      (hd 0 l0) (ht 0 l0) (hind 0 l0) (hint 0 l0)
    obtain ⟨s₂, run₂, h5₂, h7₂, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ := step_run (x := x) (k := j) (by omega_using [hj']) s₁
      (by rw [hx₁ _ (fun h => b5 h.symm)]; exact h5) (by rw [hx₁ _ (fun h => b4 h.symm)]; exact h4)
      (by rw [hx₁ _ (fun h => b7 h.symm)]; exact h7)
    rw [lanes, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    rw [WP.block_append_iff]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    have hg : s₂.gpr = s.gpr := hg₂.trans hg₁
    have hrd : s₂.rd = s.rd := hrd₂.trans hrd₁
    have hwr : s₂.wr = s.wr := hwr₂.trans hwr₁
    have hm : s₂.mem = s.mem.writeW (tA j) (Nat.repeat alphaX j x) := by rw [hm₂, hm₁, h7]
    refine WP.mono (lanes_ok (dA := dA) (tA := tA) (T := T) (x := x) bs (j + 1) s₂ (by omega_using [hj'])
      (List.nodup_cons.mp hnd).2 (fun r h => hr r (List.mem_cons_of_mem _ h)) h5₂
      (by rw [hx₂ _ (by decide) (by decide) (by decide), hx₁ _ (fun h => b4 h.symm)]; exact h4) h7₂
      (fun i hi => by rw [hg, e]; exact hd (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [hg, e]; exact ht (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [hrd, hwr, e]; exact hind (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [hwr, e]; exact hint (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [e]; exact hT (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi i' hi' hne => by
        rw [e, e]
        exact hsep (i + 1) (Nat.succ_lt_succ hi) (i' + 1) (Nat.succ_lt_succ hi') (by omega_using [hne]))
      (fun i hi i' hi' => by
        rw [e, e]; exact hdt (i + 1) (Nat.succ_lt_succ hi) (i' + 1) (Nat.succ_lt_succ hi')))
      fun s' ⟨hv', h5', h4', h7', hx', hg', hrd', hwr', hT'⟩ => ?_
    have el : j + 1 + bs.length = j + (b :: bs).length := e _
    rw [el] at h5' h7'
    refine ⟨fun i hi => ?_, h5', h4', h7', fun r h₁ h₂ h₃ h₄ => ?_, hg'.trans hg, hrd'.trans hrd, hwr'.trans hwr,
      ⟨?_, fun i hi => ?_, fun a ha => ?_⟩⟩
    · cases i with
      | zero =>
        rw [List.getElem_cons_zero, hx' b b5 b6 b7 hbs, hx₂ b b5 b6 b7, hv₁, h7, Nat.add_zero]
      | succ i =>
        obtain hi' : i < bs.length := Nat.lt_of_succ_lt_succ hi
        rw [List.getElem_cons_succ, hv' i hi', hm, e, Mem.readW_writeW_sep (hdt (i + 1) hi 0 l0) (by decide)]
    · simp only [List.mem_cons, not_or] at h₄
      rw [hx' r h₁ h₂ h₃ h₄.2, hx₂ r h₁ h₂ h₃, hx₁ r h₄.1]
    · have f := hT'.frame
      rw [hm] at f
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hT 0 l0)).trans f
    · cases i with
      | zero =>
        rw [hT'.keep _ fun i hi => by
          rw [e]; exact hsep 0 l0 (i + 1) (Nat.succ_lt_succ hi) (by omega_using []), hm]
        exact Mem.readW_writeW_self _ _ 16 _ (by decide)
      | succ i =>
        obtain h := hT'.tw i (Nat.lt_of_succ_lt_succ hi)
        rwa [e] at h
    · rw [hT'.keep a fun i hi => by rw [e]; exact ha (i + 1) (Nat.succ_lt_succ hi), hm]
      exact Mem.readW_writeW_sep (ha 0 l0) (by decide)

/-- `carries2`: the carries of the tweaks `x` times `αᵏ` and `αᵏ⁺¹`. -/
theorem carries2_run {x : BitVec 128} {k : Nat} (hk : k + 1 < 8) (s : State) (h5 : Signs x k (s.xmm .xmm5))
    (h4 : s.xmm .xmm4 = signC) {P : Addr} (hP : addr (s.gpr .edx) rO = P) (hin : InRegions s.wr P 16) :
    ∃ s', runBlock isa carries2 s = some s' ∧ s'.xmm .xmm5 = carryOf x k ∧
      (∀ r, ¬ r = .xmm5 → ¬ r = .xmm6 → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW P (carryOf x (k + 1)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [carries2, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, exec_shift, State.store128, ea_at',
      gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, hP, hin, ↓reduceIte]
    rfl, ?_, fun r h₁ h₂ => ?_, by simp only [gpr_setXmm], ?_,
    by simp only [rd_setXmm], by simp only [wr_setXmm]⟩
  · simp only [xmm_setXmm_self, reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne, h4]
    exact h5.red (by omega_using [hk])
  · simp only [xmm_setXmm_of_ne _ _ h₁, xmm_setXmm_of_ne _ _ h₂]
  · rw [mem_setXmm, mem_setXmm]
    simp only [xmm_setXmm_self, reduceCtorEq, not_false_eq_true, xmm_setXmm_of_ne, eval_movdqa, h4]
    rw [h5.step.red (by omega_using [hk])]

/-- `dblWith`: the tweak times `α`, with its carries in `r`. -/
theorem dblWith_run {x : BitVec 128} {k : Nat} (hk : k < 8) (r : XReg) (hr : ¬ r = .xmm7) (s : State)
    (h7 : s.xmm .xmm7 = Nat.repeat alphaX k x) (hc : s.xmm r = carryOf x k) :
    ∃ s', runBlock isa (dblWith r) s = some s' ∧ s'.xmm .xmm7 = Nat.repeat alphaX (k + 1) x ∧
      (∀ q, ¬ q = .xmm7 → s'.xmm q = s.xmm q) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [dblWith, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin]
    rfl, ?_, fun q h => ?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm]⟩
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ hr, h7, hc]
    exact dbl_carry x hk
  · simp only [xmm_setXmm_of_ne _ _ h]

/-- `last2`: the last two blocks of six, and the carries of the tweak after
them kept at `P`. -/
theorem last2_ok {dA tA : Nat → Addr} {T : Region} {P : Addr} {x : BitVec 128} (s : State)
    (h5 : Signs x 4 (s.xmm .xmm5)) (h4 : s.xmm .xmm4 = signC) (h7 : s.xmm .xmm7 = Nat.repeat alphaX 4 x)
    (hd : ∀ i < 6, addr (s.gpr .esi) (16 * i) = dA i) (ht : ∀ i < 6, addr (s.gpr .edx) (twO + 16 * i) = tA i)
    (hP : addr (s.gpr .edx) rO = P) (hind : ∀ i < 6, InRegions (s.rd ++ s.wr) (dA i) 16)
    (hint : ∀ i < 6, InRegions s.wr (tA i) 16) (hinP : InRegions s.wr P 16)
    (hT : ∀ i < 6, T.Contains (tA i) 16) (hTP : T.Contains P 16)
    (hsep : ∀ i < 6, ∀ i' < 6, i ≠ i' → Mem.Sep (tA i) 16 (tA i') 16)
    (hPt : ∀ i < 6, Mem.Sep P 16 (tA i) 16)
    (hdt : ∀ i < 6, ∀ i' < 6, Mem.Sep (dA i) 16 (tA i') 16) (hdP : ∀ i < 6, Mem.Sep (dA i) 16 P 16) :
    WP isa (.block last2) s fun s' =>
      s'.xmm .xmm4 = s.mem.readW (dA 4) 128 ^^^ Nat.repeat alphaX 4 x ∧
      s'.xmm .xmm5 = s.mem.readW (dA 5) 128 ^^^ Nat.repeat alphaX 5 x ∧
      s'.xmm .xmm7 = Nat.repeat alphaX 5 x ∧ s'.mem.readW P 128 = carryOf x 5 ∧
      (∀ r ∈ regs4, s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [T] s.mem s'.mem ∧
      s'.mem.readW (tA 4) 128 = Nat.repeat alphaX 4 x ∧ s'.mem.readW (tA 5) 128 = Nat.repeat alphaX 5 x ∧
      ∀ a, Mem.Sep a 16 P 16 → (∀ i < 6, 4 ≤ i → Mem.Sep a 16 (tA i) 16) →
        s'.mem.readW a 128 = s.mem.readW a 128 := by
  obtain ⟨s₁, run₁, c₁, x₁, g₁, m₁, rd₁, wr₁⟩ := carries2_run (x := x) (k := 4) (by decide) s h5 h4 hP hinP
  obtain ⟨s₂, run₂, v₂, x₂, g₂, m₂, rd₂, wr₂⟩ := lane_run (dA := dA) (tA := tA) .xmm4 (by decide) 4 s₁
    (by rw [g₁]; exact hd 4 (by decide)) (by rw [g₁]; exact ht 4 (by decide))
    (by rw [rd₁, wr₁]; exact hind 4 (by decide)) (by rw [wr₁]; exact hint 4 (by decide))
  obtain h7₁ : s₁.xmm .xmm7 = Nat.repeat alphaX 4 x := by rw [x₁ _ (by decide) (by decide), h7]
  obtain ⟨s₃, run₃, h7₃, x₃, g₃, m₃, rd₃, wr₃⟩ := dblWith_run (x := x) (k := 4) (by decide) .xmm5 (by decide) s₂
    (by rw [x₂ _ (by decide)]; exact h7₁) (by rw [x₂ _ (by decide)]; exact c₁)
  obtain gs₃ : s₃.gpr = s.gpr := g₃.trans (g₂.trans g₁)
  obtain rs₃ : s₃.rd = s.rd := rd₃.trans (rd₂.trans rd₁)
  obtain ws₃ : s₃.wr = s.wr := wr₃.trans (wr₂.trans wr₁)
  obtain ⟨s₄, run₄, v₄, x₄, g₄, m₄, rd₄, wr₄⟩ := lane_run (dA := dA) (tA := tA) .xmm5 (by decide) 5 s₃
    (by rw [gs₃]; exact hd 5 (by decide)) (by rw [gs₃]; exact ht 5 (by decide))
    (by rw [rs₃, ws₃]; exact hind 5 (by decide)) (by rw [ws₃]; exact hint 5 (by decide))
  obtain hm₃ : s₃.mem = (s.mem.writeW P (carryOf x 5)).writeW (tA 4) (Nat.repeat alphaX 4 x) := by
    rw [m₃, m₂, h7₁, m₁]
  obtain hm₄ : s₄.mem = ((s.mem.writeW P (carryOf x 5)).writeW (tA 4) (Nat.repeat alphaX 4 x)).writeW (tA 5)
      (Nat.repeat alphaX 5 x) := by rw [m₄, h7₃, hm₃]
  rw [last2, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, g₄.trans gs₃, rd₄.trans rs₃, wr₄.trans ws₃, ?_, ?_, ?_, fun a h₁ h₂ => ?_⟩
  · rw [x₄ _ (by decide), x₃ _ (by decide), v₂, h7₁, m₁, Mem.readW_writeW_sep (hdP 4 (by decide)) (by decide)]
  · rw [v₄, h7₃, hm₃, Mem.readW_writeW_sep (hdt 5 (by decide) 4 (by decide)) (by decide),
      Mem.readW_writeW_sep (hdP 5 (by decide)) (by decide)]
  · rw [x₄ _ (by decide), h7₃]
  · rw [hm₄, Mem.readW_writeW_sep (hPt 5 (by decide)) (by decide),
      Mem.readW_writeW_sep (hPt 4 (by decide)) (by decide)]
    exact Mem.readW_writeW_self _ _ 16 _ (by decide)
  · obtain ⟨n4, n5, n6, n7⟩ : ¬ r = .xmm4 ∧ ¬ r = .xmm5 ∧ ¬ r = .xmm6 ∧ ¬ r = .xmm7 := by
      revert r; decide
    rw [x₄ r n5, x₃ r n7, x₂ r n4, x₁ r n5 n6]
  · rw [hm₄]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hTP).writeW (List.mem_singleton_self _) _
      (hT 4 (by decide))).writeW (List.mem_singleton_self _) _ (hT 5 (by decide))
  · rw [hm₄, Mem.readW_writeW_sep (hsep 4 (by decide) 5 (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self _ _ 16 _ (by decide)
  · rw [hm₄]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)
  · rw [hm₄, Mem.readW_writeW_sep (h₂ 5 (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (h₂ 4 (by decide) (by decide)) (by decide), Mem.readW_writeW_sep h₁ (by decide)]

/-- What a `fill` leaves for the blocks in the registers `rs`, the tweak of
the first being `x`: what `next`, after the blocks are stored, needs for the
tweak after them. -/
def Held (rs : List XReg) (P : Addr) (x : BitVec 128) (s : State) : Prop :=
  if rs.length = 6 then s.xmm .xmm7 = Nat.repeat alphaX 5 x ∧ s.mem.readW P 128 = carryOf x 5
  else s.xmm .xmm7 = Nat.repeat alphaX rs.length x

/-- `fill6` and `fill1`: each block with its tweak XORed in. -/
theorem fill_ok {dA tA : Nat → Addr} {T : Region} {P C : Addr} {fill : List Instr} {rs : List XReg}
    (hrs : (fill = fill6 ∧ rs = regs6) ∨ (fill = fill1 ∧ rs = [.xmm0])) (s : State)
    (hC : addr (s.gpr .edx) cO = C) (hinC : InRegions (s.rd ++ s.wr) C 16) (hcv : s.mem.readW C 128 = signC)
    (hd : ∀ i < rs.length, addr (s.gpr .esi) (16 * i) = dA i) (ht : ∀ i < 6, addr (s.gpr .edx) (twO + 16 * i) = tA i)
    (hP : addr (s.gpr .edx) rO = P) (hind : ∀ i < rs.length, InRegions (s.rd ++ s.wr) (dA i) 16)
    (hint : ∀ i < 6, InRegions s.wr (tA i) 16) (hinP : InRegions s.wr P 16)
    (hT : ∀ i < 6, T.Contains (tA i) 16) (hTP : T.Contains P 16)
    (hsep : ∀ i < 6, ∀ i' < 6, i ≠ i' → Mem.Sep (tA i) 16 (tA i') 16)
    (hPt : ∀ i < 6, Mem.Sep P 16 (tA i) 16)
    (hdt : ∀ i < rs.length, ∀ i' < 6, Mem.Sep (dA i) 16 (tA i') 16)
    (hdP : ∀ i < rs.length, Mem.Sep (dA i) 16 P 16) :
    WP isa (.block fill) s fun s' =>
      (∀ i (h : i < rs.length), s'.xmm rs[i] = s.mem.readW (dA i) 128 ^^^ Nat.repeat alphaX i (s.xmm .xmm7)) ∧
      Held rs P (s.xmm .xmm7) s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [T] s.mem s'.mem ∧
      (∀ i < rs.length, s'.mem.readW (tA i) 128 = Nat.repeat alphaX i (s.xmm .xmm7)) := by
  obtain ⟨s₁, run₁, x4₁, x5₁, x7₁, g₁, m₁, rd₁, wr₁⟩ := signs_run s hC hinC
  rw [hcv] at x4₁
  obtain hl : ∀ (qs : List XReg), qs.length ≤ rs.length → qs.length ≤ 6 → qs.Nodup →
      (∀ r ∈ qs, ¬ r = .xmm4 ∧ ¬ r = .xmm5 ∧ ¬ r = .xmm6 ∧ ¬ r = .xmm7) → _ := fun qs hq hq6 hnd hr =>
    lanes_ok (dA := dA) (tA := tA) (T := T) (x := s.xmm .xmm7) qs 0 s₁ (by omega_using [hq6]) hnd hr x5₁ x4₁ x7₁
      (fun i hi => by rw [Nat.zero_add, g₁]; exact hd i (by omega_using [hi, hq]))
      (fun i hi => by rw [Nat.zero_add, g₁]; exact ht i (by omega_using [hi, hq6]))
      (fun i hi => by rw [Nat.zero_add, rd₁, wr₁]; exact hind i (by omega_using [hi, hq]))
      (fun i hi => by rw [Nat.zero_add, wr₁]; exact hint i (by omega_using [hi, hq6]))
      (fun i hi => by rw [Nat.zero_add]; exact hT i (by omega_using [hi, hq6]))
      (fun i hi i' hi' hne => by
        rw [Nat.zero_add, Nat.zero_add]; exact hsep i (by omega_using [hi, hq6]) i' (by omega_using [hi', hq6]) hne)
      (fun i hi i' hi' => by
        rw [Nat.zero_add, Nat.zero_add]; exact hdt i (by omega_using [hi, hq]) i' (by omega_using [hi', hq6]))
  rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [fill6, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    rw [WP.block_append_iff]
    refine WP.mono (hl regs4 (by decide) (by decide) (by decide) (by decide))
      fun s₂ ⟨hv₂, h5₂, h4₂, h7₂, _, g₂, rd₂, wr₂, hT₂⟩ => ?_
    simp only [Nat.zero_add] at hv₂ h5₂ h7₂
    obtain t₂ := hT₂.tw
    obtain k₂ := hT₂.keep
    simp only [Nat.zero_add] at t₂ k₂
    obtain gs : s₂.gpr = s.gpr := g₂.trans g₁
    obtain rs₂ : s₂.rd = s.rd := rd₂.trans rd₁
    obtain ws₂ : s₂.wr = s.wr := wr₂.trans wr₁
    refine WP.mono (last2_ok (dA := dA) (tA := tA) (T := T) (P := P) (x := s.xmm .xmm7) s₂ h5₂ h4₂ h7₂
      (fun i hi => by rw [gs]; exact hd i hi) (fun i hi => by rw [gs]; exact ht i hi) (by rw [gs]; exact hP)
      (fun i hi => by rw [rs₂, ws₂]; exact hind i hi) (fun i hi => by rw [ws₂]; exact hint i hi)
      (by rw [ws₂]; exact hinP) hT hTP hsep hPt hdt hdP)
      fun s₃ ⟨v4, v5, v7, vP, hx₃, g₃, rd₃, wr₃, f₃, t4, t5, k₃⟩ => ?_
    obtain kd : ∀ i < 6, s₂.mem.readW (dA i) 128 = s.mem.readW (dA i) 128 := fun i hi => by
      rw [k₂ _ fun i' hi' => hdt i hi i' (Nat.lt_of_lt_of_le hi' (by decide)), m₁]
    refine ⟨fun i hi => ?_, ?_, g₃.trans gs, rd₃.trans rs₂, wr₃.trans ws₂, ?_, fun i hi => ?_⟩
    · obtain h | rfl | rfl : i < 4 ∨ i = 4 ∨ i = 5 := by
        have : i < 6 := hi
        omega_using [this]
      · obtain e : regs6[i] = regs4[i]'h := by
          have : ∀ i (h : i < 4), regs6[i]'(Nat.lt_of_lt_of_le h (by decide)) = regs4[i]'h := by decide
          exact this i h
        rw [e, hx₃ (regs4[i]'h) (List.getElem_mem h), hv₂ i h, m₁]
      · exact v4.trans (by rw [kd 4 (by decide)])
      · exact v5.trans (by rw [kd 5 (by decide)])
    · exact (ite_eq_left (by decide)).mpr ⟨v7, vP⟩
    · rw [← m₁]; exact hT₂.frame.trans f₃
    · obtain h | rfl | rfl : i < 4 ∨ i = 4 ∨ i = 5 := by
        have : i < 6 := hi
        omega_using [this]
      · rw [k₃ _ (fun y h₁ h₂ => hPt i (by omega_using [h]) y h₂ h₁)
          fun i' hi' h' => hsep i (by omega_using [h]) i' hi' (by omega_using [h, h'])]
        exact t₂ i h
      · exact t4
      · exact t5
  · rw [fill1, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    refine WP.mono (hl [.xmm0] (by decide) (by decide) (by decide) (by decide))
      fun s₂ ⟨hv₂, _, _, h7₂, _, g₂, rd₂, wr₂, hT₂⟩ => ?_
    obtain t₂ := hT₂.tw
    simp only [Nat.zero_add] at hv₂ t₂
    refine ⟨fun i hi => by rw [hv₂ i hi, m₁], ?_, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_, t₂⟩
    · exact (ite_eq_right (by decide)).mpr h7₂
    · rw [← m₁]; exact hT₂.frame

/-- `next6`, and nothing after one block: the tweak after the blocks. -/
theorem next_ok {P : Addr} {x : BitVec 128} {next : List Instr} {rs : List XReg}
    (hrs : (next = next6 ∧ rs = regs6) ∨ (next = [] ∧ rs = [.xmm0])) (s : State)
    (hP : addr (s.gpr .edx) rO = P) (hin : InRegions (s.rd ++ s.wr) P 16) (h : Held rs P x s) :
    WP isa (.block next) s fun s' => s'.xmm .xmm7 = Nat.repeat alphaX rs.length x ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h7, hc⟩ := (ite_eq_left (by decide)).mp h
    rw [next6]
    refine x_load (B := s.gpr .edx) rfl (by rw [hP]; exact hin) ?_
    obtain ⟨s', run, v, -, g, m, rd, wr⟩ := dblWith_run (x := x) (k := 5) (by decide) .xmm6 (by decide)
      (s.setXmm .xmm6 (s.mem.readW (addr (s.gpr .edx) rO) 128)) (by rw [xmm_setXmm_of_ne _ _ (by decide)]; exact h7)
      (by rw [xmm_setXmm_self, hP]; exact hc)
    exact WP.of_runBlock ⟨s', run, v, g, m, rd, wr⟩
  · exact WP.block_nil ⟨(ite_eq_right (by decide)).mp h, rfl, rfl, rfl, rfl⟩

/-- A block register with its tweak XORed in, stored to its block. -/
theorem xorOut1_run {dA tA : Nat → Addr} (b : XReg) (hb : ¬ b = .xmm6) (j : Nat) (s : State)
    (hd : addr (s.gpr .esi) (16 * j) = dA j) (ht : addr (s.gpr .edx) (twO + 16 * j) = tA j)
    (hind : InRegions s.wr (dA j) 16) (hint : InRegions (s.rd ++ s.wr) (tA j) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm6 (at_ .edx (twO + 16 * j)), .xop (.bin .pxor b .xmm6),
        .movdquStore (at_ .esi (16 * j)) b] s = some s' ∧
      s'.mem = s.mem.writeW (dA j) (s.xmm b ^^^ s.mem.readW (tA j) 128) ∧
      (∀ r, ¬ r = .xmm6 → ¬ r = b → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, State.load128, State.store128, ea_at',
      gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, hd, ht, hind, hint, ↓reduceIte, Option.map_some]
    rfl, ?_, fun r h₁ h₂ => ?_, by rfl, by rfl, by rfl⟩
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ hb]; rfl
  · show ((s.setXmm .xmm6 _).setXmm b _).xmm r = _
    rw [xmm_setXmm_of_ne _ _ h₂, xmm_setXmm_of_ne _ _ h₁]

/-- `xorOut`: each block is its register with its tweak XORed in. -/
theorem xorOut_ok {dA tA : Nat → Addr} {D : Region} : ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup →
    .xmm6 ∉ rs → (∀ i < rs.length, addr (s.gpr .esi) (16 * (j + i)) = dA (j + i)) →
    (∀ i < rs.length, addr (s.gpr .edx) (twO + 16 * (j + i)) = tA (j + i)) →
    (∀ i < rs.length, InRegions s.wr (dA (j + i)) 16) →
    (∀ i < rs.length, InRegions (s.rd ++ s.wr) (tA (j + i)) 16) →
    (∀ i < rs.length, D.Contains (dA (j + i)) 16) →
    (∀ i < rs.length, ∀ i' < rs.length, Mem.Sep (tA (j + i)) 16 (dA (j + i')) 16) →
    (∀ i < rs.length, ∀ i' < rs.length, i ≠ i' → Mem.Sep (dA (j + i)) 16 (dA (j + i')) 16) →
    WP isa (.block (xorOut rs j)) s fun s' =>
      (∀ i (h : i < rs.length), s'.mem.readW (dA (j + i)) 128 = s.xmm rs[i] ^^^ s.mem.readW (tA (j + i)) 128) ∧
      (∀ r, ¬ r = .xmm6 → r ∉ rs → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [D] s.mem s'.mem ∧
      ∀ a, (∀ i < rs.length, Mem.Sep a 16 (dA (j + i)) 16) → s'.mem.readW a 128 = s.mem.readW a 128
  | [], _, s, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun _ _ => rfl⟩
  | b :: bs, j, s, hnd, h6, hd, ht, hind, hint, hD, htd, hdd => by
    have hb6 : ¬ b = .xmm6 := fun h => h6 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h6' : .xmm6 ∉ bs := fun h => h6 (List.mem_cons_of_mem _ h)
    have e (i : Nat) : j + 1 + i = j + (i + 1) := by omega_using []
    have l0 : 0 < (b :: bs).length := Nat.succ_pos _
    obtain ⟨s₁, run, hm, hx, hg, hrd, hwr⟩ := xorOut1_run (dA := dA) (tA := tA) b hb6 j s (hd 0 l0) (ht 0 l0)
      (hind 0 l0) (hint 0 l0)
    rw [xorOut, WP.block_append_iff]
    refine WP.of_runBlock ⟨s₁, run, ?_⟩
    refine WP.mono (xorOut_ok (dA := dA) (tA := tA) (D := D) bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 h6'
      (fun i hi => by rw [hg, e]; exact hd (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [hg, e]; exact ht (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [hwr, e]; exact hind (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [hrd, hwr, e]; exact hint (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => by rw [e]; exact hD (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi i' hi' => by rw [e, e]; exact htd (i + 1) (Nat.succ_lt_succ hi) (i' + 1) (Nat.succ_lt_succ hi'))
      (fun i hi i' hi' hne => by
        rw [e, e]
        exact hdd (i + 1) (Nat.succ_lt_succ hi) (i' + 1) (Nat.succ_lt_succ hi') (by omega_using [hne])))
      fun s' ⟨hv', hx', hg', hrd', hwr', hf', hk'⟩ => ?_
    refine ⟨fun i hi => ?_, fun r h₁ h₂ => ?_, hg'.trans hg, hrd'.trans hrd, hwr'.trans hwr, ?_, fun a ha => ?_⟩
    · cases i with
      | zero =>
        rw [List.getElem_cons_zero, Nat.add_zero, hk' _ fun i hi => by
          rw [e]; exact hdd 0 l0 (i + 1) (Nat.succ_lt_succ hi) (by omega_using []), hm]
        exact Mem.readW_writeW_self _ _ 16 _ (by decide)
      | succ i =>
        obtain hi' : i < bs.length := Nat.lt_of_succ_lt_succ hi
        rw [List.getElem_cons_succ, ← e, hv' i hi', hm, e,
          hx _ (fun h => h6' (h ▸ List.getElem_mem hi')) (fun h => hbs (h ▸ List.getElem_mem hi')),
          Mem.readW_writeW_sep (htd (i + 1) hi 0 l0) (by decide)]
    · simp only [List.mem_cons, not_or] at h₂
      rw [hx' r h₁ h₂.2, hx r h₁ h₂.1]
    · rw [hm] at hf'
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hD 0 l0)).trans hf'
    · rw [hk' a fun i hi => by rw [e]; exact ha (i + 1) (Nat.succ_lt_succ hi), hm]
      exact Mem.readW_writeW_sep (ha 0 l0) (by decide)

/-! ## Blocks as bytes -/

theorem bx_eq (x : BitVec 128) : bx x = (st x).toList := (st_toList x).symm

theorem ofFn_bx (u : BitVec 128) : (Vector.ofFn fun i : Fin 16 => (bx u).getD i.1 0) = st u := by
  apply st_ext
  intro i hi
  rw [getD_ofFn hi, getD_st _ hi, bx_eq, st_getD u hi]

/-- The rounds of a direction, on the bytes of a block register. -/
theorem bx_ciph {enc : Bool} {nr : Nat} {w : List Byte} {x u : BitVec 128}
    (h : st x = if enc then Spec.Aes.cipher nr w (st u) else Spec.Aes.invCipher nr w (st u)) :
    bx x = ciphOf enc nr w (bx u) := by
  cases enc
  · rw [bx_eq, h]
    exact congrArg (fun y => (Spec.Aes.invCipher nr w y).toList) (ofFn_bx u).symm
  · rw [bx_eq, h]
    exact congrArg (fun y => (Spec.Aes.cipher nr w y).toList) (ofFn_bx u).symm

theorem next_add (t : List Byte) (c : Nat) : ∀ n, Spec.Xts.next (Spec.Xts.next t c) n = Spec.Xts.next t (c + n)
  | 0 => rfl
  | n + 1 => congrArg Spec.Xts.mulAlpha (next_add t c n)

theorem getElem?_tweaks (t : List Byte) : ∀ (n j : Nat), j < n → (Spec.Xts.tweaks t n)[j]? = some (Spec.Xts.next t j)
  | n + 1, j, h => by
    rw [AesXts.tweaks_succ]
    by_cases hj : j < n
    · rw [List.getElem?_append_left (by rw [AesXts.length_tweaks]; exact hj)]
      exact getElem?_tweaks t n j hj
    · obtain rfl : j = n := by omega_using [h, hj]
      rw [List.getElem?_append_right (by rw [AesXts.length_tweaks]), AesXts.length_tweaks, Nat.sub_self]
      rfl

/-- Block `j` of XTS of whole blocks. -/
theorem getElem_crypt (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs : List (List Byte)) {j : Nat}
    (hj : j < xs.length) :
    (Spec.Xts.crypt ciph t xs)[j]'(by rw [AesXts.length_crypt]; exact hj) =
      Spec.Xts.block ciph (Spec.Xts.next t j) xs[j] := by
  simp only [Spec.Xts.crypt, List.getElem_zipWith]
  exact congrArg (fun y => Spec.Xts.block ciph y xs[j])
    ((List.getElem_eq_iff _).mpr (getElem?_tweaks t xs.length j hj))

/-! ## The invariant -/

section
variable (s₀ : State)

/-- The scratch buffer. -/
abbrev Sa : Addr := (S s₀).setWidth 64

/-- Where the tweak of block `i` of a group is kept. -/
abbrev tA (i : Nat) : Addr := Sa s₀ + BitVec.ofNat 64 (twO + 16 * i)

/-- The tweaks of a group, and the carries after them. -/
abbrev twR : Region := ⟨Sa s₀ + BitVec.ofNat 64 twO, 112⟩

/-- The cipher of a direction. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (wK s₀)

/-- Block `j` through XTS. -/
abbrev outB (enc : Bool) (j : Nat) : List Byte :=
  Spec.Xts.block (ciph s₀ enc) (Spec.Xts.next (iv0 s₀) j) (bytesAt s₀.mem (blk s₀ j) 16)

end

/-- After `c` blocks, with `esi` and `edi` at block `p`: the first `c` blocks
are XTS of the original ones, `xmm7` holds the tweak of block `c`, and the
scratch buffer holds the constant and, for decryption, the round keys
through `aesimc`. -/
structure Inv (enc : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : Keys (R s₀) (wK s₀) s
  dkeys : enc = false → DKeys (R s₀) (wK s₀) s
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)
  edx : s.gpr .edx = S s₀
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - p)
  ebp : s.gpr .ebp = Iv s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨Sa s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : ∀ j < N s₀, bytesAt s.mem (blk s₀ j) 16 =
    if j < c then outB s₀ enc j else bytesAt s₀.mem (blk s₀ j) 16
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = iv0 s₀
  x7 : bx (s.xmm .xmm7) = Spec.Xts.next (iv0 s₀) c
  cst : s.mem.readW (Sa s₀ + BitVec.ofNat 64 cO) 128 = signC

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem scrA {o : Nat} (ho : o < 2176) : addr (S s₀) o = Sa s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.scr_fit; omega_using [this, ho])

omit hp in
theorem tw_sub : Region.Sub (twR s₀) (scrR s₀) := Offset.sub_base _ (by decide)

/-- A part of the scratch buffer apart from a group's tweaks, which the group leaves. -/
theorem scr_keep {m m' : Mem} (hf : Frame [twR s₀, dataR s₀] m m') {o : Nat} (ho : o + 16 ≤ 2176)
    (ho' : o + 16 ≤ 256 ∨ 368 ≤ o) :
    m'.readW (Sa s₀ + BitVec.ofNat 64 o) 128 = m.readW (Sa s₀ + BitVec.ofNat 64 o) 128 :=
  hf.readW (r := ⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (e := 256) (by omega_using [ho']) (by omega_using [ho]) (by decide)
    · exact (hp.data_scr.sub_right (Offset.sub_base _ ho)).symm) (by decide)

/-- A part of the key schedule, which a group leaves. -/
theorem sch_keep {m m' : Mem} (hf : Frame [twR s₀, dataR s₀] m m') {o : Nat} (ho : o + 16 ≤ 240) :
    m'.readW (addr (W s₀) o) 128 = m.readW (addr (W s₀) o) 128 :=
  hf.readW (r := ⟨addr (W s₀) o, 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.sch_scr.sub_left (part_sub_reg hp.sch_fit ho)).sub_right tw_sub
    · exact hp.sch_data.sub_left (part_sub_reg hp.sch_fit ho)) (by decide)

/-- The round keys are kept by a group. -/
theorem keys_stable {s t : State} (h : Keys (R s₀) (wK s₀) s) (ha : s.gpr .eax = W s₀)
    (hga : t.gpr .eax = s.gpr .eax) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hf : Frame [twR s₀, dataR s₀] s.mem t.mem) : Keys (R s₀) (wK s₀) t := by
  obtain hnr : R s₀ ≤ 14 := h.le
  obtain hea : ∀ o, t.ea (Impl.Aes.X86.AesNi.at_ .eax o) = s.ea (Impl.Aes.X86.AesNi.at_ .eax o) := fun o => by
    rw [ea_at, ea_at, hga]
  refine ⟨hnr, fun j hj => by rw [hea, hr, hw]; exact h.keys j hj, fun j hj => ?_⟩
  rw [hea, ea_at, ha, sch_keep hp hf (by omega_using [hnr, hj]), ← ha, ← ea_at]
  exact h.bytes j hj

/-- The round keys through `aesimc` are kept by a group. -/
theorem dkeys_stable {s t : State} (h : DKeys (R s₀) (wK s₀) s) (ha : s.gpr .eax = W s₀)
    (hd : s.gpr .edx = S s₀) (hga : t.gpr .eax = s.gpr .eax) (hgd : t.gpr .edx = s.gpr .edx)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [twR s₀, dataR s₀] s.mem t.mem) :
    DKeys (R s₀) (wK s₀) t := by
  obtain hnr : R s₀ ≤ 14 := h.keys.le
  obtain hed : ∀ o, t.ea (Impl.Aes.X86.AesNi.at_ .edx o) = s.ea (Impl.Aes.X86.AesNi.at_ .edx o) := fun o => by
    rw [ea_at, ea_at, hgd]
  obtain hmd : ∀ o, o + 16 ≤ 240 → t.mem.readW (s.ea (Impl.Aes.X86.AesNi.at_ .edx o)) 128 =
      s.mem.readW (s.ea (Impl.Aes.X86.AesNi.at_ .edx o)) 128 := fun o ho => by
    rw [ea_at, hd, scrA hp (by omega_using [ho])]
    exact scr_keep hp hf (by omega_using [ho]) (.inl (by omega_using [ho]))
  refine ⟨keys_stable hp h.keys ha hga hr hw hf, fun j h1 h2 => ?_, ?_⟩
  · rw [hed, hr, hw, hmd _ (by omega_using [hnr, h2])]; exact h.imc j h1 h2
  · rw [hed, hr, hw, hmd _ (by decide)]; exact h.last

/-- `Inv` is kept by moving `esi` and `edi`, and changing the flags. -/
theorem Inv.move {enc : Bool} {c p p' : Nat} {s t : State} (hI : Inv enc s₀ c p s)
    (hg : ∀ r, r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r)
    (hesi : t.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * p')) (hedi : t.gpr .edi = BitVec.ofNat 32 (N s₀ - p'))
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hx : t.xmm = s.xmm) : Inv enc s₀ c p' t :=
  { le := hI.le
    keys := keys_stable hp hI.keys hI.eax (hg _ (by decide) (by decide)) hr hw (by rw [hm]; exact Frame.refl _ _)
    dkeys := fun he => dkeys_stable hp (hI.dkeys he) hI.eax hI.edx (hg _ (by decide) (by decide))
      (hg _ (by decide) (by decide)) hr hw (by rw [hm]; exact Frame.refl _ _)
    eax := by rw [hg _ (by decide) (by decide), hI.eax]
    ecx := by rw [hg _ (by decide) (by decide), hI.ecx]
    edx := by rw [hg _ (by decide) (by decide), hI.edx]
    esi := hesi
    edi := hedi
    ebp := by rw [hg _ (by decide) (by decide), hI.ebp]
    esp := by rw [hg _ (by decide) (by decide), hI.esp]
    rd := by rw [hr, hI.rd]
    wr := by rw [hw, hI.wr]
    frame := by rw [hm]; exact hI.frame
    data := by rw [hm]; exact hI.data
    iv := by rw [hm]; exact hI.iv
    x7 := by rw [hx]; exact hI.x7
    cst := by rw [hm]; exact hI.cst }

omit hp in
/-- The rounds of a direction on the block registers `rs`. -/
theorem rounds_ok (enc : Bool) (rs : List XReg) (hnd : rs.Nodup) (h6 : .xmm6 ∉ rs)
    (hR : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14) {s : State}
    (hK : Keys (R s₀) (wK s₀) s) (hD : enc = false → DKeys (R s₀) (wK s₀) s)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (R s₀)) :
    WP isa (rounds enc rs) s fun s' =>
      (∀ b ∈ rs, bx (s'.xmm b) = ciph s₀ enc (bx (s.xmm b))) ∧ XFrame (.xmm6 :: rs) s s' := by
  cases enc
  · exact WP.mono (aesDec_ok rs hnd h6 hR s (hD rfl) hc) fun s' ⟨ha, hf⟩ =>
      ⟨fun b hb => bx_ciph (enc := false) (ha b hb), hf⟩
  · exact WP.mono (aes_ok rs hnd h6 hR s hK hc) fun s' ⟨ha, hf⟩ =>
      ⟨fun b hb => bx_ciph (enc := true) (ha b hb), hf⟩

/-- The blocks `c … c + n - 1` (`n` the number of registers) through XTS. -/
theorem group_ok (enc : Bool) {fill next : List Instr} {rs : List XReg}
    (hrs : (fill = fill6 ∧ next = next6 ∧ rs = regs6) ∨ (fill = fill1 ∧ next = [] ∧ rs = [.xmm0])) {c : Nat}
    {s : State} (hc : c + rs.length ≤ N s₀) (hI : Inv enc s₀ c c s) (after : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv enc s₀ (c + rs.length) c t → WP isa (.block after) t Q) :
    WP isa (group enc fill rs next after) s Q := by
  obtain hrs' : rs = regs6 ∨ rs = [.xmm0] := hrs.imp (·.2.2) (·.2.2)
  obtain hfill : (fill = fill6 ∧ rs = regs6) ∨ (fill = fill1 ∧ rs = [.xmm0]) :=
    hrs.imp (fun h => ⟨h.1, h.2.2⟩) (fun h => ⟨h.1, h.2.2⟩)
  obtain hnext : (next = next6 ∧ rs = regs6) ∨ (next = [] ∧ rs = [.xmm0]) := hrs.imp (·.2) (·.2)
  obtain ⟨hnd, h6⟩ : rs.Nodup ∧ .xmm6 ∉ rs := by rcases hrs' with rfl | rfl <;> decide
  obtain h7 : .xmm7 ∉ rs := by rcases hrs' with rfl | rfl <;> decide
  obtain hlen : rs.length ≤ 6 := by rcases hrs' with rfl | rfl <;> decide
  have hw := hp.data_fit
  obtain tw : twO = 256 := rfl
  obtain hdat : dataR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hscr : scrR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hdA : ∀ i, c + i < N s₀ → addr (s.gpr .esi) (16 * i) = blk s₀ (c + i) := fun i hi => by
    rw [hI.esi, addr_add, addr_eq (by omega_using [hw, hi]), ← Nat.mul_add]
  obtain htA : ∀ i < 6, addr (s.gpr .edx) (twO + 16 * i) = tA s₀ i := fun i hi => by
    rw [hI.edx]; exact scrA hp (by omega_using [hi, tw])
  obtain hdC : ∀ i, c + i < N s₀ → (dataR s₀).Contains (blk s₀ (c + i)) 16 := fun i hi =>
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hw])
  obtain htC : ∀ i < 6, (scrR s₀).Contains (tA s₀ i) 16 := fun i hi =>
    Offset.contains_base _ (by omega_using [hi, tw]) (by omega_using [hi, tw])
  obtain hdIn : ∀ i, c + i < N s₀ → InRegions s₀.wr (blk s₀ (c + i)) 16 := fun i hi => ⟨_, hdat, hdC i hi⟩
  obtain htIn : ∀ i < 6, InRegions s₀.wr (tA s₀ i) 16 := fun i hi => ⟨_, hscr, htC i hi⟩
  obtain hrC : (scrR s₀).Contains (Sa s₀ + BitVec.ofNat 64 rO) 16 := Offset.contains_base _ (by decide) (by decide)
  obtain htT : ∀ i < 6, (twR s₀).Contains (tA s₀ i) 16 := fun i hi => by
    rw [tA, ← Offset.add_add]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  obtain hrT : (twR s₀).Contains (Sa s₀ + BitVec.ofNat 64 rO) 16 := by
    rw [show rO = twO + 96 from rfl, ← Offset.add_add]
    exact Offset.contains_base _ (by decide) (by decide)
  -- The data is apart from the tweaks.
  obtain sepDT : ∀ i, c + i < N s₀ → ∀ i' < 6, Mem.Sep (blk s₀ (c + i)) 16 (tA s₀ i') 16 := fun i hi i' hi' =>
    hp.data_scr.sep (hdC i hi) (htC i' hi')
  refine WP.seq (WP.mono (fill_ok (dA := fun i => blk s₀ (c + i)) (tA := tA s₀) (T := twR s₀)
    (P := Sa s₀ + BitVec.ofNat 64 rO) (C := Sa s₀ + BitVec.ofNat 64 cO) hfill s
    (by rw [hI.edx]; exact scrA hp (by decide))
    (by rw [hI.wr]; exact in_rd ⟨_, hscr, Offset.contains_base _ (by decide) (by decide)⟩) hI.cst
    (fun i hi => hdA i (by omega_using [hi, hc])) htA (by rw [hI.edx]; exact scrA hp (by decide))
    (fun i hi => by rw [hI.wr]; exact in_rd (hdIn i (by omega_using [hi, hc])))
    (fun i hi => by rw [hI.wr]; exact htIn i hi) (by rw [hI.wr]; exact ⟨_, hscr, hrC⟩) htT hrT
    (fun i hi i' hi' hne => Offset.sep _ (by omega_using [hne]) (by omega_using [hi, tw]) (by omega_using [hi', tw]))
    (fun i hi => Offset.sep _ (.inr (by
      obtain e : rO = 352 := rfl
      omega_using [hi, tw, e])) (by decide) (by omega_using [hi, tw]))
    (fun i hi i' hi' => sepDT i (by omega_using [hi, hc]) i' hi')
    (fun i hi => hp.data_scr.sep (hdC i (by omega_using [hi, hc])) hrC))
    fun s₄ ⟨hv₄, hh₄, gs₄, rs₄, ws₄, f₃, hr₄⟩ => ?_)
  obtain f₄ : Frame [twR s₀, dataR s₀] s.mem s₄.mem := f₃.mono (by simp)
  refine WP.seq (WP.mono (rounds_ok enc rs hnd h6 hp.rounds
    (keys_stable hp hI.keys hI.eax (by rw [gs₄]) rs₄ ws₄ f₄)
    (fun he => dkeys_stable hp (hI.dkeys he) hI.eax hI.edx (by rw [gs₄]) (by rw [gs₄]) rs₄ ws₄ f₄)
    (by rw [gs₄]; exact hI.ecx)) fun v ⟨ha, fa⟩ => ?_)
  obtain gv : v.gpr = s.gpr := fa.gpr.trans gs₄
  rw [WP.block_append_iff]
  refine WP.mono (xorOut_ok (dA := fun i => blk s₀ (c + i)) (tA := tA s₀) (D := ⟨blk s₀ c, 16 * rs.length⟩)
    rs 0 v hnd h6
    (fun i hi => by rw [Nat.zero_add, gv]; exact hdA i (by omega_using [hi, hc]))
    (fun i hi => by rw [Nat.zero_add, gv]; exact htA i (by omega_using [hi, hlen]))
    (fun i hi => by rw [Nat.zero_add, fa.wr, ws₄, hI.wr]; exact hdIn i (by omega_using [hi, hc]))
    (fun i hi => by
      rw [Nat.zero_add, fa.rd, fa.wr, rs₄, ws₄, hI.wr]; exact in_rd (htIn i (by omega_using [hi, hlen])))
    (fun i hi => by
      show (⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * c), _⟩ : Region).Contains
        ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * (c + (0 + i)))) 16
      rw [Nat.zero_add, Nat.mul_add, ← Offset.add_add]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hlen]))
    (fun i hi i' hi' => by
      rw [Nat.zero_add, Nat.zero_add]
      exact fun x h₁ h₂ => sepDT i' (by omega_using [hi', hc]) i (by omega_using [hi, hlen]) x h₂ h₁)
    (fun i hi i' hi' hne => by
      rw [Nat.zero_add, Nat.zero_add]
      exact Offset.sep _ (by omega_using [hne]) (by omega_using [hi, hc, hw]) (by omega_using [hi', hc, hw])))
    fun t₁ ⟨hv, hx, g, rd, wr, hf, hk⟩ => ?_
  simp only [Nat.zero_add] at hv hk
  -- What the next tweak needs is kept by the rounds and the stores.
  obtain hh : Held rs (Sa s₀ + BitVec.ofNat 64 rO) (s.xmm .xmm7) t₁ := by
    have x7 : t₁.xmm .xmm7 = s₄.xmm .xmm7 := by
      rw [hx _ (by decide) h7, fa.xmm _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, h7⟩)]
    have mP : t₁.mem.readW (Sa s₀ + BitVec.ofNat 64 rO) 128 = s₄.mem.readW (Sa s₀ + BitVec.ofNat 64 rO) 128 := by
      rw [hk _ fun i hi => fun y h₁ h₂ => hp.data_scr.sep (hdC i (by omega_using [hi, hc])) hrC y h₂ h₁, fa.mem]
    unfold Held at hh₄ ⊢
    rw [x7, mP]; exact hh₄
  rw [WP.block_append_iff]
  refine WP.mono (next_ok (x := s.xmm .xmm7) hnext t₁ (by rw [g, gv, hI.edx]; exact scrA hp (by decide))
    (by rw [rd, wr, fa.rd, fa.wr, rs₄, ws₄, hI.wr]; exact in_rd ⟨_, hscr, hrC⟩) hh)
    fun t ⟨x7t, gt₁, mt, rdt, wrt⟩ => ?_
  rw [← mt] at hv hf
  obtain gt : t.gpr = s.gpr := gt₁.trans (g.trans gv)
  obtain rt : t.rd = s.rd := rdt.trans (rd.trans (fa.rd.trans rs₄))
  obtain wt : t.wr = s.wr := wrt.trans (wr.trans (fa.wr.trans ws₄))
  -- What the group changes in memory.
  obtain hF' : Frame [twR s₀, ⟨blk s₀ c, 16 * rs.length⟩] s.mem t.mem := by
    have h₁ : Frame [twR s₀, ⟨blk s₀ c, 16 * rs.length⟩] s.mem s₄.mem := f₃.mono (by simp)
    rw [← fa.mem] at h₁
    exact h₁.trans (hf.mono (by simp))
  obtain hF : Frame [twR s₀, dataR s₀] s.mem t.mem := hF'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, Offset.sub_base _ (by omega_using [hc])⟩
  -- The tweak of each block, as the group stored it.
  obtain tv : ∀ i < rs.length, bx (v.mem.readW (tA s₀ i) 128) = Spec.Xts.next (iv0 s₀) (c + i) := fun i hi => by
    rw [fa.mem, hr₄ i hi, bx_repeat, hI.x7, next_add]
  -- Each block of the group.
  obtain blkOut : ∀ i (hi : i < rs.length), bytesAt t.mem (blk s₀ (c + i)) 16 = outB s₀ enc (c + i) := fun i hi => by
    obtain hcN : c + i < N s₀ := by omega_using [hi, hc]
    obtain e₁ : bx (s₄.xmm rs[i]) =
        Spec.Cbc.xor (bytesAt s₀.mem (blk s₀ (c + i)) 16) (Spec.Xts.next (iv0 s₀) (c + i)) := by
      rw [hv₄ i hi, bx_xor, ← bytesAt_bx, hI.data _ hcN, ite_eq_right (by omega_using []), bx_repeat, hI.x7,
        next_add]
    rw [bytesAt_bx, hv i hi, bx_xor, ha _ (List.getElem_mem hi), e₁, tv i hi]
    rfl
  exact hQ t
    { le := hc
      keys := keys_stable hp hI.keys hI.eax (by rw [gt]) rt wt hF
      dkeys := fun he => dkeys_stable hp (hI.dkeys he) hI.eax hI.edx (by rw [gt]) (by rw [gt]) rt wt hF
      eax := by rw [gt]; exact hI.eax
      ecx := by rw [gt]; exact hI.ecx
      edx := by rw [gt]; exact hI.edx
      esi := by rw [gt]; exact hI.esi
      edi := by rw [gt]; exact hI.edi
      ebp := by rw [gt]; exact hI.ebp
      esp := by rw [gt]; exact hI.esp
      rd := rt.trans hI.rd
      wr := wt.trans hI.wr
      frame := hI.frame.trans (hF.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨Sa s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
        · exact ⟨dataR s₀, by simp, fun _ h => h⟩)
      data := fun j hj => by
        by_cases h₁ : c ≤ j ∧ j < c + rs.length
        · obtain ⟨i, rfl⟩ : ∃ i, j = c + i := ⟨j - c, by omega_using [h₁]⟩
          rw [blkOut i (by omega_using [h₁]), ite_eq_left h₁.2]
        · rw [Proof.Cmac.bytesAt_frame hF' (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right tw_sub
            · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [hj, hw]) (by omega_using [hc, hw]))
            (by decide), hI.data j hj]
          by_cases h₂ : j < c
          · rw [ite_eq_left h₂, ite_eq_left (by omega_using [h₂])]
          · rw [ite_eq_right h₂, ite_eq_right (by omega_using [h₁, h₂])]
      iv := by
        rw [Proof.Cmac.bytesAt_frame hF (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.iv_scr.sub_right tw_sub
          · exact hp.iv_data) (by decide)]
        exact hI.iv
      x7 := by rw [x7t, bx_repeat, hI.x7, next_add]
      cst := by rw [scr_keep hp hF (o := cO) (by decide) (.inr (by decide))]; exact hI.cst }

end

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `add esi, 16 m; sub edi, m`, after `m` more blocks. -/
theorem advance_ok {enc : Bool} {rest : List Instr} {c m : Nat} (hc : c + m ≤ N s₀) {s : State}
    (hI : Inv enc s₀ (c + m) c s) {Q : State → Prop}
    (hQ : ∀ s', Inv enc s₀ (c + m) (c + m) s' →
      s'.zf = some (decide (N s₀ - (c + m) = 0)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * m))) :: .alu .sub .edi
      (.imm (BitVec.ofNat 32 m)) :: rest)) s Q := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  obtain e : BitVec.ofNat 32 (N s₀ - c) - BitVec.ofNat 32 m = BitVec.ofNat 32 (N s₀ - (c + m)) := by
    rw [Wp.sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  refine x_addi fun s₁ u₁ x₁ => x_subi fun s₂ u₂ x₂ hz => hQ s₂ ?_ ?_
  · refine hI.move hp (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1]) ?_ ?_
      (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [x₂, x₁])
    · rw [u₂.other _ (by decide), u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
    · rw [u₂.gpr, u₁.other _ (by decide), hI.edi, e]
  · rw [hz, u₁.other _ (by decide), hI.edi, e, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- Six blocks. -/
theorem six_ok {enc : Bool} {c : Nat} (hc : c + 6 ≤ N s₀) {s : State} (hI : Inv enc s₀ c c s) :
    WP isa (six enc) s fun s' => Inv enc s₀ (c + 6) (c + 6) s' ∧ s'.cf = some (decide (N s₀ - (c + 6) < 6)) := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  refine group_ok hp enc (.inl ⟨rfl, rfl, rfl⟩) hc hI _ fun s₁ hI₁ => ?_
  refine advance_ok hp (m := 6) hc hI₁ fun s₂ hI₂ _ => ?_
  refine x_cmpi fun s₃ u₃ x₃ hcf => WP.block_nil ⟨?_, ?_⟩
  · exact hI₂.move hp (fun r _ _ => by rw [u₃.gpr]) (by rw [u₃.gpr, hI₂.esi]) (by rw [u₃.gpr, hI₂.edi])
      u₃.mem u₃.rd u₃.wr x₃
  · rw [hcf, hI₂.edi, Wp.toNat_ofNat_lt (by omega_using [hn])]; rfl

/-- One block. -/
theorem one_ok {enc : Bool} {c : Nat} (hc : c < N s₀) {s : State} (hI : Inv enc s₀ c c s) :
    WP isa (one enc) s fun s' => Inv enc s₀ (c + 1) (c + 1) s' ∧ s'.zf = some (decide (N s₀ - (c + 1) = 0)) := by
  refine group_ok hp enc (.inr ⟨rfl, rfl, rfl⟩) hc hI _ fun s₁ hI₁ => ?_
  exact advance_ok hp (m := 1) (rest := []) hc hI₁ fun s₂ hI₂ hz => WP.block_nil ⟨hI₂, hz⟩

/-- `test edi, edi`: ZF is set when no block is left. -/
theorem test_ok {enc : Bool} {c : Nat} {s : State} (hI : Inv enc s₀ c c s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      Inv enc s₀ c c s' ∧ s'.zf = some (decide (N s₀ - c = 0)) := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  refine x_test fun s' u x hz => WP.block_nil ⟨?_, ?_⟩
  · exact hI.move hp (fun r _ _ => by rw [u.gpr]) (by rw [u.gpr, hI.esi]) (by rw [u.gpr, hI.edi])
      u.mem u.rd u.wr x
  · rw [hz, hI.edi, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- The blocks left after `c₀`, six and then one at a time. -/
theorem tail_ok {enc : Bool} {c₀ : Nat} {s₁ : State} (hI₁ : Inv enc s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (N s₀ - c₀ < 6))) : WP isa (tail enc) s₁ (Inv enc s₀ (N s₀) (N s₀)) := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀ - c < 6 ∧ Inv enc s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀ - c₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c + 6 ≤ N s₀ ∧ Inv enc s₀ c c s
      have hstep : ∀ m s, I6 m s → WP isa (six enc) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, N s₀ - c < 6 ∧ Inv enc s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (six_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : N s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 6), by omega_using [hc], c + 6, rfl,
            by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I6 hstep (N s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_using [h], hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (N s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = N s₀ := by have := hI₃.le; simp at h; omega_using [this, h]
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c < N s₀ ∧ Inv enc s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (one enc) s (fun s' =>
        (eval .ne s' = some false ∧ Inv enc s₀ (N s₀) (N s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (one_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : N s₀ - (c + 1) = 0
      · have : c + 1 = N s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], N s₀ - (c + 1), by omega_using [hc], c + 1, rfl,
          by omega_using [hlast], hI'⟩
    have hlt : c < N s₀ := by have := hI₃.le; simp at h; omega_using [h]
    exact WP.loop (M := isa) I1 hstep (N s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

/-! ## Before and after the blocks -/

omit hp in
/-- The constant. -/
theorem const_run (s : State) :
    ∃ s', runBlock isa const s = some s' ∧ s'.xmm .xmm6 = signC ∧ (∀ r, ¬ r = .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [const, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, exec_bin, exec_movd, Option.map_some]
    rfl, ?_, fun r h => ?_, by rfl, by rfl, by rfl⟩
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, gpr_setReg_self, reduceCtorEq, not_false_eq_true]
    decide
  · simp only [gpr_setXmm, gpr_setReg_of_ne _ _ h]

/-- After `pro`: the constant in the scratch buffer, and the registers the
rounds read. -/
structure P1 (s₀ s : State) : Prop where
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)
  edx : s.gpr .edx = S s₀
  esi : s.gpr .esi = Dp s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨Sa s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : ∀ j < N s₀, bytesAt s.mem (blk s₀ j) 16 = bytesAt s₀.mem (blk s₀ j) 16
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = iv0 s₀
  cst : s.mem.readW (Sa s₀ + BitVec.ofNat 64 cO) 128 = signC

omit hp in
/-- The constant stored. -/
theorem store_run {s : State} {Q : Addr} (hQ : addr (s.gpr .edx) cO = Q) (iQ : InRegions s.wr Q 16) :
    ∃ s', runBlock isa [.movdquStore (at_ .edx cO) .xmm6] s = some s' ∧
      s'.mem = s.mem.writeW Q (s.xmm .xmm6) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, ea_at', hQ, iQ, ↓reduceIte]
    rfl, by rfl, by rfl, by rfl, by rfl⟩

omit hp in
/-- A part of the scratch buffer's first 2064 bytes is among what the
function may change. -/
theorem scr_frame {m m' : Mem} {o n : Nat} (ho : o + n ≤ 2064) (hf : Frame [⟨Sa s₀ + BitVec.ofNat 64 o, n⟩] m m') :
    Frame [ivR s₀, dataR s₀, ⟨Sa s₀, 2064⟩, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨Sa s₀, 2064⟩, by simp, Offset.sub_base _ ho⟩

theorem pro_ok {M : Mode} {s : State} (h : LInv M s₀ 0 s) : WP isa (.block pro) s (P1 s₀) := by
  obtain hscr : scrR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hargs := hp.args_of (UPre.big_of h.frame)
  show WP isa (.block (.mov .edx (argOp 5) :: (const ++
    ([.movdquStore (Impl.Aes.X86.AesNi.at_ .edx cO) .xmm6, .mov .eax (argOp 0), .mov .ecx (argOp 1)] : List Instr))))
    s _
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 5 (by decide)) fun s₁ u₁ => ?_
  obtain ⟨s₂, run₂, x6₂, g₂, m₂, rd₂, wr₂⟩ := const_run s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain edx₂ : s₂.gpr .edx = S s₀ := by rw [g₂ _ (by decide)]; exact u₁.gpr
  obtain w₂ : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr, h.wr]
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := store_run (s := s₂) (Q := Sa s₀ + BitVec.ofNat 64 cO)
    (by rw [edx₂]; exact scrA hp (o := cO) (by decide))
    (by rw [w₂]; exact ⟨_, hscr, Offset.contains_base _ (by decide) (by decide)⟩)
  show WP isa (.block (([.movdquStore (at_ .edx cO) .xmm6] : List Instr) ++
    ([.mov .eax (argOp 0), .mov .ecx (argOp 1)] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [x6₂, m₂, u₁.mem] at m₄
  obtain f₄ : Frame [⟨Sa s₀ + BitVec.ofNat 64 cO, 16⟩] s.mem s₄.mem := by
    rw [m₄]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fr₄ : Frame [ivR s₀, dataR s₀, ⟨Sa s₀, 2064⟩, stkR s₀] (savedMem s₀) s₄.mem :=
    h.frame.trans (scr_frame (o := cO) (n := 16) (by decide) f₄)
  obtain esp₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [g₄, g₂ _ (by decide), u₁.other _ (by decide)]; exact h.esp
  obtain rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [rd₄, wr₄, rd₂, wr₂, u₁.rd, u₁.wr, hrw]
  obtain hargs₄ := hp.args_of (UPre.big_of fr₄)
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (hargs₄ 0 (by decide)) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide)]; exact esp₄)
    (by rw [u₅.rd, u₅.wr, rw₄]; exact hp.arg_in (by decide)) (by rw [u₅.mem]; exact hargs₄ 1 (by decide))
    fun s₆ u₆ => ?_
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  obtain blkScr : ∀ j < N s₀, (⟨blk s₀ j, 16⟩ : Region).Disjoint ⟨Sa s₀ + BitVec.ofNat 64 cO, 16⟩ :=
    fun j hj => (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Offset.sub_base _ (by decide))
  refine WP.block_nil
    { eax := by rw [u₆.other _ (by decide)]; exact u₅.gpr
      ecx := by rw [u₆.gpr]; exact arg_ofNat s₀ 1
      edx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄]; exact edx₂
      esi := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄, g₂ _ (by decide),
          u₁.other _ (by decide), h.esi, Nat.mul_zero]
        exact BitVec.add_zero _
      esp := by rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact esp₄
      rd := by rw [u₆.rd, u₅.rd, rd₄, rd₂, u₁.rd, h.rd]
      wr := by rw [u₆.wr, u₅.wr, wr₄, wr₂, u₁.wr, h.wr]
      frame := by rw [m₆]; exact fr₄
      data := fun j hj => by
        rw [m₆, Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact blkScr j hj) (by decide)]
        obtain e := List.getElem_of_eq h.data (i := j) (by rw [AesCbc.length_blocksAt]; exact hj)
        rw [AesCbc.getElem_blocksAt _ _ hj] at e
        rw [e]
        simp only [outK, List.take_zero, M.out_nil, List.nil_append, List.drop_zero]
        exact AesCbc.getElem_blocksAt _ _ hj
      iv := by
        rw [m₆, Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.iv_scr.sub_right (Offset.sub_base _ (by decide))) (by decide), h.iv]
        simp only [chainK, List.take_zero, M.chain_nil]
      cst := by rw [m₆, m₄]; exact Mem.readW_writeW_self _ _ 16 _ (by decide) }

end

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- After the round keys. -/
structure P2 (enc : Bool) (s₀ s : State) : Prop extends P1 s₀ s where
  keys : Keys (R s₀) (wK s₀) s
  dkeys : enc = false → DKeys (R s₀) (wK s₀) s

/-- The round keys: read where they are, and for decryption through
`aesimc` into the scratch buffer. -/
theorem keys_ok (enc : Bool) {s : State} (h : P1 s₀ s) : WP isa (keys enc) s (P2 enc s₀) := by
  have fS := hp.scr_fit
  obtain hnr : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain big : Frame (Big s₀) s₀.mem s.mem := UPre.big_of h.frame
  cases enc
  · show WP isa Impl.Aes.X86.AesNi.imcKeys s _
    -- The round keys, where only the schedule and the scratch buffer's first 2048 bytes are permitted.
    let rd : List Region := [reg32 (W s₀) 240]
    let wr : List Region := [reg32 (S s₀) 2048]
    obtain hwr : Covers wr s.wr := Covers.of_sub fun r hr => by
      simp only [wr, List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by rw [h.wr, hp.wr]; simp, 0, by simp, by show 0 + 2048 ≤ 2176; decide⟩
    obtain hrd : Covers (rd ++ wr) (s.rd ++ s.wr) :=
      Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
        simp only [rd, List.mem_singleton] at hr; subst hr
        rw [h.rd, hp.rd]; exact List.mem_cons_self)) (Covers.right hwr)
    obtain hs : ImcSetup (s.withRegions rd wr) :=
      { sch := by rw [State.withRegions_gpr, h.eax]; exact List.mem_cons_self
        scr := by rw [State.withRegions_gpr, h.edx]; exact List.mem_singleton_self _
        fitS := by rw [State.withRegions_gpr, h.eax]; exact hp.sch_fit
        fitB := by rw [State.withRegions_gpr, h.edx]; omega_using [fS]
        sep := by
          rw [State.withRegions_gpr, h.eax, h.edx]
          exact hp.sch_scr.sub_right (Region.sub_prefix (by decide)) }
    obtain hK₁ : Keys (R s₀) (wK s₀) (s.withRegions rd wr) := by
      obtain k := niKeys (s := s.withRegions rd wr) (nr := R s₀) (by omega_using [hnr]) hp.sch_fit
        (by rw [State.withRegions_gpr]; exact h.eax) List.mem_cons_self
      rwa [State.withRegions_mem, UPre.sched_bytes hp big] at k
    refine WP.narrow (imcKeys_ok hs hp.rounds (by rw [State.withRegions_gpr]; exact h.ecx)) hrd hwr
      (fun s₂ rd₂ wr₂ _ hd₂ => ?_) (by decide)
    obtain hK₂ : DKeys (R s₀) (wK s₀) s₂ :=
      Decrypt.dkeys_widen (dKeys_of_imc hs hK₁ hd₂) (State.withRegions_gpr ..).symm (State.withRegions_mem ..).symm
        (by rw [State.withRegions_rd, State.withRegions_wr, rd₂, wr₂]; exact hrd)
    obtain ⟨Sk, hI₂, -, -⟩ := hd₂
    obtain g₂ : s₂.gpr = s.gpr := by
      have := hI₂.gpr
      rwa [State.withRegions_gpr, State.withRegions_gpr] at this
    obtain m₂ : Frame [⟨addr (S s₀) 16, 224⟩] s.mem s₂.mem := by
      have := hI₂.frame
      rwa [State.withRegions_gpr, h.edx, State.withRegions_mem, State.withRegions_mem] at this
    rw [scrA hp (o := 16) (by decide)] at m₂
    obtain keep : ∀ o, 368 ≤ o → o + 16 ≤ 2176 →
        s₂.mem.readW (Sa s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (Sa s₀ + BitVec.ofNat 64 o) 128 :=
      fun o h₁ h₂ => m₂.readW (r := ⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)) (by decide)
    exact
      { eax := by rw [g₂]; exact h.eax
        ecx := by rw [g₂]; exact h.ecx
        edx := by rw [g₂]; exact h.edx
        esi := by rw [g₂]; exact h.esi
        esp := by rw [g₂]; exact h.esp
        rd := rd₂.trans h.rd
        wr := wr₂.trans h.wr
        frame := h.frame.trans (scr_frame (o := 16) (n := 224) (by decide) m₂)
        data := fun j hj => by
          rw [Proof.Cmac.bytesAt_frame m₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Offset.sub_base _ (by decide))) (by decide)]
          exact h.data j hj
        iv := by
          rw [Proof.Cmac.bytesAt_frame m₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.iv_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)]
          exact h.iv
        cst := by rw [keep cO (by decide) (by decide)]; exact h.cst
        keys := hK₂.keys
        dkeys := fun _ => hK₂ }
  · obtain hK : Keys (R s₀) (wK s₀) s := by
      obtain k := niKeys (s := s) (nr := R s₀) (by omega_using [hnr]) hp.sch_fit h.eax
        (by rw [h.rd, hp.rd]; exact List.mem_append_left _ List.mem_cons_self)
      rwa [UPre.sched_bytes hp big] at k
    exact WP.block_nil { toP1 := h, keys := hK, dkeys := fun he => nomatch he }

omit hp in
theorem addr_iv (hp : UPre s₀) : addr (Iv s₀) 0 = (Iv s₀).setWidth 64 := by
  rw [addr_eq (by have := hp.iv_fit; omega_using [this])]; exact add0 _

/-- `tweak`, the number of blocks and the tweak. -/
theorem start_ok (enc : Bool) {s : State} (h : P2 enc s₀ s) :
    WP isa (.block start) s fun s' => Inv enc s₀ 0 0 s' ∧ s'.cf = some (decide (N s₀ - 0 < 6)) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hargs := hp.args_of (UPre.big_of h.frame)
  show WP isa (.block [.mov .ebp (argOp 2), .mov .edi (argOp 4),
    .movdquLoad .xmm7 (Impl.Aes.X86.AesNi.at_ .ebp 0), .alu .cmp .edi (.imm 6)]) s _
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide)]; exact h.esp)
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 4 (by decide))
    fun s₂ u₂ => ?_
  obtain ebp₂ : s₂.gpr .ebp = Iv s₀ := by rw [u₂.other _ (by decide)]; exact u₁.gpr
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  obtain g₂ : ∀ r, r ≠ .ebp → r ≠ .edi → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [u₂.other r h₂, u₁.other r h₁]
  refine x_load (B := Iv s₀) ebp₂ (by
    rw [addr_iv hp, rd₂, wr₂, h.wr]
    exact in_rd ⟨ivR s₀, by rw [hp.wr]; simp, Region.contains_self _ _⟩) ?_
  obtain ⟨s₃, hs₃⟩ : ∃ s₃ : State, s₂.setXmm .xmm7 (s₂.mem.readW (addr (Iv s₀) 0) 128) = s₃ := ⟨_, rfl⟩
  rw [hs₃]
  obtain g₃ : s₃.gpr = s₂.gpr := by rw [← hs₃]; rfl
  obtain m₃ : s₃.mem = s.mem := by rw [← hs₃]; exact m₂
  obtain rd₃ : s₃.rd = s.rd := by rw [← hs₃]; exact rd₂
  obtain wr₃ : s₃.wr = s.wr := by rw [← hs₃]; exact wr₂
  obtain x₃ : s₃.xmm .xmm7 = s.mem.readW ((Iv s₀).setWidth 64) 128 := by
    rw [← hs₃, xmm_setXmm_self, addr_iv hp, m₂]
  refine x_cmpi fun s₄ u₄ x₄ hcf => WP.block_nil ⟨?_, ?_⟩
  · obtain g₄ : ∀ r, r ≠ .ebp → r ≠ .edi → s₄.gpr r = s.gpr r := fun r h₁ h₂ => by rw [u₄.gpr, g₃]; exact g₂ r h₁ h₂
    obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem]; exact m₃
    obtain rd₄ : s₄.rd = s.rd := by rw [u₄.rd]; exact rd₃
    obtain wr₄ : s₄.wr = s.wr := by rw [u₄.wr]; exact wr₃
    exact
      { le := Nat.zero_le _
        keys := keys_stable hp h.keys h.eax (g₄ _ (by decide) (by decide)) rd₄ wr₄ (by rw [m₄]; exact Frame.refl _ _)
        dkeys := fun he => dkeys_stable hp (h.dkeys he) h.eax h.edx (g₄ _ (by decide) (by decide))
          (g₄ _ (by decide) (by decide)) rd₄ wr₄ (by rw [m₄]; exact Frame.refl _ _)
        eax := by rw [g₄ _ (by decide) (by decide)]; exact h.eax
        ecx := by rw [g₄ _ (by decide) (by decide)]; exact h.ecx
        edx := by rw [g₄ _ (by decide) (by decide)]; exact h.edx
        esi := by rw [g₄ _ (by decide) (by decide), h.esi, Nat.mul_zero]; exact (BitVec.add_zero _).symm
        edi := by rw [u₄.gpr, g₃, u₂.gpr, Nat.sub_zero]; exact arg_ofNat s₀ 4
        ebp := by rw [u₄.gpr, g₃]; exact ebp₂
        esp := by rw [g₄ _ (by decide) (by decide)]; exact h.esp
        rd := rd₄.trans h.rd
        wr := wr₄.trans h.wr
        frame := by rw [m₄]; exact h.frame
        data := fun j hj => by rw [m₄, ite_eq_right (Nat.not_lt_zero _)]; exact h.data j hj
        iv := by rw [m₄]; exact h.iv
        x7 := by rw [x₄, x₃, ← bytesAt_bx, h.iv]; rfl
        cst := by rw [m₄]; exact h.cst }
  · rw [hcf, g₃, u₂.gpr]; rfl

/-- The tweak after the last block stored: the invariant the epilogue starts from. -/
theorem storeT_ok (enc : Bool) {s : State} (hI : Inv enc s₀ (N s₀) (N s₀) s) :
    WP isa (.block storeT) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) := by
  show WP isa (.block [.movdquStore (Impl.Aes.X86.AesNi.at_ .ebp 0) .xmm7]) s _
  refine x_store (B := Iv s₀) hI.ebp (by
    rw [addr_iv hp, hI.wr]; exact ⟨ivR s₀, by rw [hp.wr]; simp, Region.contains_self _ _⟩)
    fun t u => WP.block_nil ?_
  rw [addr_iv hp] at u
  obtain fT : Frame [ivR s₀] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hl : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  exact
    { esi := by rw [u.gpr]; exact hI.esi
      esp := by rw [u.gpr]; exact hI.esp
      rd := u.rd.trans hI.rd
      wr := u.wr.trans hI.wr
      frame := hI.frame.trans (fT.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
      data := by
        rw [outK, AesXts.xtsMode_out, List.take_of_length_le (by omega_using [hl]),
          List.drop_of_length_le (by omega_using [hl]), List.append_nil]
        apply List.ext_getElem (by rw [AesCbc.length_blocksAt, AesXts.length_crypt, hl])
        intro j h₁ h₂
        rw [AesCbc.length_blocksAt] at h₁
        rw [AesCbc.getElem_blocksAt _ _ h₁, getElem_crypt _ _ _ (by rw [hl]; exact h₁),
          AesCbc.getElem_blocksAt _ _ h₁, Proof.Cmac.bytesAt_frame fT (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.iv_data.symm.sub_left (UPre.data_sub h₁)) (by decide), hI.data j h₁, ite_eq_left h₁]
      iv := by
        rw [u.mem, bytesAt_writeW_bx, hI.x7, chainK, AesXts.xtsMode_chain,
          List.take_of_length_le (by omega_using [hl]), hl] }

/-- All the blocks. -/
theorem batch_wp (enc : Bool) {s₁ : State} (h : LInv (AesXts.xtsMode enc) s₀ 0 s₁) :
    WP isa (batch enc) s₁ (LInv (AesXts.xtsMode enc) s₀ (N s₀)) :=
  WP.seq (WP.mono (pro_ok hp h) fun _ h₁ =>
    WP.seq (WP.mono (keys_ok hp enc h₁) fun _ h₂ =>
      WP.seq (WP.mono (start_ok hp enc h₂) fun _ ⟨h₃, hcf⟩ =>
        WP.seq (WP.mono (tail_ok hp h₃ hcf) fun _ h₄ => storeT_ok hp enc h₄))))

end

/-- The whole function. -/
theorem crypt_wp (enc : Bool) {s₀ : State} (h0 : (modeX86 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt enc) s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 (AesXts.xtsMode enc)).post s₀ s' :=
  ends_wp h0 fun hp _ _ h => batch_wp hp enc h

/-! ## Constant time -/

materialize_code encrypt
materialize_code decrypt

theorem encrypt_ct : ConstantTime isa (modeX86 (AesXts.xtsMode true)).pre (modeX86 (AesXts.xtsMode true)).pub
    encrypt :=
  VG.Taint.constantTime (A := sseTaint) (argTaint [] (4 + 4 * 6))
    (fun _ _ h₁ h₂ hq => Pt.agree hq (UPre.of h₁) (UPre.of h₂) ⟨rfl, rfl, fun _ _ => rfl⟩ ⟨rfl, rfl, fun _ _ => rfl⟩
      (fun r hr => by simp at hr))
    (by taint_decide)

theorem decrypt_ct : ConstantTime isa (modeX86 (AesXts.xtsMode false)).pre (modeX86 (AesXts.xtsMode false)).pub
    decrypt :=
  VG.Taint.constantTime (A := sseTaint) (argTaint [] (4 + 4 * 6))
    (fun _ _ h₁ h₂ hq => Pt.agree hq (UPre.of h₁) (UPre.of h₂) ⟨rfl, rfl, fun _ _ => rfl⟩ ⟨rfl, rfl, fun _ _ => rfl⟩
      (fun r hr => by simp at hr))
    (by taint_decide)

theorem encrypt_ok (s : State) (hs : (modeX86 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeX86 (AesXts.xtsMode true)).post s s' :=
  crypt_wp true hs

theorem decrypt_ok (s : State) (hs : (modeX86 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeX86 (AesXts.xtsMode false)).post s s' :=
  crypt_wp false hs

/-! ## What their callers need of their code -/

theorem encrypt_noSp : NoSp encrypt := NoSp.of_all (by lit_decide)

theorem decrypt_noSp : NoSp decrypt := NoSp.of_all (by lit_decide)

theorem encrypt_stack : stackUse encrypt = 0 := by lit_decide

theorem decrypt_stack : stackUse decrypt = 0 := by lit_decide

theorem encrypt_spSafe : encrypt.all (fun i => !isa.writesSp i) = true := Code.all_of_spTest (by lit_decide)

theorem decrypt_spSafe : decrypt.all (fun i => !isa.writesSp i) = true := Code.all_of_spTest (by lit_decide)

theorem encrypt_calleeOk : calleeOk encrypt = true := by lit_decide

theorem decrypt_calleeOk : calleeOk decrypt = true := by lit_decide

end VG.Proof.AesXts.X86.AesNi
