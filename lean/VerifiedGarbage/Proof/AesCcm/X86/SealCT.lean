module

import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.X86.Mac
public import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesCcm.X86.Mac
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.AesCcm.X86.Entry
meta import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.Proof.AesCcm.X86.Absorb
import VerifiedGarbage.Proof.AesCcm.X86.AadCT
import VerifiedGarbage.Proof.AesCcm.X86.Aad
meta import VerifiedGarbage.Proof.AesCcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesCcm.X86.AadCT
meta import VerifiedGarbage.Proof.AesCcm.X86.Aad
import VerifiedGarbage.Proof.AesCcm.X86.Callee
meta import VerifiedGarbage.Proof.AesCcm.X86.Callee
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
meta import VerifiedGarbage.Proof.AesGcm.X86.Env
meta import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.AesCcm.Ctr
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.Cmac.Stream

/-! ### `AesCcm.X86.TopCT`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Seal`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Crypt`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data with one call of `vg_aes_ctr32_to` from `Ctr₁`, whose low 32
bits do not wrap around as there are fewer than 2²⁸ blocks (`ctrWhole_ok`),
then its last `n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which
`vg_aes_ctr32_to` writes over a zero block (`ctrTail_ok`): the data XORed with
CCM's keystream from `Ctr₁` (`ctr_ok`), which is its encryption
(`Proof.AesCcm.crypt_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold zero4_bytes' length_bytesAt and_self_beq32
  XorPre XorPost xorLoop_ok xorBytes shr4 and15 runBlock_app_of covers_left covers_off)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `[64, 96)`, `[240, 2560)`, the stack and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 64, 32⟩, wC W, below SP 60, ⟨w64 D, n⟩]

/-- What `ctr` needs. -/
structure CtrCtx (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n : Nat) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  hn32 : n < 2 ^ 32
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : Buf W SP s D n
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩

namespace CtrCtx

variable {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n : Nat}
  (C : CtrCtx K W SP s R nonce D n)
include C

/-- The parts of `W` that `ctr` does not write. -/
theorem disj {d k : Nat} (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 240)) :
    ∀ r ∈ ctrR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rcases h with h | h
    · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (C.lay.stk_w' (by omega_arith)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega_arith))).symm

theorem slot_kept {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m W o = slotv s.mem W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (C.disj (.inr ⟨by omega_arith, h₂⟩)) (by decide)

theorem c0_kept {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) :
    bytesAt m (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  rw [Proof.AesGcm.X86.bytesAt_frame hf (C.disj (.inl (by decide))) (by decide), C.c0]

theorem ciph_kept {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) :
    Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R := by
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  refine ctxCiph_frame hf (fun r hr => ?_) hRb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.stk_k.symm
  · exact C.dk

end CtrCtx

/-- After the whole blocks. -/
structure CtrMid (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n : Nat) (t : State) :
    Prop where
  env : Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (ctrR W SP D n) s.mem t.mem
  dO : slotv t.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))
  nO : slotv t.mem W nO = BitVec.ofNat 32 (n % 16)
  done : bytesAt t.mem (w64 D) (16 * (n / 16)) =
    xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) (16 * (n / 16)))
  rest : bytesAt t.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
    bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)

/-! ## The whole blocks -/

/-- The data and its length into `dO` and `nO`, and split. -/
theorem ctrSplit_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole) s = some s₁ ∧
      s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧
      Env K W SP s₁ ∧ Frame [wC W] s.mem s₁.mem ∧ slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨sa, runa, hma, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa
      [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax] s =
        some sa ∧
      sa.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) D).writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 n) ∧
      sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s.rd ∧ sa.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hDp, hlen], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hDp, hlen]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  obtain Ea : Env K W SP sa := E.keep (by rw [hbpa, E.ebp]) (by rw [hspa, E.esp]) hrda hwra
  obtain hda : slotv sa.mem W dO = D := by
    rw [hma, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  obtain hna : slotv sa.mem W nO = BitVec.ofNat 32 n := by rw [hma]; exact Mem.readW_writeW_self32 _ _ _
  obtain ⟨s₁, run₁, hbx, hdi, hzf, hbp, hsp, hm₁, hrd₁, hwr₁⟩ := split_ok L Ea hda hna hn32
  obtain cw : ∀ d, 240 ≤ d → d + 4 ≤ 2560 → (wC W).Contains (w64 W + BitVec.ofNat 64 d) 4 := fun d h₁ h₂ =>
    Offset.contains (w64 W) h₁ (by omega_arith) (by decide)
  refine ⟨s₁, runBlock_app_of runa run₁, hbx, hdi, hzf, Ea.keep (by rw [hbp, hbpa]) (by rw [hsp, hspa]) hrd₁ hwr₁,
    ?_, ?_, ?_, by rw [hrd₁, hrda], by rw [hwr₁, hwra]⟩
  · rw [hm₁, hma]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))
  · rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
  · rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _

/-- `Ctrᵢ` at `W + 64`, and the key schedule, the number of rounds and
`W + 64` in `eax`, `ecx`, `edx`, for `vg_aes_ctr32_to`. -/
theorem ctrArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : Lay K W SP) (E₁ : Env K W SP s₁) {R : Nat}
    (hK₁ : slotv s₁.mem W ctxO = K) (hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) {Q : BitVec 32} {b : BitVec 32}
    (hbx : s₁.gpr .ebx = Q) (hdi : s₁.gpr .edi = b) :
    ∃ sc, runBlock isa (([.mov .eax (imm i)] : List Instr) ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s₁.mem sc.mem ∧
      bytesAt sc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧ sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = Q ∧
      sc.gpr .edi = b ∧ sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = s₁.rd ∧ sc.wr = s₁.wr := by
  obtain ⟨sa, runa, hma, haxa, hbxa, hdia, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa [.mov .eax (imm i)] s₁ =
      some sa ∧ sa.mem = s₁.mem ∧ sa.gpr .eax = BitVec.ofNat 32 i ∧ sa.gpr .ebx = Q ∧
      sa.gpr .edi = b ∧ sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s₁.rd ∧ sa.wr = s₁.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs []
    · cregs [hbx]
    · cregs [hdi]
    · cregs [E₁.ebp]
    · cregs [E₁.esp]
    all_goals cmems []
  obtain Ea : Env K W SP sa := E₁.keep (by rw [hbpa, E₁.ebp]) (by rw [hspa, E₁.esp]) hrda hwra
  obtain ⟨sb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hi hi32 haxa
  obtain Eb : Env K W SP sb := Ea.keep (by rw [hgb .ebp (by decide) (by decide)]) (by rw [hgb .esp (by decide) (by decide)])
    hrdb hwrb
  obtain kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv sb.mem W o = slotv s₁.mem W o := fun o h₁ h₂ => by
    show sb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
      (by decide), hma]
  obtain hKb : slotv sb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₁
  obtain hRb' : slotv sb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₁
  obtain ⟨sc, runc, hmc, hax, hcx, hdx, hbxc, hdic, hbpc, hspc, hrdc, hwrc⟩ : ∃ sc, runBlock isa (keyArgs c1O) sb =
      some sc ∧ sc.mem = sb.mem ∧ sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧
      sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = Q ∧ sc.gpr .edi = b ∧
      sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = sb.rd ∧ sc.wr = sb.wr := by
    refine ⟨_, by crun [keyArgs, Eb.ebp, L.aW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hKb]
    · cregs [hRb']
    · cregs [Eb.ebp]
    · cregs [hgb .ebx (by decide) (by decide), hbxa]
    · cregs [hgb .edi (by decide) (by decide), hdia]
    · cregs [Eb.ebp]
    · cregs [Eb.esp]
    all_goals cmems []
  exact ⟨sc, runBlock_app_of (runBlock_app_of runa runb) runc, by rw [hmc, ← hma]; exact fb, by rw [hmc]; exact hcb,
    hax, hcx, hdx, hbxc, hdic, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩

/-- The whole blocks of the data, by one call of `vg_aes_ctr32_to` from `Ctr₁`. -/
theorem ctrWhole_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (.seq (.block (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole))
      (.ite .e (.block []) (.seq (.block (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) s
      (CtrMid K W SP s R nonce D n) := by
  have L := C.lay
  obtain hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain ⟨s₁, run₁, hbx, hdi, hzf, E₁, f₁, hd₁, hn₁, hrd₁, hwr₁⟩ := ctrSplit_ok L E hDp hlen C.hn32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain fr₁ : Frame (ctrR W SP D n) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, fun _ h => h⟩
  obtain dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [wC W], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (C.buf.w.sub_left (Offset.sub_base _ h)).sub_right (Lay.wSub (by decide))
  obtain hrest₁ : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (dD (by omega_arith)) (by omega_arith)
  refine WP.ite (decide (n / 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, hrd₁, hwr₁, fr₁, hd₁, hn₁, ?_, hrest₁⟩
    rw [h0, Nat.mul_zero]; rfl
  · have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
    obtain k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ => C.slot_kept fr₁ h₁ h₂
    obtain ⟨sc, runc, fc, hcc, hax, hcx, hdx, hbxc, hdic, hbpc, hspc, hrdc, hwrc⟩ :=
      ctrArgs_ok L E₁ (by rw [k₁ _ (by decide) (by decide)]; exact hK) (by rw [k₁ _ (by decide) (by decide)]; exact hRo)
        C.h7 C.h13 (C.c0_kept fr₁) (i := 1) (by
          have : 1 ≤ 256 ^ (15 - nonce.length) := Nat.pow_pos (by decide)
          have := C.hn
          omega_arith) (by decide) hbx hdi
    refine WP.seq (WP.of_runBlock ⟨sc, runc, ?_⟩)
    obtain Ec : Env K W SP sc := E₁.keep (by rw [hbpc, E₁.ebp]) (by rw [hspc, E₁.esp]) hrdc hwrc
    obtain rdc : sc.rd = s.rd := by rw [hrdc, hrd₁]
    obtain wrc : sc.wr = s.wr := by rw [hwrc, hwr₁]
    obtain hq := srcBuf ((C.buf.take hb).of_eq rdc wrc)
    obtain hqc : (⟨w64 D, 16 * (n / 16)⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ :=
      (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
    obtain hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * (n / 16)⟩ := C.dk.sub_right (Region.sub_prefix hb)
    obtain hqw : Covers [⟨w64 D, 16 * (n / 16)⟩] sc.wr := by
      rw [wrc]
      intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
    refine WP.mono (ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbxc hdic)
      fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_
    -- What was written.
    obtain fsc : Frame (ctrR W SP D n) s.mem sc.mem :=
      fr₁.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    obtain f₄' : Frame (ctrR W SP D n) sc.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨w64 D, n⟩, by simp, Region.sub_prefix hb⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below SP 60, by simp, fun _ h => h⟩
    obtain k₄ : ∀ o, 240 ≤ o → o + 4 ≤ 384 → slotv s₄.mem W o = slotv sc.mem W o := fun o h₁ h₂ =>
      f₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
        · exact ((C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega_arith))).symm
        · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact (L.stk_w' (by omega_arith)).symm) (by decide)
    obtain kc : ∀ o, 240 ≤ o → o + 4 ≤ 384 → slotv sc.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      fc.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
        (by decide)
    refine ⟨E₄, by rw [rd₄, rdc], by rw [wr₄, wrc], fsc.trans f₄', by rw [k₄ _ (by decide) (by decide),
      kc _ (by decide) (by decide), hd₁], by rw [k₄ _ (by decide) (by decide), kc _ (by decide) (by decide), hn₁],
      ?_, ?_⟩
    · have hDsc : bytesAt sc.mem (w64 D) (16 * (n / 16)) = bytesAt s.mem (w64 D) (16 * (n / 16)) := by
        rw [Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)))
            (by have := C.hn32; omega_arith),
          Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)))
            (by have := C.hn32; omega_arith)]
      obtain hc := Proof.AesCcm.ctr32_ccm (m := sc.mem) (m' := s₄.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
        (D := w64 D) (R := R) (nonce := nonce) (by have := C.h13; omega_arith) (j := 1) (k := n / 16)
        (fun i hi => by
          rw [show Spec.Gcm.blockAt sc.mem (w64 W + BitVec.ofNat 64 64) = Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce 1)
            from by show Spec.Gcm.ofBytes _ = _; rw [hcc]]
          exact Proof.AesCcm.repeat_inc32_ctrBlock C.h7 C.h13 (j := 1) (k := n / 16)
            (by have := C.hn32; omega_arith) (by have := C.hn; omega_arith) i hi) o₄
      rw [hc, C.ciph_kept fsc, hDsc]
    · have sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
        Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega_arith)
      obtain hlt : n % 16 ≤ 2 ^ 64 := by omega_arith
      rw [Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))
        · simpa using Offset.disjoint (w64 D) (d := 16 * (n / 16)) (n := n % 16) (e := 0) (k := 16 * (n / 16))
            (.inr (by omega_arith)) (by have := C.hn32; omega_arith) (by have := C.hn32; omega_arith)
        · exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sR).symm) hlt,
        Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))) hlt, hrest₁]

/-! ## The last bytes -/

/-- `Ctrⱼ`, `j = ⌊n / 16⌋ + 1`, at `W + 64`, the keystream block at `W + 80`
zeroed, and the arguments of `vg_aes_ctr32_to` to encrypt it. -/
theorem ctrTailArgs_ok {K W SP : BitVec 32} {t₀ : State} (L : Lay K W SP) (E₀ : Env K W SP t₀) {R : Nat}
    (hK₀ : slotv t₀.mem W ctxO = K) (hR₀ : slotv t₀.mem W roundsO = BitVec.ofNat 32 R) {n : Nat}
    (hl₀ : slotv t₀.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t₀.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : n / 16 + 1 < 256 ^ (15 - nonce.length)) :
    ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
        keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ = some tc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (n / 16 + 1) ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 80) 16 = Spec.Gcm.zeros 16 ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr := by
  have hbp₀ := E₀.ebp
  have hsp₀ := E₀.esp
  obtain ⟨ta, runa, hma, haxa, hbpa, hspa, hrda, hwra⟩ : ∃ ta, runBlock isa
      [.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] t₀ = some ta ∧ ta.mem = t₀.mem ∧
      ta.gpr .eax = BitVec.ofNat 32 (n / 16 + 1) ∧ ta.gpr .ebp = W ∧ ta.gpr .esp = SP ∧ ta.rd = t₀.rd ∧
      ta.wr = t₀.wr := by
    refine ⟨_, by crun [hbp₀, L.aW, E₀.perm.wR, hl₀], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hl₀, shr4 hn32]; exact (BitVec.ofNat_add _ _).symm
    · cregs [hbp₀]
    · cregs [hsp₀]
    all_goals cmems []
  obtain Ea : Env K W SP ta := E₀.keep (by rw [hbpa, hbp₀]) (by rw [hspa, hsp₀]) hrda hwra
  obtain ⟨tb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hj (by omega_arith) haxa
  obtain hbpb : tb.gpr .ebp = W := by rw [hgb .ebp (by decide) (by decide), hbpa]
  obtain hspb : tb.gpr .esp = SP := by rw [hgb .esp (by decide) (by decide), hspa]
  obtain Eb : Env K W SP tb := Ea.keep (by rw [hbpb, hbpa]) (by rw [hspb, hspa]) hrdb hwrb
  obtain kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv tb.mem W o = slotv t₀.mem W o := fun o h₁ h₂ => by
    show tb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
      (by decide), hma]
  obtain hKb : slotv tb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₀
  obtain hRb' : slotv tb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₀
  obtain hz := zero4_fold tb.mem W 80
  simp only [Nat.reduceAdd] at hz
  obtain ⟨tc, runc, hmc, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ : ∃ tc, runBlock isa
      (zero4 ksO ++ (keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr))) tb =
        some tc ∧ tc.mem = Cmac.zero4 tb.mem (w64 W + BitVec.ofNat 64 80) ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = tb.rd ∧ tc.wr = tb.wr := by
    refine ⟨_, by crun [zero4, keyArgs, hbpb, L.aW, Eb.perm.wW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · cmems [hz]
    · cregs [hKb]
    · cregs [hRb']
    · cregs [hbpb]
    · cregs [hbpb]
    · cregs []
    · cregs [hbpb]
    · cregs [hspb]
    all_goals cmems []
  obtain fz : Frame [⟨w64 W + BitVec.ofNat 64 80, 16⟩] tb.mem tc.mem := by rw [hmc]; exact Cmac.frame_store4 _ _ _ _ _
  refine ⟨tc, by
      simp only [List.append_assoc]
      exact runBlock_app_of runa (runBlock_app_of runb runc), ?_, ?_, by rw [hmc, zero4_bytes'],
    hax, hcx, hdx, hbx, hdi, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩
  · rw [← hma]
    exact (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩).trans
      (fz.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩)
  · rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hcb]

/-- The arguments of the XOR of the last bytes with the keystream block. -/
theorem xorArgs_ok {K W SP : BitVec 32} {td : State} (L : Lay K W SP) (Ed : Env K W SP td) {P : BitVec 32} {t : Nat}
    (hdd : slotv td.mem W dO = P) (hnd : slotv td.mem W nO = BitVec.ofNat 32 t) :
    ∃ te, runBlock isa
      [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)] td = some te ∧
      te.mem = td.mem ∧ te.gpr .edi = P ∧ te.gpr .edx = W + BitVec.ofNat 32 80 ∧
      te.gpr .ecx = BitVec.ofNat 32 t ∧ te.gpr .ebp = W ∧ te.gpr .esp = SP ∧ te.rd = td.rd ∧ te.wr = td.wr := by
  have hbpd := Ed.ebp
  refine ⟨_, by crun [hbpd, L.aW, Ed.perm.wR, hdd, hnd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hdd]
  · cregs [hbpd]
  · cregs [hnd]
  · cregs [hbpd]
  · cregs [Ed.esp]
  all_goals cmems []

/-- The last `n mod 16` bytes, with `CIPH_K(Ctr₁₊ₙ/₁₆)`, after the whole blocks. -/
theorem ctrTail_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : CtrCtx K W SP s R nonce D n) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) {t : State}
    (I : CtrMid K W SP s R nonce D n t) :
    WP isa (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) t
      fun t' => Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR W SP D n) s.mem t'.mem ∧
        bytesAt t'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) := by
  have L := C.lay
  have E := I.env
  have hn32 := C.hn32
  obtain hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    C.slot_kept I.frame h₁ h₂
  obtain ⟨t₀, run₀, hm₀, hzf, hbp₀, hsp₀, hrd₀, hwr₀⟩ := testN_ok L E (r := n % 16) (by omega_arith) I.nO
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  obtain E₀ : Env K W SP t₀ := E.keep (by rw [hbp₀, E.ebp]) (by rw [hsp₀, E.esp]) hrd₀ hwr₀
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, E₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega_arith] at hd
    rw [hm₀, hd]
  · have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
    obtain hj : n / 16 + 1 < 256 ^ (15 - nonce.length) := by have := C.hn; omega_arith
    obtain ⟨tc, runc, ft, hcc, hz80, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ :=
      ctrTailArgs_ok L E₀ (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hK)
        (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hRo) (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hlen)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) hj
    refine WP.seq (WP.of_runBlock ⟨tc, runc, ?_⟩)
    obtain Ec : Env K W SP tc := E₀.keep (by rw [hbpc, hbp₀]) (by rw [hspc, hsp₀]) hrdc hwrc
    -- The keystream block.
    obtain hq := srcW (s := tc) L Ec.perm (t := 80) (k := 16 * 1) (by decide)
    obtain a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
    obtain hqc : (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ := by
      rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    obtain hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ := by
      rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide))
    obtain hqw : Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr := by rw [a80]; exact Ec.perm.wC (by decide)
    refine WP.seq (WP.mono (ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbx hdi)
      fun td ⟨Ed, rdd, wrd, _, fd, od⟩ => ?_)
    -- What was written before the XOR.
    have fd' := fd
    rw [a80] at fd'
    obtain fbd : Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60]
        t.mem td.mem := by
      rw [← hm₀]
      refine (ft.sub fun r hr => ?_).trans (fd'.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨below SP 60, by simp, fun _ h => h⟩
    obtain fR : Frame (ctrR W SP D n) s.mem td.mem := I.frame.trans (fbd.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    obtain kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
      fbd.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
        · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
        · exact (L.stk_w' (by omega_arith)).symm) (by decide)
    have hbpd : td.gpr .ebp = W := Ed.ebp
    -- The XOR.
    obtain ⟨te, rune, hme, hdie, hdxe, hcxe, hbpe, hspe, hrde, hwre⟩ :=
      xorArgs_ok L Ed (P := D + BitVec.ofNat 32 (16 * (n / 16))) (t := n % 16) (by rw [kd _ (by decide) (by decide)]; exact I.dO)
        (by rw [kd _ (by decide) (by decide)]; exact I.nO)
    refine WP.seq (WP.of_runBlock ⟨te, rune, ?_⟩)
    obtain rde : te.rd = s.rd := by rw [hrde, rdd, hrdc, hrd₀, I.rd]
    obtain wre : te.wr = s.wr := by rw [hwre, wrd, hwrc, hwr₀, I.wr]
    obtain hw : D.toNat + 16 * (n / 16) < 2 ^ 32 := by have := C.buf.wrap; omega_arith
    obtain pT : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) := Buf.ptr hw
    obtain sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega_arith)
    obtain xp : XorPre te (W + BitVec.ofNat 32 80) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨hdxe, hdie, hcxe, by omega_arith, by omega_arith, by rw [L.nW (by decide)]; have := L.fw; omega_arith,
        by rw [toNat_add32 hw]; have := C.buf.wrap; omega_arith, ?_, ?_, ?_⟩
      · rw [a80]; exact covers_left (Perm.wC (Ed.perm.of_eq hrde hwre) (d := 80) (n := n % 16) (by omega_arith))
      · rw [pT, wre]; exact covers_off C.dw (by omega_arith) (by have := C.buf.lt; omega_arith)
      · rw [a80, pT]; exact ((C.buf.w.sub_left sR).sub_right (Lay.wSub (d := 80) (n := n % 16) (by omega_arith))).symm
    refine WP.mono (xorLoop_ok te xp) fun tf P => ?_
    obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes te.mem (w64 (D + BitVec.ofNat 32 (16 * (n / 16))))
        (w64 (W + BitVec.ofNat 32 80)) (n % 16) := ⟨_, rfl⟩
    have hm₄ := P.mem
    rw [← hxs] at hm₄
    obtain hxl : xs.length = n % 16 := by simp [hxs, xorBytes, length_bytesAt]
    obtain fw : Frame [⟨w64 D, n⟩] te.mem tf.mem := by
      rw [hm₄, pT]
      exact writeBytes_frame _ _ _ (by
        rw [hxl]; exact Offset.contains_base (w64 D) (show 16 * (n / 16) + n % 16 ≤ n by omega_arith)
          (by have := C.buf.lt; omega_arith))
    refine ⟨E.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hbpe, E.ebp])
        (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hspe, E.esp])
        (by rw [P.rd, rde, I.rd]) (by rw [P.wr, wre, I.wr]), by rw [P.rd, rde], by rw [P.wr, wre], ?_, ?_⟩
    · rw [← hme] at fR
      exact fR.trans (fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    · -- The bytes.
      obtain dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 64, 32⟩ : Region),
          ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
        intro a l hl r hr
        obtain sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sA).symm
      obtain h₁ : bytesAt te.mem (w64 D) (16 * (n / 16)) = bytesAt t.mem (w64 D) (16 * (n / 16)) := by
        rw [hme]
        have := Proof.AesGcm.X86.bytesAt_frame fbd (dD (a := 0) (l := 16 * (n / 16)) (by omega_arith)) (by omega_arith)
        rwa [BitVec.add_zero] at this
      obtain h₂ : bytesAt te.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
        rw [hme, Proof.AesGcm.X86.bytesAt_frame fbd (dD (by omega_arith)) (by omega_arith), I.rest]
      obtain hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem (w64 K) R) := fun x => Proof.Cmac.aesWith_length _ _ x
      obtain fRc : Frame (ctrR W SP D n) s.mem tc.mem := I.frame.trans (by
        rw [← hm₀]
        exact ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
      obtain hks : bytesAt te.mem (w64 W + BitVec.ofNat 64 80) 16 =
          Spec.Ccm.ctxCiph s.mem (w64 K) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1)) := by
        obtain hx := Proof.AesCcm.ctr32_ccm (m := tc.mem) (m' := td.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
          (D := w64 (W + BitVec.ofNat 32 80)) (R := R) (nonce := nonce) (by have := C.h13; omega_arith) (k := 1)
          (j := n / 16 + 1) (fun i hi => by
            rw [show i = 0 by omega_arith, Nat.add_zero]
            show Spec.Gcm.ofBytes _ = _
            rw [hcc]) od
        rw [Nat.mul_one, a80] at hx
        rw [hme, hx, hz80, C.ciph_kept fRc]
        exact Proof.AesCcm.xorFrom_zeros hBC _ _
      obtain ht := Proof.AesCcm.xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce (n / 16 + 1)
        (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [length_bytesAt]; omega_arith)
      rw [length_bytesAt, hBC] at ht
      obtain ht' := ht.resolve_right (by omega_arith)
      rw [hm₄, pT, bytesAt_writeBytes_at te.mem (w64 D) xs (by rw [hxl]; omega_arith) (by have := C.buf.lt; omega_arith),
        List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_arith), List.append_nil,
        ← Proof.AesCcm.bytesAt_prefix te.mem (w64 D) hb, h₁, I.done, hxs, xorBytes, pT, a80, h₂,
        Proof.AesCcm.bytesAt_prefix te.mem (w64 W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega_arith), hks, ht']
      conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
      rw [Proof.Cmac.Stream.bytesAt_append, Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _),
        Nat.add_comm 1 (n / 16)]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (ctr v.callee) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) :=
  seq_assoc (WP.seq (WP.mono (ctrWhole_ok v C E hK hRo hDp hlen) fun _ I => ctrTail_ok v C hK hRo hlen I))


end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.Top`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Args`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Contract`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as an eleventh argument, `work`, against the shared contracts
with it appended (`Proof/AesCcm/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); the calls push their
arguments and return addresses below `esp`: 60 bytes for a call of
`vg_cmac_aes_update` (its own 28 and the 32 of its calls of `vg_aes_ctr32_to`),
which no buffer overlaps, nor the return address.
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The buffers of `vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ccm_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (workR s) ∧ (schR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (tagR s) ∧ (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧
  (tagR s).Disjoint (workR s) ∧ (tagR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (tagR s) ∧ (retR s).Disjoint (workR s) ∧
  (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (schR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (tagR s) ∧ (stackR s).Disjoint (workR s) ∧
  (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
  (arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧
  valid (arg s 9).toNat (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, arg s₁ i = arg s₂ i

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
    (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

/-- `vg_aes_ccm_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) then [] else
  [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = zeros (arg s 7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`).
Between the entry and the exit, the pieces only write the parts of `W` in
`mutR`, the stack below `SP` and the data, so they keep the slots, the saved
registers, the key schedule, the nonce and the associated data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv argsR argsR_eq below_eq SavedAt savedR ofNat_toNat32)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : Buf W SP s D n
  tag : Buf W SP s T tl
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩
  nd : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 D, n⟩
  ad : (⟨w64 A, al⟩ : Region).Disjoint ⟨w64 D, n⟩
  td : (⟨w64 T, tl⟩ : Region).Disjoint ⟨w64 D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  al32 : al < 2 ^ 32
  n32 : n < 2 ^ 32
  retW : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, tl⟩
  args : Covers [argsR SP 11] (s.rd ++ s.wr)
  argsW : (argsR SP 11).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32

/-- `Args`, from what both preconditions say, with the key schedule, the
nonce, the associated data and the tag readable and the data, the working
space and the arguments writable. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (mrd : ∀ r ∈ [schR s, nonceR s, aadR s, tagR s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  simp only [oneLay, stackR] at h
  obtain ⟨d1, d2, _, d4, d5, _, d7, d8, _, d10, d11, _, d13, _, d15, _, _, _, d19, d20, d21, _,
    b1, b2, b3, b4, b5, b6, _, f1, f2, f3, f4, f5, f6, hsp, hfa, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  rw [show (60 : Addr) = BitVec.ofNat 64 60 from rfl, below_eq hsp] at b1 b2 b3 b4 b5 b6
  exact {
    lay := ⟨f1, f6, hsp, d2, b1, b6⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), f2, d5, b2⟩
    aad := ⟨mrd _ (by simp), f3, d8, b3⟩
    data := ⟨Proof.AesGcm.X86.covers_left (mwr _ (by simp)), f4, d11, b4⟩
    tag := ⟨mrd _ (by simp), f5, d13, b5⟩
    dw := mwr _ (by simp)
    dk := d1
    nd := d4
    ad := d7
    td := d10.symm
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    al32 := BitVec.isLt _
    n32 := BitVec.isLt _
    retW := d21
    retD := d19
    retT := d20
    args := by rw [argsR_eq]; exact Proof.AesGcm.X86.covers_left (mwr _ (by simp))
    argsW := by rw [argsR_eq]; exact d15.symm
    fa := by omega_using [hfa] }

theorem args_of_seal {s : State} (h : sealPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine args_of_lay hl (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)

/-- In `seal`, the tag is writable. -/
theorem tag_wr {s : State} (h : sealPre s) : Covers [tagR s] s.wr :=
  covers_of_mem (by rw [h.2.1]; simp)

theorem args_of_open {s : State} (h : openPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  exact args_of_lay hl (fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)))
    (fun r hr => covers_of_mem (by rw [hwr]; exact hr))

/-! ## What the pieces keep -/

section
variable {K W SP D : BitVec 32} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {s₀ : State} (S : SavedAt m W s₀) : SavedAt m' W s₀ :=
  S.frame hf fun r hr => (kept_mut L hD (d := 128) (k := 16) (.inl ⟨by decide, by decide⟩) r hr)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame (mutR W SP D n) m m') :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    (hPD : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega_using [this])

end

/-- Every region of `rs` is part of one of `mutR`. -/
abbrev InMut (W SP D : BitVec 32) (n : Nat) (rs : List Region) : Prop :=
  ∀ r ∈ rs, ∃ r' ∈ mutR W SP D n, Region.Sub r r'

theorem inMut_macR (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) : InMut W SP D n (macR W SP y) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩

theorem inMut_ctrR (W SP D : BitVec 32) (n : Nat) : InMut W SP D n (ctrR W SP D n) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem frame_toMut {W SP D : BitVec 32} {n : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : InMut W SP D n rs) : Frame (mutR W SP D n) m m' := hf.sub h

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the start of both functions

Untrusted: everything here is checked by Lean. `seal` and `open` both start
with the entry and `Ctr₀` (`start_ok`); after them, the slots hold the
arguments and `W + 48` holds `Ctr₀`, and the key schedule, the nonce, the
associated data, the data, the received tag and the return address are as
they were (`Started`). The pieces after them write only `mutR`, which keeps
all of that but the data (`Started.mut`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt ret_below ofNat_toNat32)

/-- After the entry and `Ctr₀`. -/
structure Started (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s' : State) : Prop where
  env : Env K W SP s'
  slots : Slots W K R N A D T nl al n tl s'.mem
  saved : SavedAt s'.mem W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  c0 : bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0
  ciph : Spec.Ccm.ctxCiph s'.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R
  aadB : bytesAt s'.mem (w64 A) al = bytesAt s.mem (w64 A) al
  dataB : bytesAt s'.mem (w64 D) n = bytesAt s.mem (w64 D) n
  tagB : bytesAt s'.mem (w64 T) tl = bytesAt s.mem (w64 T) tl
  ret : s'.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32

/-- The entry and `Ctr₀`. -/
theorem start_ok {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) :
    WP isa (.seq ccmEntry ctrs) s (Started s K W SP N A D T R nl al n tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok a10 Ar.perm.w (by rw [hsp]; exact Ar.args) (by rw [hsp]; exact Ar.argsW)
    (by rw [hsp]; exact Ar.fa) L.fw) fun s₁ E₀ => ?_)
  have E₁ : Env K W SP s₁ := ⟨E₀.ebp, by rw [E₀.esp, hsp], Ar.perm.of_eq E₀.rd E₀.wr⟩
  have sl : ∀ p ∈ entryPs, slotv s₁.mem W p.2 = arg s p.1 := E₀.slots
  have S₁ : Slots W K R N A D T nl al n tl s₁.mem :=
    ⟨by rw [sl (0, ctxO) (by simp), a0], by rw [sl (1, roundsO) (by simp), a1],
      by rw [sl (2, nonceO) (by simp), a2], by rw [sl (3, nlenO) (by simp), a3],
      by rw [sl (4, aadO) (by simp), a4], by rw [sl (5, alenO) (by simp), a5],
      by rw [sl (6, dataO) (by simp), a6], by rw [sl (7, lenO) (by simp), a7],
      by rw [sl (9, Impl.AesGcm.X86.tglO) (by simp), a9], by rw [sl (8, Impl.AesGcm.X86.tpO) (by simp), a8]⟩
  have fE := E₀.frame
  have bE : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have cE : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    ctxCiph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.mono (ctrs_ok L E₁ S₁.nonce S₁.nlen (Ar.nonce.of_eq E₀.rd E₀.wr) Ar.h7 Ar.h13)
    fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_
  have f₂' : Frame (mutR W SP D n) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  have b₂ : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₂.mem (w64 P) len = bytesAt s₁.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  refine ⟨E₂, slots_mut L Ar.data.w f₂' S₁, saved_mut L Ar.data.w f₂' E₀.saved, by rw [rd₂, E₀.rd],
    by rw [wr₂, E₀.wr], by rw [c₂, bE Ar.nonce], ?_, by rw [b₂ Ar.aad, bE Ar.aad], by rw [b₂ Ar.data, bE Ar.data],
    ?_, ?_⟩
  · rw [ctxCiph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb, cE]
  · rw [b₂ Ar.tag, bE Ar.tag]
  · rw [Proof.AesGcm.X86.ret_kept f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide))),
      Proof.AesGcm.X86.ret_kept fE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide)))]

/-- What the pieces after the start keep. -/
theorem Started.mut {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) {s₁ : State} (St : Started s K W SP N A D T R nl al n tl s₁) {m : Mem}
    (hf : Frame (mutR W SP D n) s₁.mem m) :
    Slots W K R N A D T nl al n tl m ∧ SavedAt m W s ∧
      Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R ∧
      bytesAt m (w64 A) al = bytesAt s.mem (w64 A) al ∧ m.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
  have L := Ar.lay
  refine ⟨slots_mut L Ar.data.w hf St.slots, saved_mut L Ar.data.w hf St.saved,
    by rw [ciph_mut L Ar.dk Ar.rounds hf, St.ciph], by rw [buf_mut Ar.aad Ar.ad hf, St.aadB], ?_⟩
  rw [Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ar.retW.sub_right (Region.sub_prefix (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact ret_below L.sp
    · exact Ar.retD), St.ret]

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.Mask`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: masking the data, and the tag copied out

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`: the data if `ok = 1`, zeros if `ok = 0` (`mask_ok`).
`tagOut` copies the first `tag_len` bytes of the tag at `W` to `tag`
(`tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop maskWords tglO tpO rO)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv in_of_covers covers_left succ_ofNat32 add_zero32 pred_count pred_beq bytesAt_succ
  maskWords_ok
  length_bytesAt and_self_beq32 WEnv padLoop_ok zero4_fold toNat_ofNat32 LoopPre CopyPost copyLoop_ok CT)

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : Env K W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.seq (WP.mono (maskWords_ok s₂ hn32 (by omega_arith) di₂ cx₂ bx₂ (by rw [rd₂, wr₂]; exact hD.rd)
    (by rw [wr₂]; exact hDw)) fun s₃ ⟨j₀, hj₀, hlt₀, di₃, cx₃, m₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨s₄, run₄, g₄, m₄, zf₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa [.alu .test .ecx (.reg .ecx)] s₃ = some s₄ ∧
      s₄.gpr = s₃.gpr ∧ s₄.mem = s₃.mem ∧ s₄.zf = some (decide (n - j₀ = 0)) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · cmems [cx₃]; rw [and_self_beq32 (by omega_arith)]
    · rfl
    · rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain mem₄ : s₄.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j₀ else zeros j₀) := by
    rw [m₄, m₃, m₂]; rfl
  obtain gg₄ : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s₄.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₄, g₃ r h₁ h₂ h₃]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂]
  refine WP.ite (decide (n - j₀ = 0)) (eval_e zf₄) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · obtain rfl : j₀ = n := by have := of_decide_eq_true hb; omega_arith
    exact ⟨⟨by rw [gg₄ _ (by decide) (by decide) (by decide), bp₂],
      by rw [gg₄ _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq rd₄' wr₄'⟩, rd₄', wr₄', mem₄⟩
  obtain hj₁ : j₀ < n := by have := of_decide_eq_false hb; omega_arith
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - j₀) _
    ⟨j₀, rfl, hj₁, by rw [g₄, di₃], by rw [g₄, cx₃], mem₄, gg₄, rd₄', wr₄'⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega_arith))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega_arith))
    (by rw [wr]; exact in_of_covers hDw hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  have hmem : t'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : Env K W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The tag copied out -/

/-- `tagOut`: the first `t` bytes at `W` written to `tag` (kept at `W + tpO`). -/
theorem tagOut_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {T : BitVec 32} {t : Nat}
    (hv : slotv s.mem W tglO = BitVec.ofNat 32 t) (hT : slotv s.mem W tpO = T) (ht1 : 1 ≤ t) (ht : t ≤ 16)
    (Tb : Buf W SP s T t) (tw : Covers [⟨w64 T, t⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = writeBytes s.mem (w64 T) (bytesAt s.mem (w64 W) t) ∧ Env K W SP s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tpO), .mov .ecx (slot tglO)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .edi = W ∧ s₁.gpr .edx = T ∧ s₁.gpr .ecx = BitVec.ofNat 32 t ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems []
    · cregs [E.ebp]
    · cregs [hT]
    · cregs [hv]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ W T t := ⟨hdi, hdx, hcx, ht1, by omega_arith, by have := L.fw; omega_arith, Tb.wrap,
    by rw [hrd₁, hwr₁]; simpa using covers_left (E.perm.wC (d := 0) (n := t) (by omega_arith)),
    by rw [hwr₁]; exact tw, (Tb.w.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, hm₁], ⟨?_, ?_, E.perm.of_eq ?_ ?_⟩, ?_, ?_⟩
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hbp]
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hsp]
  all_goals first | rw [P.rd, hrd₁] | rw [P.wr, hwr₁]

theorem tagOut_ct {K W SP T : BitVec 32} {t : Nat} {I : State → Prop} (L : Lay K W SP)
    (h : ∀ s, I s → Env K W SP s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t ∧ slotv s.mem W tpO = T) :
    CT I tagOut := by
  refine CT.seq (J := fun s => s.gpr .edi = W ∧ s.gpr .edx = T ∧ s.gpr .ecx = BitVec.ofNat 32 t)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (Proof.AesGcm.X86.copyLoop_ct fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2])
  obtain ⟨E, hv, hT⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], by cregs [E.ebp], by cregs [hT], by cregs [hv]⟩

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is the start (the
entry and `Ctr₀`, `start_ok`), the MAC of the payload at `W` (`mac_ok`),
encrypted (`tag_ok`), counter mode over the data (`ctr_ok`), the tag copied
to `tag` (`tagOut_ok`) and the exit (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left writeBytes_frame'
  bytesAt_writeBytes_self)

/-- What `tag y` writes, in `mutR`. -/
theorem inMut_tag (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) :
    InMut W SP D n [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 60] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack keeps its bytes across a frame of
parts of `W` and the stack. -/
theorem buf_kept' {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 60) {m m' : Mem}
    (hf : Frame rs m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hP.w.sub_right h
    · exact hP.stk.symm) (by have := hP.lt; omega_using [this])

/-- `Ctr₀` is kept by a frame of parts of `W` apart from it. -/
theorem c0_kept {W : BitVec 32} {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) {m m' : Mem} (hf : Frame rs m m') :
    bytesAt m' (w64 W + BitVec.ofNat 64 48) 16 = bytesAt m (w64 W + BitVec.ofNat 64 48) 16 :=
  Proof.AesGcm.X86.bytesAt_frame hf hrs (by decide)

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) (tw : Covers [⟨w64 T, tl⟩] s.wr) :
    WP isa («seal» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)
        (bytesAt s.mem (w64 A) al) = (bytesAt s'.mem (w64 D) n, bytesAt s'.mem (w64 T) tl) := by
  have L := Ar.lay
  obtain hnl := length_bytesAt s.mem (w64 N) nl
  obtain h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  refine seq_assoc (WP.seq (WP.mono (start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- The MAC.
  refine WP.seq (WP.mono (mac_ok v L St.env Ar.rounds St.slots hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 St.c0 (y := 0) (.inl rfl) (Ar.aad.of_eq St.rd St.wr) (Ar.data.of_eq St.rd St.wr)) fun s₃ A₃ => ?_)
  obtain f₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frame_toMut A₃.frame (inMut_macR W SP D n (.inl rfl))
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₃
  obtain hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₃.frame, St.c0]
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L A₃.env Ar.rounds S₃.ctx S₃.rounds h7' h13' hc₃ (y := 0) (.inl rfl))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  obtain f₂₄ : Frame (mutR W SP D n) s₂.mem s₄.mem := f₃.trans (frame_toMut f₄ (inMut_tag W SP D n (.inl rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  obtain hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) f₄, hc₃]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, A₃.rd, St.rd]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, A₃.wr, St.wr]
  obtain hD₄ : bytesAt s₄.mem (w64 D) n = bytesAt s.mem (w64 D) n := by
    rw [buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₄,
      buf_kept Ar.data (y := 0) (by decide) A₃.frame, St.dataB]
  -- Counter mode.
  obtain C₄ : CtrCtx K W SP s₄ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, hc₄, Ar.data.of_eq rd₄' wr₄',
      by rw [wr₄']; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v C₄ E₄ S₄.ctx S₄.rounds S₄.data S₄.len) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  obtain f₂₅ : Frame (mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (frame_toMut f₅ (inMut_ctrR W SP D n))
  obtain ⟨S₅, sv₅, ci₅, -, rt₅⟩ := St.mut Ar f₂₅
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄']
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄']
  -- The tag copied out.
  refine WP.seq (WP.mono (tagOut_ok L E₅ S₅.tl S₅.tp (by have := Ar.t4; omega_using [this]) Ar.t16
    (Ar.tag.of_eq rd₅' wr₅') (by rw [wr₅']; exact tw)) fun s₆ ⟨m₆', E₆, rd₆, wr₆⟩ => ?_)
  obtain hTl : tl < 2 ^ 64 := by have := Ar.t16; omega_using [this]
  obtain fT : Frame [⟨w64 T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆']; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain tW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 T, tl⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.tag.w.sub_right (Lay.wSub hk)).symm
  obtain sv₆ : SavedAt s₆.mem W s := sv₅.frame fT (tW (by decide))
  obtain rt₆ : s₆.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT), rt₅]
  -- The exit.
  refine WP.mono (exit_ok (W := W) (s₀ := s) E₆.ebp (by rw [E₆.esp, hsp])
    (by rw [rd₆, wr₆, rd₅', wr₅']; exact covers_left Ar.perm.w) L.fw sv₆ (by rw [hsp]; exact rt₆))
    fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  obtain ci₄ : Spec.Ccm.ctxCiph s₄.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₂₄).2.2.1
  obtain ci₃ : Spec.Ccm.ctxCiph s₃.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₃).2.2.1
  obtain hW₅ : bytesAt s₅.mem (w64 W) tl = bytesAt s₄.mem (w64 W) tl := by
    have ht := Ar.t16
    exact Proof.AesGcm.X86.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by omega_using [ht])) (by omega_using [ht]) (by decide)
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 240) (k := 2320) (.inl (by omega_using [ht])) (by omega_using [ht])
          (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by omega_using [ht]))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by omega_using [ht]))).symm) (by omega_using [hTl])
  obtain e0 : w64 W + BitVec.ofNat 64 0 = w64 W := BitVec.add_zero _
  have o₃ := A₃.out
  rw [e0] at h₄ o₃
  obtain hY := congrArg List.length o₃
  rw [length_bytesAt] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [m₇, Proof.AesGcm.X86.bytesAt_frame fT (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by have := Ar.data.lt; omega_using [this]), h₅, ci₄, hD₄, crypt_eq (hBC _)]
  · have hT₇ : bytesAt s₇.mem (w64 T) tl = bytesAt s₅.mem (w64 W) tl := by
      have := bytesAt_writeBytes_self s₅.mem (w64 T) (bytesAt s₅.mem (w64 W) tl) (by rw [length_bytesAt]; omega_using [hTl])
      rw [length_bytesAt] at this
      rw [m₇, m₆', this]
    rw [hT₇, hW₅, Proof.AesCcm.bytesAt_prefix s₄.mem (w64 W) Ar.t16, h₄,
      take_xorFrom_zero (hBC _) _ (by rw [length_bytesAt]) Ar.t16, o₃, ci₃,
      ← Proof.AesCcm.mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega_using [this]), St.ciph, St.aadB, St.dataB]

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.CryptCT`, which only this module used -/

section

/-!
# AES-CCM on x86: counter mode in constant time

Untrusted: everything here is checked by Lean. `ctr` branches on the length
of the data and addresses memory by `W` and the data's address, all public
(`ctr_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What `ctr` starts from. -/
structure CtrPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n
  c : ∃ nonce, CtrCtx K W SP s R nonce D n

theorem ctrWhole_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (CtrPre K W SP R D n) (.seq (.block (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole))
      (.ite .e (.block []) (.seq (.block (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) := by
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => ctrSplit_ok L hs.env hs.data hs.len hn32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
  have blk : ∀ s₁ : State, (∃ s, CtrPre K W SP R D n s ∧ s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ Env K W SP s₁ ∧ Frame [wC W] s.mem s₁.mem ∧
      slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧ slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      ∃ sc, runBlock isa (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
        sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧ sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = D ∧
        sc.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = s₁.rd ∧
        sc.wr = s₁.wr := fun s₁ ⟨s, hs, hbx, hdi, _, E₁, f₁, _, _, rd, wr⟩ => by
    obtain ⟨nonce, C⟩ := hs.c
    have fr₁ : Frame (ctrR W SP D n) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, fun _ h => h⟩
    obtain ⟨sc, run, -, -, rest⟩ := ctrArgs_ok L E₁
      (by rw [C.slot_kept fr₁ (by decide) (by decide)]; exact hs.ctx)
      (by rw [C.slot_kept fr₁ (by decide) (by decide)]; exact hs.rounds) C.h7 C.h13 (C.c0_kept fr₁) (i := 1)
      (by
        have : 1 ≤ 256 ^ (15 - nonce.length) := Nat.pow_pos (by decide)
        have := C.hn
        omega_using [h0, this]) (by decide) hbx hdi
    exact ⟨sc, run, rest⟩
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, E₁, _⟩ => E₁.ebp) (by taint_decide) blk ?_
  refine ctrCall_ct v L hR (c := 64) (Q := D) (n := n / 16) (by decide)
    fun sc ⟨s₁, ⟨s, hs, _, _, _, E₁, _, _, _, rd₁, wr₁⟩, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => ?_
  obtain ⟨nonce, C⟩ := hs.c
  have rdc : sc.rd = s.rd := by rw [rd, rd₁]
  have wrc : sc.wr = s.wr := by rw [wr, wr₁]
  refine ⟨⟨bp, sp, hs.env.perm.of_eq rdc wrc⟩, srcBuf ((C.buf.take hb).of_eq rdc wrc), ?_,
    (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)), C.dk.sub_right (Region.sub_prefix hb),
    ax, cx, dx, bx, di⟩
  rw [wrc]
  intro a k ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hc]⟩

/-- What `ctr`'s last bytes start from. -/
abbrev CtrTailPre (K W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (t : State) : Prop :=
  ∃ s, CtrPre K W SP R D n s ∧ ∃ nonce, CtrCtx K W SP s R nonce D n ∧ CtrMid K W SP s R nonce D n t

theorem ctrTail_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) :
    CT (CtrTailPre K W SP R D n) (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) := by
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, I⟩ => I.env.ebp) (by taint_decide)
    (fun t ⟨_, _, _, _, I⟩ => testN_ok L I.env (r := n % 16) (by omega_using []) I.nO) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun _ ⟨_, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun hf => ?_
  have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
  -- The arguments of the call making the keystream block.
  have blk : ∀ t₀ : State, (∃ t, CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
      t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) →
      ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++
          zero4 ksO ++ keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ =
          some tc ∧
        Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
        tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
        tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
        tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr :=
    fun t₀ ⟨t, ⟨s, hs, nonce, C, I⟩, hm₀, _, hbp₀, hsp₀, hrd₀, hwr₀⟩ => by
      have E₀ : Env K W SP t₀ := I.env.keep (by rw [hbp₀, I.env.ebp]) (by rw [hsp₀, I.env.esp]) hrd₀ hwr₀
      have k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t₀.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
        rw [hm₀]; exact C.slot_kept I.frame h₁ h₂
      obtain ⟨tc, run, ft, -, -, rest⟩ := ctrTailArgs_ok L E₀ (by rw [k₀ _ (by decide) (by decide)]; exact hs.ctx)
        (by rw [k₀ _ (by decide) (by decide)]; exact hs.rounds) (by rw [k₀ _ (by decide) (by decide)]; exact hs.len)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) (by have := C.hn; omega_using [h0, this])
      exact ⟨tc, run, ft, rest⟩
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, hbp, _⟩ => hbp) (by taint_decide) blk ?_
  -- The call.
  have a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
  have pre : ∀ tc : State, (∃ t₀ : State, (∃ t, CtrTailPre K W SP R D n t ∧ t₀.mem = t.mem ∧
      t₀.zf = some (decide (n % 16 = 0)) ∧ t₀.gpr .ebp = W ∧ t₀.gpr .esp = SP ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr) →
      Env K W SP tc ∧ Src W SP tc (W + BitVec.ofNat 32 80) (16 * 1) ∧
      Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr ∧
      (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 :=
    fun tc ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, _, _, _, _, hrd₀, hwr₀⟩, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have Ec : Env K W SP tc := ⟨bp, sp, I.env.perm.of_eq (by rw [rd, hrd₀]) (by rw [wr, hwr₀])⟩
      exact ⟨Ec, srcW L Ec.perm (by decide), by rw [a80]; exact Ec.perm.wC (by decide),
        by rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide),
        by rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide)), ax, cx, dx, bx, di⟩
  refine CT.seq (J := fun td => Env K W SP td ∧ slotv td.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv td.mem W nO = BitVec.ofNat 32 (n % 16))
    (ctrCall_ct v L hR (c := 64) (by decide) pre) (fun tc h => ?_) ?_
  · obtain ⟨Ec, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩ := pre tc h
    obtain ⟨t₀, ⟨t, ⟨_, _, _, _, I⟩, hm₀, _⟩, ft, _⟩ := h
    refine WP.mono (ctrCall_ok v L Ec hR (c := 64) (by decide) hq hqc hqk hqw ax cx dx bx di)
      fun td ⟨Ed, _, _, _, fd, _⟩ => ?_
    have fd' := fd
    rw [a80] at fd'
    have kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ => by
      rw [← hm₀]
      exact ((ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
        (fd'.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
          · exact ⟨⟨w64 W + BitVec.ofNat 64 384, 2048⟩, by simp, fun _ h => h⟩
          · exact ⟨below SP 60, by simp, fun _ h => h⟩) :
          Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 60]
            t₀.mem td.mem).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
          · exact (L.stk_w' (by omega_using [h₂])).symm) (by decide)
    exact ⟨Ed, by rw [kd _ (by decide) (by decide)]; exact I.dO, by rw [kd _ (by decide) (by decide)]; exact I.nO⟩
  -- The XOR.
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)
    (fun td hd => xorArgs_ok L hd.1 hd.2.1 hd.2.2) ?_
  exact Proof.AesGcm.X86.xorLoop_ct (pin3 fun _ ⟨_, _, _, hdi, hdx, hcx, _⟩ => ⟨hdi, hdx, hcx⟩)

theorem ctr_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32) : CT (CtrPre K W SP R D n) (ctr v.callee) :=
  RelCT.assoc (CT.seq (J := CtrTailPre K W SP R D n) (ctrWhole_ct v L hR hn32)
    (fun s hs => by
      obtain ⟨nonce, C⟩ := hs.c
      exact WP.mono (ctrWhole_ok v C hs.env hs.ctx hs.rounds hs.data hs.len) fun t I => ⟨s, hs, nonce, C, I⟩)
    (ctrTail_ct v L hR hn32))

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.MacCT`, which only this module used -/

section

/-!
# AES-CCM on x86: the CBC-MAC and the tag in constant time

Untrusted: everything here is checked by Lean. `b0`, `mac` and `tag` branch
and address memory only by the slots, the lengths and `W`: all public
(`b0_ct`, `mac_ct`, `tag_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (CT w64 slotv)

/-- What the MAC's pieces keep: the slots, and the associated data and the
data readable. -/
structure MacMid (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  slots : Slots W K R N A D T nl al n tl s.mem
  aad : Buf W SP s A al
  data : Buf W SP s D n

theorem MacMid.next {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} {s : State}
    (h : MacMid K W SP R N A D T nl al n tl s) {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s')
    (f : Frame (macR W SP y) s.mem s'.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    MacMid K W SP R N A D T nl al n tl s' :=
  ⟨E, h.slots.macR L hy f, h.aad.of_eq rd wr, h.data.of_eq rd wr⟩

/-- What `b0` and `mac` start from: also `Ctr₀` at `W + 48`. -/
structure MacPre (K W SP : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (s : State) : Prop
    extends MacMid K W SP R N A D T nl al n tl s where
  c0 : ∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Blk_ct {y : Nat} (hy : y = 0 ∨ y = 96) {I : State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r) :
    CT I (.block (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y)) := by
  rcases hy with rfl | rfl
  · exact CT.taint [.ebp] hr (by taint_decide)
  · exact CT.taint [.ebp] hr (by taint_decide)

theorem b0_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D T nl al n tl) (b0 v.callee v.suffix y) := by
  refine CT.assoc3 (CT.seq (J := fun s => Env K W SP s ∧ slotv s.mem W ctxO = K ∧
      slotv s.mem W roundsO = BitVec.ofNat 32 R) ?_ (fun s hs => ?_) (updBlock_ct v L hR hy fun _ h => h))
  · refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
      (fun s hs => b0Flags_ok L hs.env h13 ht4 hal hs.slots.tl hs.slots.nlen hs.slots.alen) ?_
    refine CT.seq (J := fun s => s.gpr .ebp = W)
      (CT.ite (decide (al = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil)
        (fun _ => by exact CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)))
      (fun s₁ ⟨_, _, _, _, hzf, hbp, _⟩ => ?_) (b0Blk_ct hy (pin_ebp fun _ h => h))
    refine WP.ite (decide (al = 0)) (eval_e hzf) (fun _ => WP.of_runBlock ⟨s₁, rfl, hbp⟩) (fun _ => ?_)
    exact WP.of_runBlock ⟨_, by crun [], by cregs [hbp]⟩
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    refine WP.mono (b0Pre_ok L hs.env hnl h7 h13 ht4 ht16 hte hal hn hn32 hs.slots.tl hs.slots.nlen hs.slots.alen
      hs.slots.len hc0 hy) fun s₃ ⟨E₃, _, _, f₃, _⟩ => ?_
    have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
        · rcases hy with rfl | rfl
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
          · exact Lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)) (by decide)
    exact ⟨E₃, by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [k₃ _ (by decide) (by decide)]; exact hs.slots.rounds⟩

theorem mac_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D T : BitVec 32} {nl al n tl : Nat} (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    CT (MacPre K W SP R N A D T nl al n tl) (mac v.callee v.suffix y) := by
  refine CT.seq (J := MacMid K W SP R N A D T nl al n tl) (b0_ct v L hR h7 h13 ht4 ht16 hte hal hn hn32 hy)
    (fun s hs => ?_) ?_
  · obtain ⟨nonce, hnl, hc0⟩ := hs.c0
    exact WP.mono (b0_ok v L hs.env hR hs.slots hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
      fun s₁ ⟨E₁, f₁, _, rd, wr⟩ => hs.toMacMid.next L hy E₁ f₁ rd wr
  refine CT.seq (J := MacMid K W SP R N A D T nl al n tl)
    ((aad_ct v L hR hy hal).mono fun s hs => ⟨hs.env, hs.slots.ctx, hs.slots.rounds, hs.slots.aad, hs.slots.alen,
      hs.aad⟩)
    (fun s hs => WP.mono (aad_ok v L hs.env hR hs.slots.ctx hs.slots.rounds hy hs.slots.aad hs.slots.alen hs.aad hal)
      fun s₂ M => hs.next L hy M.env M.frame M.rd M.wr) ?_
  refine CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide)
    (fun s hs => dataArgs_ok L hs.env hs.slots.data hs.slots.len) ?_
  exact (absorbPad_ct v L hR hy hn32).mono fun s₃ ⟨s, hs, hm₃, hbp, hsp, hrd, hwr⟩ =>
    ⟨⟨hbp, hsp, hs.env.perm.of_eq hrd hwr⟩, by rw [dn_kept hm₃ (by decide) (by decide)]; exact hs.slots.ctx,
      by rw [dn_kept hm₃ (by decide) (by decide)]; exact hs.slots.rounds, fun _ => hs.data.of_eq hrd hwr,
      (dn_read hm₃).1, (dn_read hm₃).2⟩

/-- What `tag` starts from. -/
structure TagPre (K W SP : BitVec 32) (R : Nat) (s : State) : Prop where
  env : Env K W SP s
  ctx : slotv s.mem W ctxO = K
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  c0 : ∃ nonce : List Byte, 7 ≤ nonce.length ∧ nonce.length ≤ 13 ∧
    bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem tag_ct (v : Ctr32Impl) {K W SP : BitVec 32} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) : CT (TagPre K W SP R) (tag v.callee y) := by
  have blk : ∀ s, TagPre K W SP R s → ∃ s₃, runBlock isa (([.mov .eax (imm 0)] : List Instr) ++ ctrAt ++ keyArgs c1O ++
      ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s = some s₃ ∧
      s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr := fun s hs => by
    obtain ⟨nonce, h7, h13, hc0⟩ := hs.c0
    obtain ⟨s₃, run, -, -, rest⟩ := tagArgs_ok L hs.env hs.ctx hs.rounds h7 h13 hc0 y
    exact ⟨s₃, run, rest⟩
  have h₂ := ctrCall_ct v L hR (c := 64) (Q := W + BitVec.ofNat 32 y) (n := 1) (by decide)
    (I := fun s' => ∃ s, TagPre K W SP R s ∧ s'.gpr .eax = K ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 64 ∧ s'.gpr .ebx = W + BitVec.ofNat 32 y ∧ s'.gpr .edi = BitVec.ofNat 32 1 ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    fun s₃ ⟨s, hs, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ => by
      have E₃ : Env K W SP s₃ := ⟨bp, sp, hs.env.perm.of_eq rd wr⟩
      obtain ⟨hq, hqw, hqc, hqk⟩ := tagCall_pre L E₃ hy
      exact ⟨E₃, hq, hqw, hqc, hqk, ax, cx, dx, bx, di⟩
  rcases hy with rfl | rfl
  · exact CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂
  · exact CT.block_seq [.ebp] (pin_ebp fun _ h => h.env.ebp) (by taint_decide) blk h₂

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the start, and what the pieces after it keep, for
constant time

Untrusted: everything here is checked by Lean. The arguments and `esp` are
public (`pubOf`); from them, `seal` and `open` start (`Top`), the entry and
`Ctr₀` are constant time (`start_ct`), and after them each piece keeps `Run`,
from which the next one's precondition follows.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt tglO tpO)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains ofNat_toNat32 length_bytesAt)

/-- What is public: `esp` and the arguments. -/
def pubOf (s : State) : BitVec 32 × (Nat → BitVec 32) := (s.gpr .esp, fun i => if i < 11 then arg s i else 0)

theorem pubOf_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : pubOf s₁ = pubOf s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

/-- `seal` and `open` from their arguments. -/
structure Top (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  args : Args s K W SP N A D T R nl al n tl
  sp : s.gpr .esp = SP
  a0 : arg s 0 = K
  a1 : arg s 1 = BitVec.ofNat 32 R
  a2 : arg s 2 = N
  a3 : arg s 3 = BitVec.ofNat 32 nl
  a4 : arg s 4 = A
  a5 : arg s 5 = BitVec.ofNat 32 al
  a6 : arg s 6 = D
  a7 : arg s 7 = BitVec.ofNat 32 n
  a8 : arg s 8 = T
  a9 : arg s 9 = BitVec.ofNat 32 tl
  a10 : arg s 10 = W

/-- `Top` for the public values `p`. -/
abbrev TopOf (p : BitVec 32 × (Nat → BitVec 32)) : State → Prop :=
  Top (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
    (p.2 7).toNat (p.2 9).toNat

theorem top_of {s : State}
    (h : Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) : TopOf p s := by
  subst hp
  simp only [pubOf, show (0 : Nat) < 11 from by decide, show (1 : Nat) < 11 from by decide,
    show (2 : Nat) < 11 from by decide, show (3 : Nat) < 11 from by decide, show (4 : Nat) < 11 from by decide,
    show (5 : Nat) < 11 from by decide, show (6 : Nat) < 11 from by decide, show (7 : Nat) < 11 from by decide,
    show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, show (10 : Nat) < 11 from by decide,
    ↓reduceIte]
  exact ⟨h, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl⟩

/-! ## The start -/

theorem entry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 10 = W ∧ Covers [argsR SP 11] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32) : CT I ccmEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 10) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem start_ct {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (L : Lay K W SP) (h13 : nl ≤ 13) :
    CT (Top K W SP N A D T R nl al n tl) (.seq ccmEntry ctrs) := by
  refine CT.seq (J := fun s₁ => ∃ s, Top K W SP N A D T R nl al n tl s ∧ Entered s W s₁)
    (entry_ct fun s hs => ⟨hs.sp, hs.a10, hs.args.args, hs.args.fa⟩)
    (fun s hs => WP.mono (entry_ok hs.a10 hs.args.perm.w (by rw [hs.sp]; exact hs.args.args)
      (by rw [hs.sp]; exact hs.args.argsW) (by rw [hs.sp]; exact hs.args.fa) L.fw) fun s₁ E => ⟨s, hs, E⟩)
    (ctrs_ct L h13 fun s₁ ⟨s, hs, E₀⟩ => ⟨⟨E₀.ebp, by rw [E₀.esp, hs.sp], hs.args.perm.of_eq E₀.rd E₀.wr⟩,
      by rw [E₀.slots (2, nonceO) (by simp), hs.a2], by rw [E₀.slots (3, nlenO) (by simp), hs.a3]⟩)

/-! ## What the pieces keep -/

/-- After the start, and the pieces after it. -/
structure Run (s₀ : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : ∃ s₂, Started s₀ K W SP N A D T R nl al n tl s₂ ∧ Frame (mutR W SP D n) s₂.mem s.mem
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s₀.mem (w64 N) nl) 0

section
variable {s₀ : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}

theorem Run.of_started {s₂ : State} (St : Started s₀ K W SP N A D T R nl al n tl s₂) :
    Run s₀ K W SP N A D T R nl al n tl s₂ :=
  ⟨St.env, St.rd, St.wr, ⟨s₂, St, Frame.refl _ _⟩, St.c0⟩

theorem Run.step {s : State} (h : Run s₀ K W SP N A D T R nl al n tl s) {s' : State} (E : Env K W SP s')
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) {rs : List Region} (f : Frame rs s.mem s'.mem) (hm : InMut W SP D n rs)
    (hc : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) : Run s₀ K W SP N A D T R nl al n tl s' := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨s₂, St, f₂.trans (frame_toMut f hm)⟩,
    by rw [Proof.AesGcm.X86.bytesAt_frame f hc (by decide), h.c0]⟩

theorem Run.slots {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    Slots W K R N A D T nl al n tl s.mem := by
  obtain ⟨s₂, St, f₂⟩ := h.st
  exact (St.mut Ar f₂).1

theorem Run.mac_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    MacPre K W SP R N A D T nl al n tl s :=
  ⟨⟨h.env, h.slots Ar, Ar.aad.of_eq h.rd h.wr, Ar.data.of_eq h.rd h.wr⟩,
    ⟨_, length_bytesAt _ _ _, h.c0⟩⟩

theorem Run.tag_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    TagPre K W SP R s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds,
    ⟨_, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13, h.c0⟩⟩

theorem Run.ctr_pre {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s) :
    CtrPre K W SP R D n s :=
  ⟨h.env, (h.slots Ar).ctx, (h.slots Ar).rounds, (h.slots Ar).data, (h.slots Ar).len,
    ⟨_, ⟨Ar.lay, Ar.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, Ar.n32, h.c0, Ar.data.of_eq h.rd h.wr, by rw [h.wr]; exact Ar.dw,
      Ar.dk⟩⟩⟩

/-- After the MAC into `W + y`. -/
theorem Run.mac {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Y : List Byte} {s' : State} (A' : Absorbed K W SP s y Y s') :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step A'.env A'.rd A'.wr A'.frame (inMut_macR W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After the tag at `W + y`. -/
theorem Run.tag {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (f : Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 60] s.mem s'.mem) :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (inMut_tag W SP D n hy) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm

/-- After counter mode. -/
theorem Run.ctr {s : State} (Ar : Args s₀ K W SP N A D T R nl al n tl) (h : Run s₀ K W SP N A D T R nl al n tl s)
    {s' : State} (E : Env K W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (f : Frame (ctrR W SP D n) s.mem s'.mem) :
    Run s₀ K W SP N A D T R nl al n tl s' :=
  h.step E rd wr f (inMut_ctrR W SP D n) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (Ar.lay.stk_w' (by decide)).symm
    · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm

end

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. From the public values (the
arguments and `esp`), the start, the MAC, the tag, counter mode, the tag
copied out and the exit are each constant time (`seal_top_ct`); so is `seal`
(`seal_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (restore)
open VG.Proof.AesGcm.X86 (CT w64 length_bytesAt)

/-- `seal` from its arguments: `Top`, with the tag writable. -/
structure SealTop (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop
    extends Top K W SP N A D T R nl al n tl s where
  tw : Covers [⟨w64 T, tl⟩] s.wr

theorem seal_top_of {s : State} (h : sealPre s) {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) :
    SealTop (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
      (p.2 7).toNat (p.2 9).toNat s := by
  refine ⟨top_of (args_of_seal h) hp, ?_⟩
  subst hp
  simp only [pubOf, show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, ↓reduceIte]
  exact tag_wr h

theorem seal_top_ct (v : Ctr32Impl) {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : SealTop K W SP N A D T R nl al n tl z) :
    CT (SealTop K W SP N A D T R nl al n tl) («seal» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((start_ct L Ar.h13).mono fun s hs => hs.toTop) (fun s hs => WP.mono (start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9 hs.a10) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inl rfl)).mono
      fun s ⟨_, Tp, h⟩ => h.mac_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (mac_ok v L h.env Ar.rounds (h.slots Tp.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inl rfl) (Tp.args.aad.of_eq h.rd h.wr)
      (Tp.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, Tp, h.mac Tp.args (.inl rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((tag_ct v L Ar.rounds (.inl rfl)).mono fun s ⟨_, Tp, h⟩ => h.tag_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tag_ok v L h.env Ar.rounds (h.slots Tp.args).ctx (h.slots Tp.args).rounds (h7' _)
      (h13' _) h.c0 (.inl rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, Tp, h.tag Tp.args (.inl rfl) E rd wr f⟩) ?_
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, Tp, h⟩ => h.ctr_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre Tp.args
      exact WP.mono (ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, Tp, h.ctr Tp.args E' rd wr f⟩) ?_
  -- The tag copied out.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (tagOut_ct L fun s ⟨_, Tp, h⟩ => ⟨h.env, (h.slots Tp.args).tl, (h.slots Tp.args).tp⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tagOut_ok L h.env (h.slots Tp.args).tl (h.slots Tp.args).tp
      (by have := Ar.t4; omega_using [this]) Ar.t16 (Tp.args.tag.of_eq h.rd h.wr) (by rw [h.wr]; exact Tp.tw))
      fun _ ⟨_, E, _, _⟩ => E.ebp) ?_
  -- The exit.
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callee v.suffix) :=
  CT.constantTime pubOf (fun _ _ _ _ h => pubOf_eq h) fun p => by
    by_cases hex : ∃ s, sealX86.pre s ∧ pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (seal_top_ct v z (seal_top_of hz hp)).mono fun s hs => seal_top_of hs.1 hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86
