module

public import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.AesCcm.X86.SealCT
import VerifiedGarbage.Proof.CmacAes.X86.Verified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCcm.X86
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.AesCcm.X86.Seal
import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.AesCcm.X86.TopCT
public import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.X86.Mac
import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.X86.TopCT
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesCcm.X86.Seal
meta import VerifiedGarbage.Proof.AesCcm.X86.Mac
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesCcm.X86.Blocks
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86.Top

/-! ### `AesCcm.X86.OpenCT`, which only this module used -/

section

/-! ### `AesCcm.X86.Open`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is the start (the
entry and `Ctr₀`), counter mode over the data, which decrypts it (`ctr_ok`),
the MAC of the plaintext at `W + 96` (`mac_ok`), encrypted (`tag_ok`), the
received tag padded (AES-GCM's `recv_ok`) and compared with it without a branch
(AES-GCM's `cmp_ok`), the data masked (`mask_ok`) and the exit
(`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot cmp recv tglO tpO rO vO)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left WEnv)

theorem ofNat_ite (p : Prop) [Decidable p] :
    BitVec.ofNat 32 (if p then 1 else 0) = if decide p = true then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem append_zeros_iff {x y : List Byte} {k : Nat} :
    x ++ Spec.Gcm.zeros k = y ++ Spec.Gcm.zeros k ↔ x = y :=
  ⟨List.append_cancel_right, fun h => by rw [h]⟩

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) :
    WP isa («open» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      match Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl)
          (bytesAt s.mem (w64 D) n) (bytesAt s.mem (w64 A) al) (bytesAt s.mem (w64 T) tl) with
      | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 D) n = pt
      | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 D) n = Spec.Ccm.zeros n := by
  have L := Ar.lay
  obtain hnl := length_bytesAt s.mem (w64 N) nl
  obtain h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  have ht16 := Ar.t16
  have ht4 := Ar.t4
  refine seq_assoc (WP.seq (WP.mono (start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- Counter mode: the plaintext.
  obtain C₂ : CtrCtx K W SP s₂ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, St.c0, Ar.data.of_eq St.rd St.wr,
      by rw [St.wr]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v C₂ St.env St.slots.ctx St.slots.rounds St.slots.data St.slots.len)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  obtain f₂₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frame_toMut f₃ (inMut_ctrR W SP D n)
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₂₃
  obtain hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 :=
    C₂.c0_kept f₃
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, St.rd]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, St.wr]
  -- The MAC of the plaintext.
  refine WP.seq (WP.mono (mac_ok v L E₃ Ar.rounds S₃ hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 hc₃ (y := 96) (.inr rfl) (Ar.aad.of_eq rd₃' wr₃') (Ar.data.of_eq rd₃' wr₃')) fun s₄ A₄ => ?_)
  obtain f₂₄ : Frame (mutR W SP D n) s₂.mem s₄.mem := f₂₃.trans (frame_toMut A₄.frame (inMut_macR W SP D n (.inr rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  obtain hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₄.frame, hc₃]
  -- The tag of the plaintext.
  refine WP.seq (WP.mono (tag_ok v L A₄.env Ar.rounds S₄.ctx S₄.rounds h7' h13' hc₄ (y := 96) (.inr rfl))
    fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  obtain f₂₅ : Frame (mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (frame_toMut f₅ (inMut_tag W SP D n (.inr rfl)))
  obtain ⟨S₅, -, -, -, -⟩ := St.mut Ar f₂₅
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, A₄.rd, rd₃']
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, A₄.wr, wr₃']
  -- The received tag.
  obtain Tb₅ := Ar.tag.of_eq rd₅' wr₅'
  refine WP.seq (WP.mono (Proof.AesGcm.X86.recv_ok ⟨E₅.ebp, E₅.perm.w, L.fw⟩ S₅.tl S₅.tp Tb₅.rd Tb₅.wrap Tb₅.w
    (by omega_arith) ht16) fun s₆ ⟨b₆, f₆, bp₆, _, sp₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ : Env K W SP s₆ := ⟨by rw [bp₆, E₅.ebp], by rw [sp₆, E₅.esp], E₅.perm.of_eq rd₆ wr₆⟩
  -- The comparison.
  obtain hv₆ : slotv s₆.mem W tglO = BitVec.ofNat 32 tl := by
    show s₆.mem.readW (w64 W + BitVec.ofNat 64 tglO) 32 = _
    rw [f₆.readW (r := ⟨w64 W + BitVec.ofNat 64 tglO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact S₅.tl
  refine WP.seq (WP.mono (Proof.AesGcm.X86.cmp_ok (o := uO) ⟨E₆.ebp, E₆.perm.w, L.fw⟩ hv₆ (by omega_arith) ht16 (by decide))
    fun s₇ ⟨ax₇, f₇, bp₇, _, sp₇, rd₇, wr₇⟩ => ?_)
  rw [ofNat_ite] at ax₇
  generalize hc : decide (bytesAt s₆.mem (w64 W + BitVec.ofNat 64 uO) tl ++ Spec.Gcm.zeros (16 - tl) =
    bytesAt s₆.mem (w64 W + BitVec.ofNat 64 rO) 16) = c at ax₇
  obtain E₇ : Env K W SP s₇ := ⟨by rw [bp₇, E₆.ebp], by rw [sp₇, E₆.esp], E₆.perm.of_eq rd₇ wr₇⟩
  -- `ok` kept.
  obtain ⟨s₈, run₈, hm₈, bp₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.store (at_ .ebp okO) .eax] s₇ = some s₈ ∧
      s₈.mem = s₇.mem.writeW (w64 W + BitVec.ofNat 64 okO) (if c = true then (1 : BitVec 32) else 0) ∧
      s₈.gpr .ebp = W ∧ s₈.gpr .esp = SP ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by crun [E₇.ebp, L.aW, E₇.perm.wW], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [ax₇]
    · cregs [E₇.ebp]
    · cregs [E₇.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  obtain E₈ : Env K W SP s₈ := ⟨bp₈, sp₈, E₇.perm.of_eq rd₈ wr₈⟩
  obtain f₅₈ : Frame (mutR W SP D n) s₅.mem s₈.mem := by
    rw [hm₈]
    refine (((f₆.sub fun r hr => ?_).trans (f₇.sub fun r hr => ?_)).writeW (r := wO W) (by simp) _
      (Region.contains_self _ _))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨wT W, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain f₂₈ : Frame (mutR W SP D n) s₂.mem s₈.mem := f₂₅.trans f₅₈
  obtain ⟨S₈, -, -, -, -⟩ := St.mut Ar f₂₈
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅']
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅']
  -- The data masked.
  obtain hok : slotv s₈.mem W okO = if c = true then 1 else 0 := by rw [hm₈]; exact Mem.readW_writeW_self32 _ _ _
  refine WP.seq (WP.mono (mask_ok L E₈ S₈.data S₈.len Ar.n32 (Ar.data.of_eq rd₈' wr₈') (by rw [wr₈']; exact Ar.dw) hok)
    fun s₉ ⟨E₉, rd₉, wr₉, hm₉⟩ => ?_)
  obtain f₈₉ : Frame (mutR W SP D n) s₈.mem s₉.mem := by
    rw [hm₉]
    exact writeBytes_frame _ _ _ (by
      rw [Proof.AesCcm.X86.length_mask]; exact Region.contains_self _ _) |>.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  obtain f₂₉ : Frame (mutR W SP D n) s₂.mem s₉.mem := f₂₈.trans f₈₉
  obtain ⟨S₉, sv₉, -, -, rt₉⟩ := St.mut Ar f₂₉
  obtain hok₉ : slotv s₉.mem W okO = if c = true then 1 else 0 := by
    rw [hm₉]
    refine (writeBytes_frame _ _ _ (R := ⟨w64 D, n⟩) (by rw [length_mask]; exact Region.contains_self _ _)).readW
      (r := ⟨w64 W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide) |>.trans hok
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm
  -- `ok` returned.
  obtain ⟨s₁₀, run₁₀, hm₁₀, ax₁₀, bp₁₀, sp₁₀, rd₁₀, wr₁₀⟩ : ∃ s₁₀, runBlock isa [.mov .eax (slot okO)] s₉ = some s₁₀ ∧
      s₁₀.mem = s₉.mem ∧ s₁₀.gpr .eax = (if c = true then 1 else 0) ∧ s₁₀.gpr .ebp = W ∧ s₁₀.gpr .esp = SP ∧
      s₁₀.rd = s₉.rd ∧ s₁₀.wr = s₉.wr := by
    refine ⟨_, by crun [E₉.ebp, L.aW, E₉.perm.wR, hok₉], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hok₉]
    · cregs [E₉.ebp]
    · cregs [E₉.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩)
  -- The exit.
  obtain rd₁₀' : s₁₀.rd = s.rd := by rw [rd₁₀, rd₉, rd₈']
  obtain wr₁₀' : s₁₀.wr = s.wr := by rw [wr₁₀, wr₉, wr₈']
  refine WP.mono (exit_ok (W := W) (s₀ := s) bp₁₀ (by rw [sp₁₀, hsp])
    (by rw [rd₁₀', wr₁₀']; exact covers_left Ar.perm.w) L.fw (by rw [hm₁₀]; exact sv₉)
    (by rw [hm₁₀, hsp]; exact rt₉)) fun s' ⟨abi, m', ax', _, _⟩ => ⟨abi, ?_⟩
  -- The plaintext, the tags and the comparison.
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  obtain ci₃ := (St.mut Ar f₂₃).2.2.1
  obtain ci₄ := (St.mut Ar f₂₄).2.2.1
  obtain aa₃ := (St.mut Ar f₂₃).2.2.2.1
  obtain dW : ∀ (r : Region), Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 60 → (⟨w64 D, n⟩ : Region).Disjoint r :=
    fun r h => by rcases h with h | rfl; exact Ar.data.w.sub_right h; exact Ar.data.stk.symm
  obtain pt₃ : bytesAt s₃.mem (w64 D) n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n) := by
    rw [h₃, St.ciph, St.dataB, crypt_eq (hBC _)]
  obtain pt₈ : bytesAt s₈.mem (w64 D) n = bytesAt s₃.mem (w64 D) n := by
    rw [hm₈, bytesAt_writeW_sep _ _ (Ar.data.w.sub_right (Lay.wSub (by decide))) (by have := Ar.data.lt; omega_arith),
      Proof.AesGcm.X86.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
        (by have := Ar.data.lt; omega_arith),
      Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
        (by have := Ar.data.lt; omega_arith),
      buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₅,
      buf_kept Ar.data (y := 96) (by decide) A₄.frame]
  obtain tg₅ : bytesAt s₅.mem (w64 T) tl = bytesAt s.mem (w64 T) tl := by
    rw [buf_mut Ar.tag Ar.td f₂₅, St.tagB]
  obtain hl : (bytesAt s.mem (w64 N) nl).length ≤ 15 := by rw [hnl]; have := Ar.h13; omega_arith
  have o₄ := A₄.out
  rw [ci₃, aa₃, pt₃] at o₄
  obtain hY := congrArg List.length o₄
  rw [length_bytesAt] at hY
  obtain hV : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 uO) tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n))) := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by simp only [uO, rO]; omega_arith)) (by simp only [uO]; omega_arith) (by decide)) (by omega_arith),
      Proof.AesCcm.bytesAt_prefix s₅.mem _ ht16, h₅, ci₄, o₄, take_xorFrom_zero (hBC _) _ hY.symm ht16,
      ← Proof.AesCcm.mac_eq _ _ hl]
  obtain hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n))).length =
        tl := by
    rw [Proof.AesCcm.mac_eq _ _ hl, List.length_take, length_bytesAt] at *; omega_arith
  obtain key : c = true ↔
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 T) tl) =
        Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)) := by
    rw [← hc, b₆, tg₅, hV, decide_eq_true_iff,
      append_zeros_iff, cryptTag_eq_iff (hBC _) ht16 _ hML (length_bytesAt _ _ _), eq_comm]
  simp only [Spec.Ccm.decryptWith]
  obtain hD₉ : bytesAt s'.mem (w64 D) n = if c then bytesAt s₈.mem (w64 D) n else Spec.Ccm.zeros n := by
    rw [m', hm₁₀, hm₉, bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) (by have := Ar.data.lt; omega_arith),
      List.drop_eq_nil_of_le (by rw [length_mask, length_bytesAt]), List.append_nil]
  by_cases hk : c = true
  · have hk' := key.mp hk
    simp only [hk', ↓reduceIte]
    refine ⟨by rw [ax', ax₁₀, hk]; rfl, by rw [hD₉, hk]; simp only [↓reduceIte]; rw [pt₈, pt₃]⟩
  · have hk' : ¬ _ := fun e => hk (key.mpr e)
    simp only [hk', ↓reduceIte]
    obtain hf : c = false := by simpa using hk
    refine ⟨by rw [ax', ax₁₀, hf]; rfl, by rw [hD₉, hf]; rfl⟩

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. After the pieces `seal` also
has (`SealCT.lean`), `open` compares the tags without a branch (AES-GCM's
`recv` and `cmp`, `cmp96_ct`), keeps the result and masks the data with it,
looping over the data's length alone (`mask_ct`): `open_top_ct`, `open_ct`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop cmp recv restore tglO tpO rO vO)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq WEnv cmp_ok recv_ct recv_ok length_bytesAt and_self_beq32 readW_writeW_off)

/-- `cmp 96` (AES-GCM's `cmp_ct`, for CCM's offset of the computed tag). -/
theorem cmp96_ct {I : State → Prop} {W : BitVec 32} {t : Nat}
    (h : ∀ s, I s → WEnv W s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t) : CT I (cmp uO) := by
  have hb : CT I (.block (zero4 vO ++ [.mov .edi (.reg .ebp), .alu .add .edi (imm uO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm vO), .mov .ecx (slot tglO)])) :=
    CT.taint [.ebp] (pin1 fun s hs => (h s hs).1.ebp) (by taint_decide)
  refine CT.seq (J := fun s => s.gpr .edi = W + BitVec.ofNat 32 uO ∧ s.gpr .edx = W + BitVec.ofNat 32 vO ∧
      s.gpr .ecx = BitVec.ofNat 32 t ∧ s.gpr .ebp = W) hb
    (fun s hs => ?_) (CT.taint [.edi, .edx, .ecx, .ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  obtain ⟨he, hv⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  exact WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv], by regs [he.ebp],
    by regs [he.ebp], by regs [], by regs [he.ebp]⟩

/-! ## Masking the data -/

theorem maskTest_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {n : Nat}
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hlen]
  · cmems [hlen]; rw [and_self_beq32 hn32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem maskArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : Lay K W SP) (E₁ : Env K W SP s₁) {D : BitVec 32} {n : Nat}
    (hd₁ : slotv s₁.mem W dataO = D) (cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 n) :
    ∃ s₂, runBlock isa [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n := by
  refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], ?_, ?_⟩
  · cregs [hd₁]
  · cregs [cx₁]

theorem mask_ct {K W SP : BitVec 32} (L : Lay K W SP) {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32)
    {I : State → Prop}
    (h : ∀ s, I s → Env K W SP s ∧ slotv s.mem W dataO = D ∧ slotv s.mem W lenO = BitVec.ofNat 32 n) :
    CT I mask := by
  refine CT.block_seq [.ebp] (pin_ebp fun s hs => (h s hs).1.ebp) (by taint_decide)
    (fun s hs => maskTest_ok L (h s hs).1 (h s hs).2.2 hn32) ?_
  refine CT.ite (decide (n = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, m₁, cx₁, _, bp₁, sp₁, rd₁, wr₁⟩ => maskArgs_ok L
      ⟨bp₁, sp₁, (h s hs).1.perm.of_eq rd₁ wr₁⟩ (by rw [m₁]; exact (h s hs).2.1) cx₁) ?_
  exact CT.taint [.edi, .ecx] (pin2 fun _ ⟨_, _, hdi, hcx⟩ => ⟨hdi, hcx⟩) (by taint_decide)

/-! ## `open` -/

theorem okStore_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) :
    ∃ s', runBlock isa [.store (at_ .ebp okO) .eax] s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 okO) (s.gpr .eax) ∧ Env K W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW], ?_, E.keep (by cregs []) (by cregs []) (by cmems []) (by cmems []), ?_, ?_⟩
  all_goals cmems []

theorem open_top_ct (v : Ctr32Impl) {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : Top K W SP N A D T R nl al n tl z) :
    CT (Top K W SP N A D T R nl al n tl) («open» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  have c0W : ∀ {d k : Nat}, (64 ≤ d ∨ d + k ≤ 48) → d + k ≤ 2560 →
      (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ =>
    Lay.w_w (by omega_using [h₁]) (by decide) h₂
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    (start_ct L Ar.h13) (fun s hs => WP.mono (start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9 hs.a10) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, Tp, h⟩ => h.ctr_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre Tp.args
      exact WP.mono (ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, Tp, h.ctr Tp.args E' rd wr f⟩) ?_
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inr rfl)).mono
      fun s ⟨_, Tp, h⟩ => h.mac_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (mac_ok v L h.env Ar.rounds (h.slots Tp.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inr rfl) (Tp.args.aad.of_eq h.rd h.wr)
      (Tp.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, Tp, h.mac Tp.args (.inr rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((tag_ct v L Ar.rounds (.inr rfl)).mono fun s ⟨_, Tp, h⟩ => h.tag_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tag_ok v L h.env Ar.rounds (h.slots Tp.args).ctx (h.slots Tp.args).rounds (h7' _)
      (h13' _) h.c0 (.inr rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, Tp, h.tag Tp.args (.inr rfl) E rd wr f⟩) ?_
  -- The received tag.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    (recv_ct (W := W) (T := T) (t := tl) fun s ⟨_, Tp, h⟩ =>
      ⟨⟨h.env.ebp, h.env.perm.w, L.fw⟩, (h.slots Tp.args).tl, (h.slots Tp.args).tp⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (recv_ok ⟨h.env.ebp, h.env.perm.w, L.fw⟩ (h.slots Tp.args).tl (h.slots Tp.args).tp
      (Tp.args.tag.of_eq h.rd h.wr).rd (Tp.args.tag.of_eq h.rd h.wr).wrap (Tp.args.tag.of_eq h.rd h.wr).w
      (by have := Ar.t4; omega_using [this]) Ar.t16) fun _ ⟨_, f, bp, _, sp, rd, wr⟩ => ⟨s₀, Tp,
        h.step ⟨by rw [bp, h.env.ebp], by rw [sp, h.env.esp], h.env.perm.of_eq rd wr⟩ rd wr f
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨wT W, by simp, fun _ h => h⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide))⟩) ?_
  -- The comparison.
  refine CT.seq (J := fun s => (∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s) ∧
      ∃ c : Bool, s.gpr .eax = if c then 1 else 0)
    (cmp96_ct (W := W) (t := tl) fun s ⟨_, Tp, h⟩ => ⟨⟨h.env.ebp, h.env.perm.w, L.fw⟩, (h.slots Tp.args).tl⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (cmp_ok (o := uO) ⟨h.env.ebp, h.env.perm.w, L.fw⟩ (h.slots Tp.args).tl
      (by have := Ar.t4; omega_using [this]) Ar.t16 (by decide)) fun s' ⟨ax, f, bp, _, sp, rd, wr⟩ =>
        ⟨⟨s₀, Tp, h.step ⟨by rw [bp, h.env.ebp], by rw [sp, h.env.esp], h.env.perm.of_eq rd wr⟩ rd wr f
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide))⟩,
          _, by rw [ax, ofNat_ite]⟩) ?_
  -- `ok` kept.
  refine CT.seq (J := fun s => (∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s) ∧
      ∃ c : Bool, slotv s.mem W okO = if c then 1 else 0)
    (CT.taint [.ebp] (pin_ebp fun _ ⟨⟨_, _, h⟩, _⟩ => h.env.ebp) (by taint_decide))
    (fun s ⟨⟨s₀, Tp, h⟩, c, hc⟩ => by
      obtain ⟨s', run, hm, E', rd, wr⟩ := okStore_ok L h.env
      refine WP.of_runBlock ⟨s', run, ⟨s₀, Tp, h.step E' rd wr (rs := [wO W]) ?_ ?_ ?_⟩, c, ?_⟩
      · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨wO W, by simp, fun _ h => h⟩
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide)
      · rw [hm, ← hc]; exact Mem.readW_writeW_self32 _ _ _) ?_
  -- The data masked.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    (mask_ct L Ar.n32 fun s ⟨⟨_, Tp, h⟩, _⟩ => ⟨h.env, (h.slots Tp.args).data, (h.slots Tp.args).len⟩)
    (fun s ⟨⟨s₀, Tp, h⟩, c, hc⟩ => WP.mono (mask_ok L h.env (h.slots Tp.args).data (h.slots Tp.args).len Ar.n32
      (Tp.args.data.of_eq h.rd h.wr) (by rw [h.wr]; exact Tp.args.dw) hc) fun s' ⟨E, rd, wr, hm⟩ =>
        ⟨s₀, Tp, h.step E rd wr (rs := [⟨w64 D, n⟩])
          (by rw [hm]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (Tp.args.data.w.sub_right (Lay.wSub (by decide))).symm)⟩) ?_
  -- `ok` returned, and the exit.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (CT.taint [.ebp] (pin_ebp fun _ ⟨_, _, h⟩ => h.env.ebp) (by taint_decide))
    (fun s ⟨_, _, h⟩ => WP.of_runBlock ⟨_, by crun [h.env.ebp, L.aW, h.env.perm.wR], by cregs [h.env.ebp]⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem open_ct (v : Ctr32Impl) : ConstantTime isa openX86.pre openX86.pub («open» v.callee v.suffix) :=
  CT.constantTime pubOf (fun _ _ _ _ h => pubOf_eq h.1) fun p => by
    by_cases hex : ∃ s, openX86.pre s ∧ pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (open_top_ct v z (top_of (args_of_open hz) hp)).mono fun s hs => top_of (args_of_open hs.1) hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.Verified`, which only this module used -/

section

/-!
# AES-CCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`seal_wp'`,
`open_wp'`) and constant time (`seal_ct`, `open_ct`) for any implementation
`v` of `vg_aes_ctr32_to`, a state satisfying the precondition, and the shared
contracts with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 60 bytes of stack: a call of
`vg_cmac_aes_update` (its six arguments and return address) and its own
calls of `vg_aes_ctr32_to`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (ofNat_toNat32)

theorem seal_correct (v : Ctr32Impl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' := by
  obtain ⟨t, s', e, abi, h⟩ := seal_wp' v (args_of_seal hs) rfl rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (tag_wr hs)
  exact ⟨t, s', e, abi, h⟩

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

theorem open_correct (v : Ctr32Impl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' := by
  obtain ⟨t, s', e, abi, h⟩ := open_wp' v (args_of_open hs) rfl rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
  refine ⟨t, s', e, abi, ?_⟩
  simp only [openX86, setWidth_ret]
  exact h

theorem seal_spSafe (v : Ctr32Impl) : («seal» v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, tagOut, Code.all, Proof.CmacAes.X86.update_spSafe v,
    v.spSafe, Bool.and_true]
  decide +kernel

theorem open_spSafe (v : Ctr32Impl) : («open» v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    Code.all, Proof.CmacAes.X86.update_spSafe v, v.spSafe, Bool.and_true]
  decide +kernel

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: the key
schedule at `0x1000`, 10 rounds, a 7-byte nonce at `0x2000`, no associated
data (at `0x2100`), no data (at `0x3000`), a 4-byte tag at `0x4000` and
`work` at `0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8010 then 7 else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30
    else if a = 0x8025 then 0x40 else if a = 0x8028 then 4 else if a = 0x802d then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩] }

theorem sealSat_args : arg sealSat 0 = 0x1000 ∧ arg sealSat 1 = 10 ∧ arg sealSat 2 = 0x2000 ∧ arg sealSat 3 = 7 ∧
    arg sealSat 4 = 0x2100 ∧ arg sealSat 5 = 0 ∧ arg sealSat 6 = 0x3000 ∧ arg sealSat 7 = 0 ∧
    arg sealSat 8 = 0x4000 ∧ arg sealSat 9 = 4 ∧ arg sealSat 10 = 0x5000 ∧ argAddr sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg openSat 0 = 0x1000 ∧ arg openSat 1 = 10 ∧ arg openSat 2 = 0x2000 ∧ arg openSat 3 = 7 ∧
    arg openSat 4 = 0x2100 ∧ arg openSat 5 = 0 ∧ arg openSat 6 = 0x3000 ∧ arg openSat 7 = 0 ∧
    arg openSat 8 = 0x4000 ∧ arg openSat 9 = 4 ∧ arg openSat 10 = 0x5000 ∧ argAddr openSat 0 = 0x8004 :=
  sealSat_args

theorem seal_verified (v : Ctr32Impl) :
    Verified X86.target («seal» v.callee v.suffix) (Proof.AesCcm.sealScratchContract X86.abi 60) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
      Proof.AesCcm.sealRoundsPost, sealX86, sealPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
      stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using sealSat)

theorem open_verified (v : Ctr32Impl) :
    Verified X86.target («open» v.callee v.suffix) (Proof.AesCcm.openScratchContract X86.abi 60) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR,
          workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero,
          false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by
        obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := openSat_args
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR,
          workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using openSat }

end VG.Proof.AesCcm.X86

end

end


/-!
# AES-CCM on x86, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the ten argument slots and the 2560 bytes of working space, 2608 bytes. The
code's own calls use 60 bytes below it. The copies are read only where the
pre- and postconditions read the buffers, and `open`'s leak, whether it
succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem seal_noEsp : («seal» v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, tagOut, Code.allInstrs,
    noEsp_of (Proof.CmacAes.X86.update_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem open_noEsp : («open» v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» v.callee v.suffix) ≤ 60 := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, tagOut, stackUse,
    Proof.CmacAes.X86.update_stack v, v.stack]
  decide +kernel

theorem open_stackUse : stackUse («open» v.callee v.suffix) ≤ 60 := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    stackUse, Proof.CmacAes.X86.update_stack v, v.stack]
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: as `sealSat`, with ten stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x8004, 40⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract X86.abi 2668).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract X86.abi 2668).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («seal» v.callee v.suffix))
      (Proof.AesCcm.sealRoundsContract X86.abi 2668) :=
  X86.Verified.stackScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ccm.sealPre X86.abi.ptrBits) (post := Proof.AesCcm.sealRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 60) (bytes := 2608) (seal_verified v) (by decide) (seal_noEsp v)
    (seal_stackUse v) (sealPre_local _) (sealPost_local _) (sealPostOut_local _) sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» v.callee v.suffix))
      (Proof.AesCcm.openRoundsContract X86.abi 2668) :=
  X86.Verified.stackScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ccm.openPre X86.abi.ptrBits) (post := Proof.AesCcm.openRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 60) (leak := some (Spec.Ccm.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (openPre_local _) (openPost_local _) (openPostOut_local _)
    openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesCcm.X86
