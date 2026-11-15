module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Sm4Gcm.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.Run
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Open
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OpenCT
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.AesGcm.Scratch

/-! ### `Sm4Gcm.X86_64.Verified`, which only this module used -/

section

/-! ### `Sm4Gcm.X86_64.Init`, which only this module used -/

section

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule from
`vg_sm4_expand_key` in the context's first 128 bytes, then the hash subkey
`CIPH_K(0¹²⁸)` at byte 240 from `vg_sm4_ctr32` over a zero block with a zero
counter block (`init_wp`), as AES-GCM's (`Proof/AesGcm/X86_64/Init.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr save restore tO)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.AesGcm.X86_64 (save_ok exit_ok SavedAt savedR ret_kept covers_left covers_cons covers_of_mem
  covers_off in_off covers_prefix add_ofNat_assoc zeroT_bytes bytesAt_frame blockAt_frame blocksAt_one
  ctr32_single ctxH_eq)

/-- The key, as SM4's block of 16 bytes. -/
theorem blockAt_eq_ofFn (m : Mem) (p : Addr) :
    Spec.Sm4.blockAt m p = Vector.ofFn fun i => (bytesAt m p 16).getD i.val 0 := by
  apply Vector.ext
  intro i hi
  simp [Spec.Sm4.blockAt, bytesAt, hi]

/-- `vg_sm4_gcm_init`. -/
theorem init_wp {s : State} (hp : Proof.Sm4Gcm.initX86_64.pre s) :
    WP isa init s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.initX86_64.post s s' := by
  simp only [Proof.Sm4Gcm.initX86_64, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk] at hp ⊢
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, r_c, r_s, k_k, k_c, k_s, wk, wc, ws, hsp⟩ := hp
  generalize hK : s.gpr .rdi = K at *
  generalize hCtx : s.gpr .rsi = Ctx at *
  generalize hW : s.gpr .rdx = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .rdx hW pW
  obtain ⟨s₂, run₂, h15, h13, hdi, hsi, hsp₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = Ctx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hg₁, hW, hCtx, hK, hSP]
  refine WP.seq ?_
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  have kc : KeyCall s₂ K Ctx := by
    refine ⟨hdi, hsi, by rw [hsp₂]; exact hsp, wk, by omega_arith, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [hsp₂]; exact k_k, by rw [hsp₂]; exact k_c.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂, hrd]
      exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (covers_left (covers_prefix pC (by decide)))
    · rw [wr₂]; exact covers_prefix pC (by decide)
  refine WP.seq (WP.mono (key_call kc) fun s₃ g => ?_)
  have g15 : s₃.gpr .r15 = W := by rw [g.saved .r15 (by decide), h15]
  have g13 : s₃.gpr .r13 = Ctx := by rw [g.saved .r13 (by decide), h13]
  have gsp : s₃.gpr .rsp = SP := by rw [g.saved .rsp (by decide), hsp₂]
  have rd₃ : s₃.rd = s.rd := g.rd.trans rd₂
  have wr₃ : s₃.wr = s.wr := g.wr.trans wr₂
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  rw [← wr₃] at w₁ w₂ w₃ w₄
  obtain ⟨s₄, run₄, hm₄, hdi₄, hsi₄, hdx₄, hcx₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] ++
        ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ [.mov32 .rcx (imm 1)]) s₃ = some s₄ ∧
      s₄.mem = (((s₃.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = W + BitVec.ofNat 64 96 ∧ s₄.gpr .rdx = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .rcx = BitVec.ofNat 64 1 ∧ (∀ r ∈ calleeSaved, s₄.gpr r = s₃.gpr r) ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    rw [add_ofNat_assoc, add_ofNat_assoc]
    refine ⟨_, by xrun [g15, g13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), gsp]
  have rd₄ : s₄.rd = s.rd := hrd₄.trans rd₃
  have wr₄ : s₄.wr = s.wr := hwr₄.trans wr₃
  -- The disjointness of the parts.
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_arith)
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Cmac.frame_store2 _ _ _).mono (by simp))
  have hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  have hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  have hk₄ : Spec.Sm4.scheduleAt s₄.mem Ctx = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem K) := by
    rw [Proof.Sm4.scheduleAt_congr fun i hi => f₄.bytes (R := ⟨Ctx, 128⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by show 128 ≤ 2 ^ 64; omega_arith) hi, g.out, hm₂]
    apply congrArg Spec.Sm4.expandKey
    apply Vector.ext
    intro i hi
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    exact f₁.bytes (R := ⟨K, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_ks.sub_right (Offset.sub_base _ (by decide)))
      (by show 16 ≤ 2 ^ 64; omega_arith) hi
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  have cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 := by
    refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, by rw [g4sp]; exact hsp, by omega_arith,
      by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith,
      by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega_arith,
      by simpa using dCW 0 128 (by decide) 96 16 (by decide), dK0,
      (dCW 240 16 (by decide) 96 16 (by decide)).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g4sp]; exact k_c.sub_right (Region.sub_prefix (by decide))
    · rw [g4sp]; exact k_s.sub_right (Offset.sub_base _ (by decide))
    · rw [g4sp]; exact k_c.sub_right (Offset.sub_base _ (by decide))
    · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
        (covers_left (covers_off pW' (by decide) (by decide)))
        (covers_left (covers_off pC' (by decide) (by decide))))
    · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))
  refine WP.seq (WP.mono (ctr_call cc) fun s₅ c => ?_)
  have gout := c.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq, hT₄, hD₄, hk₄] at gout
  have c15 : s₅.gpr .r15 = W := by rw [c.saved .r15 (by decide), hg₄ .r15 (by decide), g15]
  have c5sp : s₅.gpr .rsp = SP := by rw [c.saved .rsp (by decide), g4sp]
  have cfr := c.frame
  rw [g4sp] at cfr
  have gfr := g.frame
  rw [hsp₂] at gfr
  -- The saved registers and the return address.
  have dSv : ∀ r ∈ [(⟨Ctx, 128⟩ : Region), below SP stkN], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
    · exact (k_s.sub_right (Offset.sub_base _ (by decide))).symm
  have dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  have dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩, below SP stkN],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact (k_s.sub_right (Offset.sub_base _ (by decide))).symm
  have hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← hm₂]; exact gfr) dSv).frame f₄ dSv₄).frame cfr dSv₅)
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept cfr (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_), ret_kept gfr (fun r hr => ?_), hm₂,
      ret_kept f₁ (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact r_s.sub_right (Offset.sub_base _ (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact r_c.sub_right (Region.sub_prefix (by decide))
      · exact ret_stk SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact r_s.sub_right (Offset.sub_base _ (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact r_s.sub_right (Offset.sub_base _ (by decide))
      · exact r_c.sub_right (Offset.sub_base _ (by decide))
      · exact ret_stk SP
  have hrc : Covers [⟨W, 2560⟩] (s₅.rd ++ s₅.wr) := by rw [c.rd, c.wr, rd₄, wr₄]; exact covers_left pW
  refine WP.mono (exit_ok c15 (by rw [c5sp, hSP]) hrc hsv₅ (by rw [hSP]; exact hret)) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  rw [hm]
  refine ⟨?_, ?_⟩
  · rw [Proof.Sm4.scheduleAt_congr fun i hi => cfr.bytes (R := ⟨Ctx, 128⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
        · exact dK0
        · exact (k_c.sub_right (Region.sub_prefix (by decide))).symm)
        (by show 128 ≤ 2 ^ 64; omega_arith) hi, hk₄, blockAt_eq_ofFn]
  · rw [ctxH_eq, gout.1, Spec.Sm4.gcmCipherOfKey, blockAt_eq_ofFn]
    simp

end VG.Proof.Sm4Gcm.X86_64

end

end


/-!
# SM4-GCM on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_ghash`, in AES-GCM's `GcmImpl`, of which
the code calls only `vg_ghash`), a state satisfying each precondition, and
the shared contracts of `Spec/Sm4/Gcm/Contract.lean` with the working space
as a last argument (`Proof/Sm4Gcm/Scratch.lean`), with the `stkN` bytes of
stack below the stack pointer that the calls of `vg_sm4_ctr32` use.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (cryptHead absorb absorbPad lens j0 recv cmp tagOut tagLenOk partWith
  firstFlush streamLoad oneAad xorLoop xorLoopG flush absorbHead absorbWhole absorbTail padTail ghash1 j0hash
  minLen copyLoop headPart)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

theorem ctrFn_mx : ctrFn.code.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem keyFn_mx : keyFn.code.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem ctrFn_spSafe : ctrFn.code.all (fun i => !X86_64.isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  exact congrArg Bool.not (ctr_spSafe i hi)

theorem keyFn_spSafe : keyFn.code.all (fun i => !X86_64.isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  exact congrArg Bool.not (key_spSafe i hi)

theorem ctrFn_depth : ctrFn.code.x86_64Depth ≤ 3216 := ctr_depth

theorem keyFn_depth : keyFn.code.x86_64Depth ≤ 3144 := key_depth

theorem init_mx : init.allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs]
  rw [ctrFn_mx, keyFn_mx]
  decide +kernel

theorem init_spSafe : init.all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all]
  rw [ctrFn_spSafe, keyFn_spSafe]
  decide +kernel

theorem init_xdepth : init.x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  have := keyFn_depth
  simp only [init, Code.x86_64Depth, Nat.max_le, stkN]
  omega_arith

theorem init_correct (s : State) (hs : Proof.Sm4Gcm.initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

/-- A state satisfying `vg_sm4_gcm_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified :
    Verified X86_64.target init (Proof.Sm4Gcm.initScratchContract X86_64.abi stkN) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initPost,
      Proof.Sm4Gcm.initX86_64, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk,
      Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret, stkN, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSat] using initSat)

section
variable (v : GcmImpl)

theorem streamEncrypt_mx : (streamEncrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamEncrypt_spSafe : (streamEncrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamEncrypt_xdepth : (streamEncrypt v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega_using [this]

theorem streamEncrypt_correct (s : State) (hs : Proof.Sm4Gcm.streamEncryptX86_64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncrypt_mx v) he hg, hp⟩

theorem streamDecrypt_mx : (streamDecrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamDecrypt_spSafe : (streamDecrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamDecrypt_xdepth : (streamDecrypt v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega_using [this]

theorem streamDecrypt_correct (s : State) (hs : Proof.Sm4Gcm.streamDecryptX86_64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecrypt_mx v) he hg, hp⟩

theorem streamFinish_mx : (streamFinish v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamFinish_spSafe : (streamFinish v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamFinish_xdepth : (streamFinish v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega_using [this]

theorem streamFinish_correct (s : State) (hs : Proof.Sm4Gcm.streamFinishX86_64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamFinishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamFinish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamFinish_mx v) he hg, hp⟩

theorem streamVerify_mx : (streamVerify v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem streamVerify_spSafe : (streamVerify v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem streamVerify_xdepth : (streamVerify v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega_using [this]

theorem streamVerify_correct (s : State) (hs : Proof.Sm4Gcm.streamVerifyX86_64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.streamVerifyX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamVerify_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamVerify_mx v) he hg, hp⟩

theorem seal_mx : («seal» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem seal_xdepth : («seal» v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega_using [this]

theorem seal_correct (s : State) (hs : Proof.Sm4Gcm.sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_mx : («open» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.allInstrs, ctrFn_mx, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  rw [ctrFn_mx]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.all, ctrFn_spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  rw [ctrFn_spSafe]
  decide +kernel

theorem open_xdepth : («open» v.callees).x86_64Depth ≤ stkN := by
  have := ctrFn_depth
  simp only [streamEncrypt, streamDecrypt, streamText, streamFinish, streamVerify, «seal», «open», cryptWhole,
    cryptTail, crypt, cryptAl, tag, finTag, oneCrypt, oneTag, cryptHead, absorb, absorbPad, absorbHead,
    absorbWhole, absorbTail, padTail, ghash1, lens, flush, j0, j0hash, recv, cmp, tagOut, tagLenOk, partWith,
    firstFlush, oneAad, xorLoop, xorLoopG, minLen, copyLoop, Impl.AesGcm.X86_64.copyTag, GcmImpl.callees, ↓reduceIte, Bool.false_eq_true, Code.x86_64Depth, v.gh.noStack, Nat.max_le, stkN]
  omega_using [this]

theorem open_correct (s : State) (hs : Proof.Sm4Gcm.openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.Sm4Gcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

end

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and `_decrypt` (with no data, and
`scratch` at 0). -/
def crSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .r8 => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0, 768⟩]

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamEncrypt v.callees)
      (Proof.Sm4Gcm.streamEncryptScratchContract96 X86_64.abi stkN) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract96, Proof.Sm4Gcm.streamCryptScratchSig96,
      Spec.Sm4.Gcm.streamEncryptPost, Proof.Sm4Gcm.streamEncryptX86_64, Proof.Sm4Gcm.streamCryptPre,
      Proof.Sm4Gcm.streamCryptPub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamDecrypt v.callees)
      (Proof.Sm4Gcm.streamDecryptScratchContract96 X86_64.abi stkN) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract96, Proof.Sm4Gcm.streamCryptScratchSig96,
      Spec.Sm4.Gcm.streamDecryptPost, Proof.Sm4Gcm.streamDecryptX86_64, Proof.Sm4Gcm.streamCryptPre,
      Proof.Sm4Gcm.streamCryptPub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition. -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .r8 => 0x5000 | .r9 => 0x6000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x6000, 768⟩]

theorem streamFinish_verified (v : GcmImpl) :
    Verified X86_64.target (streamFinish v.callees)
      (Proof.Sm4Gcm.streamFinishScratchContract96 X86_64.abi stkN) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract96, Proof.Sm4Gcm.streamFinishScratchSig96,
      Spec.Sm4.Gcm.streamFinishPost, Proof.Sm4Gcm.streamFinishX86_64, Proof.Sm4Gcm.finPre,
      X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSat] using finSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def verSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .r8 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamVerify_verified (v : GcmImpl) :
    Verified X86_64.target (streamVerify v.callees)
      (Proof.Sm4Gcm.streamVerifyScratchContract96 X86_64.abi stkN) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Proof.Sm4Gcm.streamVerifyScratchContract96, Proof.Sm4Gcm.streamVerifyScratchSig96,
      Spec.Sm4.Gcm.streamVerifyPost, Proof.Sm4Gcm.streamVerifyX86_64, Proof.Sm4Gcm.verifyPre,
      X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSat] using verSat)

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce, additional data or data, `tag`
at `0x3000` and `work` at 0). -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 2560⟩]

theorem seal_verified (v : GcmImpl) :
    Verified X86_64.target («seal» v.callees) (Proof.Sm4Gcm.sealScratchContract X86_64.abi stkN) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig, Spec.Sm4.Gcm.sealPost,
      Proof.Sm4Gcm.sealX86_64, Proof.Sm4Gcm.sealPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub,
      X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using sealSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition (with no nonce, additional data, data or tag, and
`work` at 0). -/
def openSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : GcmImpl) :
    Verified X86_64.target («open» v.callees) (Proof.Sm4Gcm.openScratchContract X86_64.abi stkN) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
        Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      post := by sig_implies_post [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
        Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
          Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
          Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
        sig_simp [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
          Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, Proof.Sm4Gcm.openX86_64, Proof.Sm4Gcm.openLeak,
        Proof.Sm4Gcm.openPre, Proof.Sm4Gcm.oneLay, Proof.Sm4Gcm.onePub, X86_64.abi, Proof.Sm4Gcm.arg, Proof.Sm4Gcm.args, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk, Proof.Sm4Gcm.ret,
      stkN, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [openSat] using openSat }

end VG.Proof.Sm4Gcm.X86_64

end

end


/-!
# SM4-GCM on x86-64, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it, as AES-GCM's
(`Proof/AesGcm/X86_64/Frame.lean`), below which its calls use the `stkN`
bytes that a call of `vg_sm4_ctr32` takes. `init` and `stream_finish`, whose
working space is their last argument in a register, have a frame of 2568
bytes (`Verified.stackScratch`): the 2560 bytes of working space, and 8 more
to keep `rsp` aligned. The working space of the others is their last
argument, passed on the stack after the six argument registers and their
other stack arguments: their frames (`Verified.stackArgScratch`) also hold a
copy of those, 2576 bytes for `stream_encrypt`, `stream_decrypt` and
`stream_verify` (none), 2592 for `seal` (two) and 2600 for `open` (three,
and a leak, whether it succeeds, which reads only its buffers:
`openLeak_local`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.Impl.Sm4Gcm.X86_64
open VG.Proof.AesGcm.X86_64 (GcmImpl)

variable (v : GcmImpl)

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract X86_64.abi 5792).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rdx init)
      (Spec.Sm4.Gcm.initContract X86_64.abi 5792) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (post := Spec.Sm4.Gcm.initPost X86_64.abi.ptrBits) (wa := true) (stack := stkN) (bytes := 2568)
    init_verified (by decide) (by decide) (by decide) init_spSafe init_xdepth initFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space. -/
def crFrameSat : State := { crSat with rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre :
    ∃ s, (Spec.Sm4.Gcm.streamEncryptContract X86_64.abi 4008).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamEncrypt v.callees))
      (Spec.Sm4.Gcm.streamEncryptContract X86_64.abi 4008) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 784) (streamEncrypt_verified v) (by decide) (by decide) (by decide)
    (streamEncrypt_spSafe v) (streamEncrypt_xdepth v) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.streamEncryptPost_local _) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre :
    ∃ s, (Spec.Sm4.Gcm.streamDecryptContract X86_64.abi 4008).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, X86_64.abi, X86_64.argRegs] [crFrameSat, crSat] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamDecrypt v.callees))
      (Spec.Sm4.Gcm.streamDecryptContract X86_64.abi 4008) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 784) (streamDecrypt_verified v) (by decide) (by decide) (by decide)
    (streamDecrypt_spSafe v) (streamDecrypt_xdepth v) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.streamDecryptPost_local _) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract X86_64.abi 4000).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig,
    Spec.Sm4.Gcm.streamFinishPost, X86_64.abi, X86_64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 776 .r9 (streamFinish v.callees))
      (Spec.Sm4.Gcm.streamFinishContract X86_64.abi 4000) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamFinishPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 776) (streamFinish_verified v) (by decide) (by decide) (by decide)
    (streamFinish_spSafe v) (streamFinish_xdepth v) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩], wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract X86_64.abi 4008).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig,
    Spec.Sm4.Gcm.streamVerifyPost, X86_64.abi, X86_64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamVerify v.callees))
      (Spec.Sm4.Gcm.streamVerifyContract X86_64.abi 4008) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamVerifyPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 784) (streamVerify_verified v) (by decide) (by decide) (by decide)
    (streamVerify_spSafe v) (streamVerify_xdepth v) (Proof.Sm4Gcm.pre_local _ _)
    (Proof.Sm4Gcm.streamVerifyPost_local _) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract X86_64.abi 5816).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2592 2 («seal» v.callees))
      (Spec.Sm4.Gcm.sealContract X86_64.abi 5816) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.sealPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (bytes := 2592) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.sealPost_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract X86_64.abi 5824).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («open» v.callees))
      (Spec.Sm4.Gcm.openContract X86_64.abi 5824) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.openPost X86_64.abi.ptrBits) (wa := true)
    (stack := stkN) (leak := some (Spec.Sm4.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2600)
    (open_verified v) (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v)
    (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.openPost_local _) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local _)

/-! ## Without secret residue

Each function followed by the clearing of its whole stack
(`X86_64.Scrub.withScrubAll`): its own frame, and below it the frames of
`vg_sm4_ctr32` and `vg_sm4_expand_key`, which leave them as they are (the
working space they share: the key schedule they prepare and the keystream,
cleared once here for all the calls). Their postconditions read the memory
on return only within the buffers (`X86_64.Scrub.PostOut`). -/

section Scrub

open VG.X86_64.Scrub

theorem bytesAt_of0 {m₁ m₂ : Mem} {p : Addr} {L n : Nat}
    (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n :=
  Proof.AesGcm.bytesAt_congr fun i hi => Proof.AesGcm.agree_of h i (by omega_using [hi, hn])

theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L d n : Nat}
    (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n :=
  Proof.AesGcm.bytesAt_congr_off hn (Proof.AesGcm.agree_of h)

theorem initOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.initContract X86_64.abi stack) (Spec.Sm4.Gcm.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, ctx], _ =>
      simp only [Spec.Sm4.Gcm.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      change Spec.Sm4.Gcm.KeyRepr m₁ ctx _ at h
      change Spec.Sm4.Gcm.KeyRepr m₂ ctx _
      obtain ⟨h1, h2⟩ := h
      have ha := Proof.AesGcm.agree_of hb.2
      refine ⟨?_, ?_⟩
      · rw [Proof.Sm4.scheduleAt_congr fun k hk => ha k (by omega_using [hk])]
        exact h1
      · simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [bytesAt_of hb.2 (by decide)]
        exact h2

theorem sealOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.sealContract X86_64.abi stack) (Spec.Sm4.Gcm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Sm4.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      show _ = (Spec.Aes.bytesAt m₂ data len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [bytesAt_of0 hb.2.2.2.1 (by omega_arith), bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h

theorem openOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.openContract X86_64.abi stack) (Spec.Sm4.Gcm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, nonce, nl, aad, al, data, len, tag, tl], _ =>
      simp only [Spec.Sm4.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      show (match Spec.Gcm.openResult (Spec.Sm4.Gcm.ctxCiph m ctx) (Spec.Gcm.ctxH m ctx) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m data len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ data len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ data len.toNat = Spec.Aes.bytesAt m data len.toNat)
      rw [bytesAt_of0 hb.2.2.2.1 (by omega_arith)]
      exact h

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamEncryptContract X86_64.abi stack) (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, tl, data, len], _ =>
      simp only [Spec.Sm4.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro iv a p hr hA hT
      obtain ⟨h1, h2⟩ := h iv a p hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamDecryptContract X86_64.abi stack) (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, tl, data, len], _ =>
      simp only [Spec.Sm4.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro iv a c hr hA hT
      obtain ⟨h1, h2⟩ := h iv a c hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamFinishContract X86_64.abi stack) (Spec.Sm4.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, tl, tag], _ =>
      simp only [Spec.Sm4.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro iv a c hr hA hT
      show Spec.Aes.bytesAt m₂ tag 16 = _
      rw [bytesAt_of0 hb.2.2 (by decide)]
      exact h iv a c hr hA hT

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamVerifyContract X86_64.abi stack) (Spec.Sm4.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, st, al, tl, tag, tagLen], _ => exact h

/-- `vg_sm4_gcm_init`, its whole stack cleared. -/
def initReg : Registration Spec.Sm4.Gcm.initApi X86_64.target :=
  withScrubAll {
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rdx init
    stack := 5792
    verified := init_framed
    spSafe := X86_64.withStackScratch_spSafe_of init_spSafe } (initOut _)

/-- `vg_sm4_gcm_seal` over `v`, its whole stack cleared. -/
def sealReg : Registration Spec.Sm4.Gcm.sealApi X86_64.target :=
  withScrubAll {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2592 2 («seal» v.callees)
    stack := 5816
    verified := seal_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v) } (sealOut _)

/-- `vg_sm4_gcm_open` over `v`, its whole stack cleared. -/
def openReg : Registration Spec.Sm4.Gcm.openApi X86_64.target :=
  withScrubAll {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («open» v.callees)
    stack := 5824
    verified := open_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v) } (openOut _)

/-- `vg_sm4_gcm_stream_encrypt` over `v`, its whole stack cleared. -/
def streamEncryptReg : Registration Spec.Sm4.Gcm.streamEncryptApi X86_64.target :=
  withScrubAll {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamEncrypt v.callees)
    stack := 4008
    verified := streamEncrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v) } (streamEncryptOut _)

/-- `vg_sm4_gcm_stream_decrypt` over `v`, its whole stack cleared. -/
def streamDecryptReg : Registration Spec.Sm4.Gcm.streamDecryptApi X86_64.target :=
  withScrubAll {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamDecrypt v.callees)
    stack := 4008
    verified := streamDecrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v) } (streamDecryptOut _)

/-- `vg_sm4_gcm_stream_finish` over `v`, its whole stack cleared. -/
def streamFinishReg : Registration Spec.Sm4.Gcm.streamFinishApi X86_64.target :=
  withScrubAll {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (streamFinish v.callees)
    stack := 4000
    verified := streamFinish_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamFinish_spSafe v) } (streamFinishOut _)

/-- `vg_sm4_gcm_stream_verify` over `v`, its whole stack cleared. -/
def streamVerifyReg : Registration Spec.Sm4.Gcm.streamVerifyApi X86_64.target :=
  withScrubAll {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 784 0 (streamVerify v.callees)
    stack := 4008
    verified := streamVerify_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe v) } (streamVerifyOut _)

end Scrub

end VG.Proof.Sm4Gcm.X86_64
