module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
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
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinCT
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
public import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Callee
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Init
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Sm4Gcm.X86_64.InitCT`, which only this module used -/

section

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The code around the calls
depends only on the pointers (checked by the taint analysis), and each call
of `vg_sm4_expand_key` and `vg_sm4_ctr32` has the same arguments in both runs:
the key at `key`, the schedule into `ctx`, and the zero block at `W + 96`
encrypted into `ctx + 240`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr save restore tO)
open VG.Proof.AesGcm.X86_64 (save_ok rel_taint rel_wp covers_left covers_cons covers_of_mem covers_off
  covers_prefix in_off add_ofNat_assoc ct_of_rel)

/-- After the entry of `init`: the call of `vg_sm4_expand_key`'s arguments. -/
def InitA (s₀ s : State) : Prop :=
  KeyCall s (s₀.gpr .rdi) (s₀.gpr .rsi) ∧ s.gpr .r15 = s₀.gpr .rdx ∧ s.gpr .r13 = s₀.gpr .rsi ∧
    s.gpr .rsp = s₀.gpr .rsp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- Between the calls: the registers `init` keeps. -/
def InitK (s₀ s : State) : Prop :=
  s.gpr .r15 = s₀.gpr .rdx ∧ s.gpr .r13 = s₀.gpr .rsi ∧ s.gpr .rsp = s₀.gpr .rsp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- Before the call of `vg_sm4_ctr32`: its arguments. -/
def InitB (s₀ s : State) : Prop :=
  CtrCall s (s₀.gpr .rsi) (s₀.gpr .rdx + BitVec.ofNat 64 96) (s₀.gpr .rsi + BitVec.ofNat 64 240) 1 ∧
    s.gpr .r15 = s₀.gpr .rdx ∧ s.gpr .rsp = s₀.gpr .rsp

theorem initA_ok {s : State} (hp : Proof.Sm4Gcm.initX86_64.pre s) :
    WP isa (.block (save .rdx ++ ([.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] : List Instr))) s (InitA s) := by
  simp only [Proof.Sm4Gcm.initX86_64, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_kc, -, -, -, -, k_k, k_c, -, wk, wc, -, hsp⟩ := hp
  have pW : Covers [⟨s.gpr .rdx, 2560⟩] s.wr := by
    rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨s.gpr .rsi, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := save_ok s .rdx rfl pW
  obtain ⟨s₂, run₂, h15, h13, hdi, hsi, hsp₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] s₁ = some s₂ ∧
      s₂.gpr .r15 = s.gpr .rdx ∧ s₂.gpr .r13 = s.gpr .rsi ∧ s₂.gpr .rdi = s.gpr .rdi ∧ s₂.gpr .rsi = s.gpr .rsi ∧
      s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, rd_setReg, wr_setReg, hg₁]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  have wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  refine ⟨⟨hdi, hsi, by rw [hsp₂]; exact hsp, wk, by omega_using [wc], d_kc.sub_right (Region.sub_prefix (by decide)),
    by rw [hsp₂]; exact k_k, by rw [hsp₂]; exact k_c.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩,
    h15, h13, hsp₂, rd₂, wr₂⟩
  · rw [rd₂, wr₂, hrd]
    exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
      (covers_left (covers_prefix pC (by decide)))
  · rw [wr₂]; exact covers_prefix pC (by decide)

theorem initB_ok {s₀ s : State} (hp : Proof.Sm4Gcm.initX86_64.pre s₀) (hk : InitK s₀ s) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
      .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ ([.mov32 .rcx (imm 1)] : List Instr))) s (InitB s₀) := by
  simp only [Proof.Sm4Gcm.initX86_64, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨-, hwr, -, -, d_cs, -, -, -, k_c, k_s, -, wc, ws, hsp⟩ := hp
  obtain ⟨g15, g13, gsp, rd₃, wr₃⟩ := hk
  unfold InitB
  generalize s₀.gpr .rsi = Ctx at *
  generalize s₀.gpr .rdx = W at *
  generalize s₀.gpr .rsp = SP at *
  have pW : Covers [⟨W, 2560⟩] s.wr := by
    rw [wr₃, hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [wr₃, hwr]; exact covers_of_mem (List.mem_cons_self ..)
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  have w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
  obtain ⟨s₄, run₄, hdi₄, hsi₄, hdx₄, hcx₄, h15₄, hsp₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
        .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] ++
        ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ [.mov32 .rcx (imm 1)]) s = some s₄ ∧
      s₄.gpr .rdi = Ctx ∧ s₄.gpr .rsi = W + BitVec.ofNat 64 96 ∧ s₄.gpr .rdx = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .rcx = BitVec.ofNat 64 1 ∧ s₄.gpr .r15 = W ∧ s₄.gpr .rsp = SP ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr := by
    refine ⟨_, by xrun [g15, g13, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, g13]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, g15]
    · simp [gpr_setReg, gpr_arithFlags, gsp]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₄, run₄, ?_, h15₄, hsp₄⟩
  have dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  have dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_using [])
  have pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [hwr₄]; exact pC
  have pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [hwr₄]; exact pW
  refine ⟨hdi₄, hsi₄, hdx₄, hcx₄, by rw [hsp₄]; exact hsp, by omega_using [wc],
    by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [ws],
    by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); omega_using [wc],
    by simpa using dCW 0 128 (by decide) 96 16 (by decide), dK0,
    (dCW 240 16 (by decide) 96 16 (by decide)).symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp₄]; exact k_c.sub_right (Region.sub_prefix (by decide))
  · rw [hsp₄]; exact k_s.sub_right (Offset.sub_base _ (by decide))
  · rw [hsp₄]; exact k_c.sub_right (Offset.sub_base _ (by decide))
  · exact covers_cons (covers_left (covers_prefix pC' (by decide))) (covers_cons
      (covers_left (covers_off pW' (by decide) (by decide)))
      (covers_left (covers_off pC' (by decide) (by decide))))
  · exact covers_cons (covers_off pW' (by decide) (by decide)) (covers_off pC' (by decide) (by decide))

theorem init_rel {s₀ s₀' : State} (hp : Proof.Sm4Gcm.initX86_64.pre s₀)
    (hp' : Proof.Sm4Gcm.initX86_64.pre s₀') (hq : Proof.Sm4Gcm.initX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') init fun _ _ => True := by
  obtain ⟨q₁, q₂, q₃, q₄⟩ := hq
  have hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s₀.gpr r = s₀'.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  -- The entry, and the call of `vg_sm4_expand_key`.
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (c := .block (save .rdx ++ ([.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] : List Instr)))
      [.rdi, .rsi, .rdx, .rsp] (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hag) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (G₁ := InitA s₀) (G₂ := InitA s₀')
    (fun s h => by subst h; exact initA_ok hp) (fun s h => by subst h; exact initA_ok hp')
  have hK : ∀ {t₀ : State}, ∀ s, InitA t₀ s → WP isa (.call keyFn.name keyFn.code) s (InitK t₀) :=
    fun s ⟨kc, h15, h13, hsp, hrd, hwr⟩ => WP.mono (key_call kc) fun _ g =>
      ⟨by rw [g.saved _ (by decide), h15], by rw [g.saved _ (by decide), h13], by rw [g.saved _ (by decide), hsp],
        g.rd.trans hrd, g.wr.trans hwr⟩
  have b := rel_wp (key_rel (P := fun s₁ s₂ => True ∧ InitA s₀ s₁ ∧ InitA s₀' s₂) fun s₁ s₂ h =>
      ⟨_, _, h.2.1.1, by rw [q₁, q₂]; exact h.2.2.1, by rw [h.2.1.2.2.2.1, h.2.2.2.2.2.1, q₄]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hK hK
  -- The arguments of the call of `vg_sm4_ctr32`, and the call.
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ InitK s₀ s₁ ∧ InitK s₀' s₂) [.r13, .r15, .rsp]
      (fun _ _ h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1, q₂]
        · rw [h.2.1.1, h.2.2.1, q₃]
        · rw [h.2.1.2.2.1, h.2.2.2.2.1, q₄]) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun s h => initB_ok hp h) (fun s h => initB_ok hp' h)
  have hC : ∀ {t₀ : State}, ∀ s, InitB t₀ s → WP isa (.call ctrFn.name ctrFn.code) s fun s' =>
      s'.gpr .r15 = t₀.gpr .rdx := fun s ⟨cc, h15, _⟩ => WP.mono (ctr_call cc) fun _ g =>
    by rw [g.saved _ (by decide), h15]
  have d := rel_wp (ctr_rel (P := fun s₁ s₂ => True ∧ InitB s₀ s₁ ∧ InitB s₀' s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.2.1.1, by rw [q₂, q₃]; exact h.2.2.1, by rw [h.2.1.2.2, h.2.2.2.2, q₄]⟩)
    (fun _ _ h => ⟨h.2.1, h.2.2⟩) hC hC
  -- `restore`, from `W`.
  have e := rel_taint (P := fun s₁ s₂ => True ∧ s₁.gpr .r15 = s₀.gpr .rdx ∧ s₂.gpr .r15 = s₀'.gpr .rdx)
    (c := .block restore) [.r15] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1, h.2.2, q₃]) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c (RelCT.seq d e)))

theorem init_ct :
    ConstantTime isa Proof.Sm4Gcm.initX86_64.pre Proof.Sm4Gcm.initX86_64.pub init :=
  ct_of_rel fun _ _ hp hp' hq => init_rel hp hp' hq

end VG.Proof.Sm4Gcm.X86_64

end

end

/-! ### `Sm4Gcm.X86_64.StreamCryptCT`, which only this module used -/

section

/-! ### `Sm4Gcm.X86_64.StreamCrypt`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86_64.StreamText`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86-64: the text of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. `streamText enc` pads the
additional data first if there is no text yet (AES-GCM's `firstFlush`), then
encrypts the data and absorbs the ciphertext (`enc`), or absorbs the
ciphertext and decrypts it, with `crypt` and AES-GCM's `absorb`, as AES-GCM's
does for fewer than 256 bytes (`Proof/AesGcm/X86_64/StreamText.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm tlenO alenO streamLoad partWith firstFlush absorb)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen ghashInput)
open VG.Proof.Gcm (Absorbed Ctr xorKs)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk absFrame tFrame AbsIn AbsOut FlOut absorb_ok flush_ok
  load_ok load_env ctext ctext_append length_ctext ctext_nil bytesAt_zero abs_frame ctr_frame test_ok eval_e
  bytesAt_frame blockAt_frame and15 imm_eq and_self_beq toNat_mod16 data_absFrame data_absFrame₀ length_bytesAt bytesAt_add
  WP.with_rdwr)

/-- What `streamText` writes. -/
abbrev stFrame (St W SP D : Addr) (n : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 64⟩, ⟨D, n⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP stkN]

theorem crFrame_st {St W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (crFrame St SP D n) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP stkN, by simp, fun _ h => h⟩

theorem absFrame_st {St W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (absFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, below8_stk SP⟩

theorem tFrame_st {St W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (tFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, below8_stk SP⟩

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768)
include L

theorem ctx_tFrame16 : ∀ r ∈ tFrame St W SP 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  · exact L.lay.kc.symm

theorem ctx_absFrame16 : ∀ r ∈ absFrame St W SP 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  · exact L.lay.kc.symm

theorem ctr_absFrame16 : ∀ r ∈ absFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.lay.stk_st (by decide)).symm

theorem ctr_tFrame16 : ∀ r ∈ tFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.lay.stk_st (by decide)).symm

theorem abs_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW4 Ctx St W SP s D n 768) :
    ∀ r ∈ crFrame St SP D n, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.dw.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact (L.ks.sub_right (Lay.stSub (by decide))).symm

/-- The slots of `W` from 176 are outside the regions the pieces write. -/
theorem slot_tFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact L.lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact L.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.lay.stk_w (by omega_arith)).symm

theorem slot_absFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ absFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact L.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.lay.stk_w (by omega_arith)).symm

theorem slot_crFrame {s : State} {D : Addr} {n d : Nat} (hd : DataW4 Ctx St W SP s D n 768) (h₁ : 176 ≤ d)
    (h₂ : d + 8 ≤ 512) : ∀ r ∈ crFrame St SP D n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.dw.ok.w.sub_right (Lay.wSub (by omega_arith))).symm
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact (L.kw.sub_right (Lay.wSub (by omega_arith))).symm

omit L in
theorem data_tFrame {s : State} {D : Addr} {n : Nat} (hd : DataW4 Ctx St W SP s D n 768) :
    ∀ r ∈ tFrame St W SP 16, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.dw.ok.st.sub_right (Lay.stSub (by decide))
  · exact hd.dw.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.dw.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.dw.ok.stk.symm

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768)
include L

/-- Before the text: the additional data padded if there is no text yet. -/
theorem start_ok {Hyp : Prop} {H : Block} {m₀ : Mem} {s : State} (he : Env Ctx St W SP s 768) (hm : s.mem = m₀)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64) (hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀)) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s fun s' => Env Ctx St W SP s' 768 ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame (tFrame St W SP 16) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length) ++ c₀)) := by
  obtain r₂ := he.perm.wR (show 192 + 8 ≤ 768 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (c₀.length = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain he₂ : Env Ctx St W SP s₂ 768 := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  obtain hm₂' : s₂.mem = m₀ := hm₂.trans hm
  refine WP.ite (decide (c₀.length = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => ?_)
  · have hc : c₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
    subst hc
    obtain r₃ := he₂.perm.wR (show 184 + 8 ≤ 768 by decide)
    obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (a.length % 16) ∧
        (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
      obtain hand := and15 (BitVec.ofNat 64 a.length)
      rw [imm_eq (by decide), toNat_mod16] at hand
      refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
      · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    unfold firstFlush
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ : Env Ctx St W SP s₃ 768 := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    obtain hm₃' : s₃.mem = m₀ := hm₃.trans hm₂'
    refine WP.mono (WP.with_rdwr (flush_ok v L.lay (yo := 16) (.inr rfl) (H := H) (x := a)
      ⟨he₃, by rw [hm₃']; exact hH⟩ hbx₃)) fun s₄ ⟨fo, rd₄, wr₄⟩ =>
        ⟨fo.env, by rw [rd₄, hrd₃, hrd₂], by rw [wr₄, hwr₃, hwr₂], hm₃' ▸ fo.frame, fun hy => ?_⟩
    rw [List.append_nil]
    exact fo.abs (by rw [hm₃']; exact hyA hy)
  · have hc : c₀ ≠ [] := fun e => by subst e; simp_all
    refine WP.block_nil ⟨he₂, hrd₂, hwr₂, by rw [hm₂']; exact Frame.refl _ _, fun hy => ?_⟩
    rw [hm₂', ← Proof.Gcm.ghashInput_of_ne hc]
    exact hyA hy

/-- `streamText enc`: the `n` bytes at `D` encrypted (`enc`) or decrypted,
and their ciphertext absorbed, after additional data `a` and text `c₀`. -/
theorem streamText_ok (enc : Bool) {Hyp : Prop} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem} {s : State}
    (he : Env Ctx St W SP s 768) (hm : s.mem = m₀) (hd : DataW4 Ctx St W SP s D n 768)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb c₀.length) :
    WP isa (streamText v.callees enc) s fun s' => Env Ctx St W SP s' 768 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx) icb c₀.length (bytesAt m₀ D n)) := by
  have hlt := hd.dw.ok.lt
  obtain hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega_arith
  simp only [streamText]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx St W SP s₁ 768 := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₁, hrd₁, hwr₁, by rw [hm₁, hm]; exact Frame.refl _ _, fun hy => ⟨?_, ?_, rfl⟩⟩
    · rw [bytesAt_zero, ctext_nil, List.append_nil, hm₁, hm]; exact hyA hy
    · rw [hm₁, hm]; exact hyC hy
  obtain h0 : n ≠ 0 := by simpa using hf
  refine WP.assoc (WP.seq (WP.mono (start_ok v L he₁ (hm₁.trans hm) hP hH (by rw [hm₁]; exact hal)
    (by rw [hm₁]; exact htl) hyA) fun s₂ ⟨he₂, rd₂, wr₂, f₂, ha₂⟩ => ?_))
  -- The slots of `W`, the hash subkey, the cipher, the counter and the data, through the padding.
  obtain sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_tFrame L h₁ h₂) (by decide), hm]
  obtain hd₂ : DataW4 Ctx St W SP s₂ D n 768 := hd.of_eq (rd₂.trans hrd₁) (wr₂.trans hwr₁)
  obtain hc₂ : ciphOf s₂.mem Ctx = ciphOf m₀ Ctx := ciph_frame f₂ (ctx_tFrame16 L)
  obtain hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame f₂ fun r hr => (ctx_tFrame16 L r hr).sub_left (Lay.ctxSub (by decide)), hH]
  obtain hD₂ : bytesAt s₂.mem D n = bytesAt m₀ D n := bytesAt_frame f₂ (data_tFrame hd) (by omega_arith)
  obtain hC₂ : Hyp → Ctr s₂.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb c₀.length :=
    fun hy => ctr_frame f₂ (ctr_tFrame16 L) (hyC hy)
  -- The data, its length and the text so far modulo 16.
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok he₂
    ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
    ((sl₂ 192 (by decide) (by decide)).trans htl)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  obtain he₃ := he₂.keep (load_env hg₃) hrd₃ hwr₃
  obtain hd₃ : DataW4 Ctx St W SP s₃ D n 768 := hd₂.of_eq hrd₃ hwr₃
  obtain sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃]; exact sl₂ d h₁ h₂
  obtain hne : ∀ y : List Byte, y.length = n → c₀ ++ y ≠ [] := fun y hy e => h0 (by
    have := congrArg List.length e
    rw [List.length_append, hy, List.length_nil] at this
    omega_arith)
  cases enc
  · -- Decrypting: the ciphertext absorbed, then decrypted.
    simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    obtain hai : AbsIn Ctx St W SP 16 H (a ++ zeros (padLen a.length) ++ c₀) D n s₃ 768 :=
      ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hx], hd₃.dw.ok, by rw [hm₃]; exact hH₂⟩
    refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok v L.lay (.inr rfl) hai)) fun s₄ ⟨ao, rd₄, wr₄⟩ => ?_)
    obtain sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ h₂)
        (by decide), sl₃ d h₁ h₂]
    obtain ⟨s₅, run₅, h12₅, hbp₅, hbx₅, hg₅, hm₅, hrd₅, hwr₅⟩ := load_ok ao.env
      ((sl₄ 200 (by decide) (by decide)).trans hdat) ((sl₄ 208 (by decide) (by decide)).trans hlen)
      ((sl₄ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
    rw [toNat_mod16] at hbx₅
    obtain he₅ := ao.env.keep (load_env hg₅) hrd₅ hwr₅
    obtain hd₅ : DataW4 Ctx St W SP s₅ D n 768 := hd₃.of_eq (by rw [hrd₅, rd₄]) (by rw [hwr₅, wr₄])
    obtain hc₅ : ciphOf s₅.mem Ctx = ciphOf m₀ Ctx := by
      rw [hm₅, ciph_frame ao.frame (ctx_absFrame16 L), hm₃, hc₂]
    obtain hD₅ : bytesAt s₅.mem D n = bytesAt m₀ D n := by
      rw [hm₅, bytesAt_frame ao.frame (data_absFrame (yo := 16) (.inr rfl) (gs := 256) (.inr (by decide)) hd₃.dw.ok) (by omega_arith), hm₃, hD₂]
    refine WP.mono (WP.with_rdwr (crypt_ok L (icb := icb) (P := c₀.length) ⟨he₅, h12₅, hbp₅, hbx₅, hd₅⟩))
      fun s₆ ⟨co, rd₆, wr₆⟩ => ⟨co.env, by rw [rd₆, hrd₅, rd₄, hrd₃, rd₂, hrd₁], by rw [wr₆, hwr₅, wr₄, hwr₃, wr₂, hwr₁],
        (tFrame_st f₂).trans ((hm₃ ▸ absFrame_st ao.frame).trans (hm₅ ▸ crFrame_st co.frame)), fun hy => ⟨?_, ?_, ?_⟩⟩
    · have A := abs_frame co.frame (abs_crFrame L hd₅) (hm₅ ▸ ao.abs (hm₃ ▸ ha₂ hy))
      rw [hm₃, hD₂] at A
      simp only [ctext, Bool.false_eq_true, ↓reduceIte]
      rw [Proof.Gcm.ghashInput_of_ne (hne _ (length_bytesAt _ _ _)), ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hc₅] at C
      exact C (hm₅ ▸ ctr_frame ao.frame (ctr_absFrame16 L) (hm₃ ▸ hC₂ hy))
    · have C := co.out
      rw [hc₅, hD₅] at C
      exact C (hm₅ ▸ ctr_frame ao.frame (ctr_absFrame16 L) (hm₃ ▸ hC₂ hy))
  · -- Encrypting: the plaintext encrypted, then the ciphertext absorbed.
    simp only [partWith, ↓reduceIte]
    obtain hc₃ : ciphOf s₃.mem Ctx = ciphOf m₀ Ctx := by rw [hm₃, hc₂]
    refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L (icb := icb) (P := c₀.length) ⟨he₃, h12₃, hbp₃, hbx₃, hd₃⟩))
      fun s₄ ⟨co, rd₄, wr₄⟩ => ?_)
    obtain sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hd₃ h₁ h₂)
        (by decide), sl₃ d h₁ h₂]
    obtain ⟨s₅, run₅, h12₅, hbp₅, hbx₅, hg₅, hm₅, hrd₅, hwr₅⟩ := load_ok co.env
      ((sl₄ 200 (by decide) (by decide)).trans hdat) ((sl₄ 208 (by decide) (by decide)).trans hlen)
      ((sl₄ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
    rw [toNat_mod16] at hbx₅
    obtain he₅ := co.env.keep (load_env hg₅) hrd₅ hwr₅
    obtain hd₅ : DataW4 Ctx St W SP s₅ D n 768 := hd₃.of_eq (by rw [hrd₅, rd₄]) (by rw [hwr₅, wr₄])
    obtain hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₅, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₃ r hr).sub_left (Lay.ctxSub (by decide))),
        hm₃, hH₂]
    obtain hai : AbsIn Ctx St W SP 16 H (a ++ zeros (padLen a.length) ++ c₀) D n s₅ 768 :=
      ⟨he₅, h12₅, hbp₅, by rw [hbx₅, hx], hd₅.dw.ok, hH₅⟩
    refine WP.mono (WP.with_rdwr (absorb_ok v L.lay (.inr rfl) hai))
      fun s₆ ⟨ao, rd₆, wr₆⟩ => ⟨ao.env, by rw [rd₆, hrd₅, rd₄, hrd₃, rd₂, hrd₁], by rw [wr₆, hwr₅, wr₄, hwr₃, wr₂, hwr₁],
        (tFrame_st f₂).trans ((hm₃ ▸ crFrame_st co.frame).trans (hm₅ ▸ absFrame_st ao.frame)), fun hy => ⟨?_, ?_, ?_⟩⟩
    · have C := co.out
      rw [hc₃, hm₃, hD₂] at C
      obtain o := C (hm₃ ▸ hC₂ hy)
      obtain A := ao.abs (hm₅ ▸ abs_frame co.frame (abs_crFrame L hd₃) (hm₃ ▸ ha₂ hy))
      rw [hm₅, o] at A
      simp only [ctext, ↓reduceIte]
      rw [Proof.Gcm.ghashInput_of_ne (hne _ (Proof.Gcm.length_xorKs _ _ _ _ |>.trans (length_bytesAt _ _ _))),
        ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hc₃, hm₃] at C
      exact ctr_frame ao.frame (ctr_absFrame16 L) (hm₅ ▸ C (hC₂ hy))
    · have C := co.out
      rw [hc₃, hm₃, hD₂] at C
      rw [bytesAt_frame ao.frame (data_absFrame (yo := 16) (.inr rfl) (gs := 256) (.inr (by decide)) hd₅.dw.ok) (by omega_arith), hm₅]
      exact C (hC₂ hy)

end

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry keeps the public
arguments in `W` (`cryptEntry_ok`), from what the precondition gives
(`CryptCtx`); `streamText` follows (`StreamText.lean`), then the exit, for
any message the state represents (`streamText_run`): encrypting appends the
ciphertext it writes (`streamEncrypt_wp`), decrypting the ciphertext it reads
(`streamDecrypt_wp`), as AES-GCM's (`Proof/AesGcm/X86_64/StreamCryptCT.lean`,
`StreamRun.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm save restore saved alenO tlenO dataO lenO)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput gctr inc32)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm DataOk DataW save_ok exit_ok SavedAt savedR ret_kept
  covers_left covers_of_mem in_off add_ofNat_assoc and15 imm_eq bytesAt_frame blockAt_frame ctxH_eq ofNat_lit
  ctext length_ctext length_bytesAt abs_frame ctr_frame WP.forall_det)

/-- What the entry writes in `W`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- After `cryptEntry`. -/
structure CryptEntry (s₀ : State) (Ctx St W SP D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s 768
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rdx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .rcx
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 ((s₀.gpr .rcx).toNat % 16)
  saved : SavedAt s.mem W s₀
  frame : Frame [entryR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cryptEntry_ok {s : State} {Ctx St W SP D : Addr} {n : Nat} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rsi = St)
    (hD : s.gpr .r8 = D) (hSP : s.gpr .rsp = SP) (hW : stackArg s 0 = W) (hn : (s.gpr .r9).toNat = n)
    (hperm : Perm Ctx St W s 768) (hargs : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8) :
    WP isa (.block cryptEntry) s (CryptEntry s Ctx St W SP D n) := by
  have hW' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = W := by rw [← hW, ← hSP]; rfl
  have h9 : s.gpr .r9 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 8))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, hargs], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx St W s₀ 768 := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 768 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 768 by decide) (by decide)
  have w₄ := in_off hperm.w (show 200 + 8 ≤ 768 by decide) (by decide)
  have w₅ := in_off hperm.w (show 208 + 8 ≤ 768 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₂ w₃ w₄ w₅
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 768 → d + 8 ≤ 768 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega_using [ha]) (by omega_using [hd])
  have q4 := sep 184 192 (by decide) (by decide) (by decide)
  have q5 := sep 184 200 (by decide) (by decide) (by decide)
  have q6 := sep 184 208 (by decide) (by decide) (by decide)
  have q7 := sep 192 200 (by decide) (by decide) (by decide)
  have q8 := sep 192 208 (by decide) (by decide) (by decide)
  have q9 := sep 200 208 (by decide) (by decide) (by decide)
  have hand := and15 (s.gpr .rcx)
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
        .store (at_ .r15 alenO) .rdx, .store (at_ .r15 tlenO) .rcx, .store (at_ .r15 dataO) .r8,
        .mov .rbp (.reg .r9), .store (at_ .r15 lenO) .rbp, .mov .r12 (.reg .r8), .mov .rbx (.reg .rcx),
        .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧ s₂.gpr .rbp = BitVec.ofNat 64 n ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((s.gpr .rcx).toNat % 16) ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = (((s₁.mem.writeW (W + BitVec.ofNat 64 184) (s.gpr .rdx)).writeW (W + BitVec.ofNat 64 192)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 200) D).writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₂, w₃, w₄, w₅], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, hrsi, hSt]
    · simp [gpr_setReg, hrdi, hCtx]
    · simp [gpr_setReg, hr8, hD]
    · simp [gpr_setReg, hr9, h9]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hrcx, hand]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags,
        Mem.readW_writeW_sep, hrdx, hrcx, hr8, hr9, hD, h9]
    all_goals rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 184, 32⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 184 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 184, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 184 ∧ v = s.gpr .rdx) ∨ (d = 192 ∧ v = s.gpr .rcx) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, rd 184 _ (.inl ⟨rfl, rfl⟩),
    rd 192 _ (.inr (.inl ⟨rfl, rfl⟩)), rd 200 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))),
    rd 208 _ (.inr (.inr (.inr ⟨rfl, rfl⟩))), h12, hbp, hbx, ?_, ?_, hrd', hwr'⟩
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by omega_using []) (by omega_using [])
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- What the precondition of `encrypt` and `decrypt` gives. -/
structure CryptCtx (s : State) (Ctx St W SP D : Addr) (n : Nat) : Prop where
  lay : Lay4 Ctx St W SP 768
  perm : Perm Ctx St W s 768
  args : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8
  data : DataW4 Ctx St W SP s D n 768
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 768⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 768⟩

theorem CryptCtx.of {s : State} (hp : Proof.Sm4Gcm.streamCryptPre s) :
    CryptCtx s (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) (s.gpr .r8) (s.gpr .r9).toNat := by
  simp only [Proof.Sm4Gcm.streamCryptPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.args,
    Proof.Sm4Gcm.arg, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_cs, d_cd, d_cw, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, r_s, r_d, r_w, t_c, t_s, t_d, t_w,
    wc, ws, wd, ww, sp, wsp⟩ := hp
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_sa d_da d_wa
  obtain L : Lay4 (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) 768 := Lay4.of wc ws ww d_cs d_cw d_sw sp t_c t_s t_w
  obtain pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_, ⟨⟨⟨?_, by have := (s.gpr .r9).isLt; omega_using [], wd, d_sd.symm, d_dw,
    t_d.sub_left (below8_stk _)⟩, ?_, d_cd⟩, t_d⟩, r_d, r_s, r_w, d_dw⟩
  · rw [hrd]; intro a m ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), by simp only [Region.Contains] at hc ⊢; omega_using [hc]⟩
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · simpa using in_off pm (show 0 + 8 ≤ 8 by decide) (by decide)
  · rw [hwr]; exact covers_left (covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768)
include L

/-- The slots of `W` below `176` are outside `stFrame`. -/
theorem w_stFrame {D : Addr} {n d k : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 768⟩) (h₁ : 128 ≤ d)
    (h₂ : d + k ≤ 176) : ∀ r ∈ stFrame St W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega_using [h₁], by omega_using [h₂]⟩)).symm
  · exact (hD.sub_right (Lay.wSub (by omega_using [h₂]))).symm
  · exact L.lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
  · exact L.lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
  · exact (L.kw.sub_right (Lay.wSub (by omega_using [h₂]))).symm

/-- `J₀` is outside `stFrame`. -/
theorem j0_stFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ stFrame St W SP D n, (⟨St, 16⟩ : Region).Disjoint r := by
  intro r hr
  obtain e : (⟨St, 16⟩ : Region) = ⟨St + BitVec.ofNat 64 0, 16⟩ := by rw [BitVec.add_zero]
  rw [e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.stSub (by decide))).symm
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.ks.sub_right (Lay.stSub (by decide))).symm

omit L in
/-- The return address is outside `stFrame`. -/
theorem ret_stFrame {D : Addr} {n : Nat} (rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩)
    (rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) (rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 768⟩) :
    ∀ r ∈ stFrame St W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact rS.sub_right (Lay.stSub (by decide))
  · exact rD
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact ret_stk SP

end

/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, for the message
the state represents, with ciphertext `c₀` so far. -/
theorem streamText_run (v : GcmImpl) (enc : Bool) {s : State} (hp : Proof.Sm4Gcm.streamCryptPre s)
    {iv a c₀ : List Byte} (hA : s.gpr .rdx = BitVec.ofNat 64 a.length) (hT : (s.gpr .rcx).toNat = c₀.length) :
    WP isa (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block restore))) s fun s' =>
      gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi)
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rsi) ciph h iv a c₀ →
        StreamRepr s'.mem (s.gpr .rsi) ciph h iv a
          (c₀ ++ ctext enc ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) ∧
        bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
          xorKs ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) := by
  obtain C := CryptCtx.of hp
  obtain hP : c₀.length < 2 ^ 64 := hT ▸ (s.gpr .rcx).isLt
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hW : stackArg s 0 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r8 = D at *
  generalize hn : (s.gpr .r9).toNat = n at *
  have L := C.lay
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx = ciph
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.args) fun s₁ E => ?_)
  obtain dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (d := 240) (by decide))), ← hH, ctxH_eq]
  obtain hc₁ : ciphOf s₁.mem Ctx = ciph := by rw [ciph_frame E.frame dCE, ← hciph]; rfl
  obtain eS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [entryR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.st_w hk (.inr ⟨by decide, by decide⟩)
  obtain hyA : StreamRepr s.mem St ciph H iv a c₀ → Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀) :=
    fun hy => by
      rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hy
      exact abs_frame E.frame (eS (by decide)) hy.2.1
  obtain hyC : StreamRepr s.mem St ciph H iv a c₀ → Ctr s₁.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₁.mem Ctx) icb
      c₀.length := fun hy => by
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hicb] at hy
    rw [hc₁]
    exact ctr_frame E.frame (eS (by decide)) hy.2.2
  obtain htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (streamText_ok v L enc E.env rfl (C.data.of_eq E.rd E.wr) E.rbp hP hH₁ (E.alen.trans hA)
    htl E.dat E.len hyA hyC) fun s₂ ⟨he₂, rd₂, wr₂, f₂, hq⟩ => ?_)
  obtain hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.dw.ok.w (by decide) (by decide))
  obtain hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hy => ?_⟩
  rw [hicb]
  obtain hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide)))
    (by have := C.data.dw.ok.lt; omega_using [hn])
  obtain ⟨qa, qc, qo⟩ := hq hy
  simp only [hc₁, hd₁] at qa qc qo
  refine ⟨?_, by rw [hm]; exact qo⟩
  have hj := hy
  rw [Proof.Gcm.streamRepr_iff] at hj ⊢
  rw [ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, hicb, List.length_append, length_ctext, length_bytesAt]
  refine ⟨?_, qa, qc⟩
  rw [← hj.1]
  obtain e : St = St + BitVec.ofNat 64 0 := (BitVec.add_zero St).symm
  rw [blockAt_frame f₂ (j0_stFrame L C.data.dw.ok.st), e]
  exact blockAt_frame E.frame (eS (by decide))

/-- `vg_sm4_gcm_stream_encrypt`. -/
theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamEncryptX86_64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.streamEncryptX86_64.post s s' := by
  obtain run : ∀ {iv a p : List Byte}, s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = p.length →
      WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi)
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rsi) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
          let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          StreamRepr s'.mem (s.gpr .rsi) ciph h iv a c ∧
            bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = c.drop p.length) := fun {iv a p} hA hT =>
    WP.mono (streamText_run v true hp (iv := iv) (c₀ := gctr (ctxCiph s.mem (s.gpr .rdi)) (inc32 (Spec.Gcm.j0 (ctxH s.mem (s.gpr .rdi)) iv)) p) hA (by rw [hT, Proof.Gcm.length_gctr]))
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, ↓reduceIte, Proof.Gcm.length_gctr] at h₁ h₂
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rdx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .rcx).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rdx).toNat 0)
      (p := List.replicate (s.gpr .rcx).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a p hr hA hT => hq (iv, a, p) ⟨hA, hT⟩ hr⟩

/-- `vg_sm4_gcm_stream_decrypt`. -/
theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamDecryptX86_64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.streamDecryptX86_64.post s s' := by
  obtain run : ∀ {iv a c : List Byte}, s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = c.length →
      WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi)
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rsi) ciph h iv a c →
          let c' := c ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
          StreamRepr s'.mem (s.gpr .rsi) ciph h iv a c' ∧
            bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
              (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := fun {iv a c} hA hT =>
    WP.mono (streamText_run v false hp (iv := iv) (c₀ := c) hA hT)
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, Bool.false_eq_true, ↓reduceIte] at h₁
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rdx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .rcx).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rdx).toNat 0)
      (c := List.replicate (s.gpr .rcx).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => hq (iv, a, c) ⟨hA, hT⟩ hr⟩

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/StreamCryptCT.lean`): the branches are on the length
of the data and of the text so far, the same in both runs; the padding of
the additional data is AES-GCM's (`start_rel`); `crypt` and `absorb` are on
data at the same address, of the same length (`crypt_rel`, `absorb_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ tlenO streamLoad partWith absorb firstFlush restore)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env AbsIn rel_taint rel_wp rel_ite_e rel_reassoc2 rel_both rel_envT
  env_agree absRegs absorb_ok absorb_rel start_rel load_ok load_env toNat_mod16 test_ok fn_rel₂ fn_rel₂N ct_of_rel)

/-- Between `crypt` and `absorb`, in either order. -/
def PartM (Ctx St W SP : Addr) (P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  Env Ctx St W SP s 768 ∧ DataW4 Ctx St W SP s D n 768 ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀

/-- `PartM` with the registers `crypt` and `absorb` start from. -/
abbrev PartI (Ctx St W SP : Addr) (P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  PartM Ctx St W SP P₀ D n s ∧ s.gpr .r12 = D ∧ s.gpr .rbp = BitVec.ofNat 64 n ∧
    s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768) {P₀ : Nat} {D : Addr} {n : Nat}
include L

omit L in
theorem PartI.crIn {s : State} (h : PartI Ctx St W SP P₀ D n s) : CrIn Ctx St W SP 0 P₀ D n s 768 :=
  ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.1⟩

omit L in
theorem PartI.absIn {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    AbsIn Ctx St W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (List.replicate P₀ 0) D n s 768 :=
  ⟨h.1.1, h.2.1, h.2.2.1, by rw [List.length_replicate]; exact h.2.2.2, h.1.2.1.dw.ok, rfl⟩

omit L in
/-- The data reloaded. -/
theorem partM_load {s : State} (h : PartM Ctx St W SP P₀ D n s) :
    WP isa (.block streamLoad) s (PartI Ctx St W SP P₀ D n) := by
  obtain ⟨he, hd, hdat, hlen, htl⟩ := h
  obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok he hdat hlen htl
  rw [toNat_mod16] at hbx
  exact WP.of_runBlock ⟨s', run, ⟨he.keep (load_env hg) hrd hwr, hd.of_eq hrd hwr, hm ▸ hdat, hm ▸ hlen,
    hm ▸ htl⟩, h12, hbp, hbx⟩

/-- After `crypt`. -/
theorem partI_crypt {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    WP isa crypt s (PartM Ctx St W SP P₀ D n) := by
  have hd := h.1.2.1
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (crypt_ok L (icb := 0) h.crIn)) fun s' ⟨co, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hd h₁ (by omega_using [h₂]))
      (by decide)
  exact ⟨co.env, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2⟩

/-- After `absorb`. -/
theorem partI_absorb {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    WP isa (absorb v.callees 16) s (PartM Ctx St W SP P₀ D n) := by
  have hd := h.1.2.1
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (absorb_ok v L.lay (.inr rfl) h.absIn)) fun s' ⟨ao, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega_using [h₂]))
      (by decide)
  exact ⟨ao.env, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2⟩

/-- `partWith`, in one run. -/
theorem partI_part (enc : Bool) {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    WP isa (partWith enc crypt (absorb v.callees 16)) s (PartM Ctx St W SP P₀ D n) := by
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    exact WP.seq (WP.mono (partI_absorb v L h) fun _ h => WP.seq (WP.mono (partM_load h) fun _ h => partI_crypt L h))
  · simp only [partWith, ↓reduceIte]
    exact WP.seq (WP.mono (partI_crypt L h) fun _ h => WP.seq (WP.mono (partM_load h) fun _ h => partI_absorb v L h))

/-- `crypt` and `absorb` over the same data in both runs. -/
theorem part_rel (enc : Bool) :
    RelCT isa (fun s₁ s₂ => PartI Ctx St W SP P₀ D n s₁ ∧ PartI Ctx St W SP P₀ D n s₂)
      (partWith enc crypt (absorb v.callees 16)) fun _ _ => True := by
  have crR : RelCT isa (fun s₁ s₂ => PartI Ctx St W SP P₀ D n s₁ ∧ PartI Ctx St W SP P₀ D n s₂) crypt
      fun _ _ => True :=
    (crypt_rel L (icb₁ := 0) (icb₂ := 0) (P₁ := P₀) (P₂ := P₀) rfl).mono (fun _ _ h => ⟨h.1.crIn, h.2.crIn⟩)
      fun _ _ h => h
  have abR : RelCT isa (fun s₁ s₂ => PartI Ctx St W SP P₀ D n s₁ ∧ PartI Ctx St W SP P₀ D n s₂)
      (absorb v.callees 16) fun _ _ => True :=
    (RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => absorb_rel v L.lay (yo := 16) (.inr rfl) (H₁ := H₁)
      (H₂ := H₂) (x₁ := List.replicate P₀ 0) (x₂ := List.replicate P₀ 0) (D := D) (n := n) rfl).mono
      (fun _ _ h => ⟨_, _, h.1.absIn, h.2.absIn⟩) fun _ _ h => h
  have ld := rel_both (rel_envT (F := PartM Ctx St W SP P₀ D n) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => partM_load h) (fun _ h => partM_load h)
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    exact RelCT.seq (rel_both abR (fun _ h => partI_absorb v L h) (fun _ h => partI_absorb v L h)) (RelCT.seq ld crR)
  · simp only [partWith, ↓reduceIte]
    exact RelCT.seq (rel_both crR (fun _ h => partI_crypt L h) (fun _ h => partI_crypt L h)) (RelCT.seq ld abR)

end

/-- Before `streamText`: what the entry leaves, in each run. -/
structure TPre (Ctx St W SP : Addr) (aL P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s 768
  data : DataW4 Ctx St W SP s D n 768
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768) {aL P₀ : Nat} {D : Addr} {n : Nat}
include L

/-- The additional data padded if there is no text yet, in one run. -/
theorem tpre_start (hP : P₀ < 2 ^ 64) {s : State} (h : TPre Ctx St W SP aL P₀ D n s) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s (PartM Ctx St W SP P₀ D n) := by
  refine WP.mono (start_ok v L (Hyp := False) (a := List.replicate aL 0) (c₀ := List.replicate P₀ 0) h.env rfl
    (by rw [List.length_replicate]; exact hP) rfl (by rw [List.length_replicate]; exact h.alen)
    (by rw [List.length_replicate]; exact h.tlen) (fun f => f.elim)) fun s' ⟨he, hrd, hwr, f, _⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_tFrame L h₁ h₂) (by decide)
  exact ⟨he, h.data.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.dat,
    by rw [sl 208 (by decide) (by decide)]; exact h.len, by rw [sl 192 (by decide) (by decide)]; exact h.tlen⟩

/-- `streamText` in two runs, with the same data and lengths. -/
theorem streamText_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TPre Ctx St W SP aL P₀ D n s₁ ∧ TPre Ctx St W SP aL P₀ D n s₂)
      (streamText v.callees enc) fun s₁ s₂ => Env Ctx St W SP s₁ 768 ∧ Env Ctx St W SP s₂ 768 := by
  have hlt := fun {s} (h : TPre Ctx St W SP aL P₀ D n s) => h.data.dw.ok.lt
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre Ctx St W SP aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, TPre Ctx St W SP aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (hlt h)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁,
      by rw [hg₁]; exact h.rbp, hm₁ ▸ h.alen, hm₁ ▸ h.tlen, hm₁ ▸ h.dat, hm₁ ▸ h.len⟩, hz₁⟩
  have a := rel_both (rel_envT (F := TPre Ctx St W SP aL P₀ D n) [.rbp] (fun _ h => h.env)
    (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  simp only [streamText]
  refine RelCT.seq a (rel_ite_e (Q := fun s₁ s₂ => Env Ctx St W SP s₁ 768 ∧ Env Ctx St W SP s₂ 768)
    (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelCT.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hn0] at this
  -- The additional data padded, then the data.
  have st := rel_both ((start_rel v L.lay (aL := aL) (P := P₀) hP (F := TPre Ctx St W SP aL P₀ D n)
      fun s h => ⟨h.env, h.tlen, h.alen⟩).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (F₁ := fun s => T1 s) (F₂ := fun s => T1 s) (G₁ := PartM Ctx St W SP P₀ D n) (G₂ := PartM Ctx St W SP P₀ D n)
    (fun s h => tpre_start v L hP h.1) (fun s h => tpre_start v L hP h.1)
  have ld := rel_both (rel_envT (F := PartM Ctx St W SP P₀ D n) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => partM_load h) (fun _ h => partM_load h)
  have pt := rel_both (part_rel v L (P₀ := P₀) (D := D) (n := n) enc)
    (fun _ h => partI_part v L enc h) (fun _ h => partI_part v L enc h)
  exact (rel_reassoc2 (RelCT.seq st (RelCT.seq ld pt))).mono (fun _ _ h => ⟨h.1.1, h.1.2⟩)
    fun _ _ h => ⟨h.1.1, h.2.1⟩

end

/-- After the entry, what `streamText` needs. -/
theorem cryptEntry_tpre {s : State} (hp : Proof.Sm4Gcm.streamCryptPre s) :
    WP isa (.block cryptEntry) s (TPre (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) (s.gpr .rdx).toNat
      (s.gpr .rcx).toNat (s.gpr .r8) (s.gpr .r9).toNat) := by
  have C := CryptCtx.of hp
  refine WP.mono (cryptEntry_ok rfl rfl rfl rfl rfl rfl C.perm C.args) fun s₁ E => ?_
  exact ⟨E.env, C.data.of_eq E.rd E.wr, E.rbp, by rw [E.alen, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.tlen, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len⟩

theorem stream_pub {s₀ s₀' : State} (hq : Proof.Sm4Gcm.streamCryptPub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem stream_rel (v : GcmImpl) (enc : Bool) {s₀ s₀' : State}
    (hp : Proof.Sm4Gcm.streamCryptPre s₀) (hp' : Proof.Sm4Gcm.streamCryptPre s₀')
    (hq : Proof.Sm4Gcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block restore))) fun _ _ => True := by
  have L := (CryptCtx.of hp).lay
  have hE₂ := cryptEntry_tpre hp'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq'
  simp only [Proof.Sm4Gcm.arg] at q₈
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  have hE₁ := cryptEntry_tpre hp
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂N (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := stackArg s₀ 0) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 8) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₈
    (CryptCtx.of hp).args (CryptCtx.of hp').args ⟨_, by taint_decide⟩ hE₁ hE₂
    ((streamText_rel v L enc (s₀.gpr .rcx).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamEncryptX86_64.pre Proof.Sm4Gcm.streamEncryptX86_64.pub
      (streamEncrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v true hp hp' hq

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamDecryptX86_64.pre Proof.Sm4Gcm.streamDecryptX86_64.pub
      (streamDecrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v false hp hp' hq

end VG.Proof.Sm4Gcm.X86_64

end

end

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
  obtain pW : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  obtain pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .rdx hW pW
  obtain ⟨s₂, run₂, h15, h13, hdi, hsi, hsp₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rdi = K ∧ s₂.gpr .rsi = Ctx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hg₁, hW, hCtx, hK, hSP]
  refine WP.seq ?_
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  obtain rd₂ : s₂.rd = s.rd := hrd₂.trans hrd₁
  obtain wr₂ : s₂.wr = s.wr := hwr₂.trans hwr₁
  obtain kc : KeyCall s₂ K Ctx := by
    refine ⟨hdi, hsi, by rw [hsp₂]; exact hsp, wk, by omega_arith, d_kc.sub_right (Region.sub_prefix (by decide)),
      by rw [hsp₂]; exact k_k, by rw [hsp₂]; exact k_c.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂, hrd]
      exact covers_cons (covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _)))
        (covers_left (covers_prefix pC (by decide)))
    · rw [wr₂]; exact covers_prefix pC (by decide)
  refine WP.seq (WP.mono (key_call kc) fun s₃ g => ?_)
  obtain g15 : s₃.gpr .r15 = W := by rw [g.saved .r15 (by decide), h15]
  obtain g13 : s₃.gpr .r13 = Ctx := by rw [g.saved .r13 (by decide), h13]
  obtain gsp : s₃.gpr .rsp = SP := by rw [g.saved .rsp (by decide), hsp₂]
  obtain rd₃ : s₃.rd = s.rd := g.rd.trans rd₂
  obtain wr₃ : s₃.wr = s.wr := g.wr.trans wr₂
  obtain w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  obtain w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  obtain w₃ := in_off pW (show 96 + 8 ≤ 2560 by decide) (by decide)
  obtain w₄ := in_off pW (show 104 + 8 ≤ 2560 by decide) (by decide)
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
  obtain g4sp : s₄.gpr .rsp = SP := by rw [hg₄ .rsp (by decide), gsp]
  obtain rd₄ : s₄.rd = s.rd := hrd₄.trans rd₃
  obtain wr₄ : s₄.wr = s.wr := hwr₄.trans wr₃
  -- The disjointness of the parts.
  obtain dCW : ∀ d n, d + n ≤ 256 → ∀ e k, e + k ≤ 2560 →
      (⟨Ctx + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ := fun d n hd e k he =>
    (d_cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)
  obtain dK0 : (⟨Ctx, 128⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16⟩ :=
    Offset.base_disjoint Ctx (by decide) (by omega_arith)
  obtain f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((Cmac.frame_store2 _ _ _).mono (by simp)).trans ((Cmac.frame_store2 _ _ _).mono (by simp))
  obtain hT₄ : blockAt s₄.mem (W + BitVec.ofNat 64 96) = 0 := by
    rw [blockAt, hm₄, zeroT_bytes]; decide
  obtain hD₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
    rw [blockAt, hm₄, bytesAt_frame (Cmac.frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCW 240 16 (by decide) 96 16 (by decide)) (by decide),
      zeroT_bytes]
    decide
  obtain hk₄ : Spec.Sm4.scheduleAt s₄.mem Ctx = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem K) := by
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
  obtain pC' : Covers [⟨Ctx, 256⟩] s₄.wr := by rw [wr₄]; exact pC
  obtain pW' : Covers [⟨W, 2560⟩] s₄.wr := by rw [wr₄]; exact pW
  obtain cc : CtrCall s₄ Ctx (W + BitVec.ofNat 64 96) (Ctx + BitVec.ofNat 64 240) 1 := by
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
  obtain c15 : s₅.gpr .r15 = W := by rw [c.saved .r15 (by decide), hg₄ .r15 (by decide), g15]
  obtain c5sp : s₅.gpr .rsp = SP := by rw [c.saved .rsp (by decide), g4sp]
  have cfr := c.frame
  rw [g4sp] at cfr
  have gfr := g.frame
  rw [hsp₂] at gfr
  -- The saved registers and the return address.
  obtain dSv : ∀ r ∈ [(⟨Ctx, 128⟩ : Region), below SP stkN], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide)) |>.symm
    · exact (k_s.sub_right (Offset.sub_base _ (by decide))).symm
  obtain dSv₄ : ∀ r ∈ [(⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region), ⟨W + BitVec.ofNat 64 96, 16⟩], (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  obtain dSv₅ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩, below SP stkN],
      (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
    · exact (dCW 240 16 (by decide) 128 48 (by decide)).symm
    · exact (k_s.sub_right (Offset.sub_base _ (by decide))).symm
  obtain hsv₅ : SavedAt s₅.mem W s :=
    (((hsv₁.frame (by rw [← hm₂]; exact gfr) dSv).frame f₄ dSv₄).frame cfr dSv₅)
  obtain hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
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
  obtain hrc : Covers [⟨W, 2560⟩] (s₅.rd ++ s₅.wr) := by rw [c.rd, c.wr, rd₄, wr₄]; exact covers_left pW
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
bytes that a call of `vg_sm4_ctr32` takes. The working space is 2560 bytes for
`init`, `seal` and `open`, and the 768 the streaming functions use for them
(`vg_ghash`'s 256 at 512 the last). `init` and `stream_finish`, whose
working space is their last argument in a register, have a frame of it and
8 more bytes to keep `rsp` aligned (`Verified.stackScratch`): 2568 and 776.
The working space of the others is their last argument, passed on the stack
after the six argument registers and their other stack arguments: their
frames (`Verified.stackArgScratch`) also hold a copy of those, 784 bytes for
`stream_encrypt`, `stream_decrypt` and `stream_verify` (none), 2592 for
`seal` (two) and 2600 for `open` (three,
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
  X86_64.Verified.stackScratch (hpostOut := Proof.Sm4Gcm.initPostOut_local _) (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
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
  X86_64.Verified.stackArgScratch (hpostOut := Proof.Sm4Gcm.streamEncryptPostOut_local _) (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
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
  X86_64.Verified.stackArgScratch (hpostOut := Proof.Sm4Gcm.streamDecryptPostOut_local _) (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
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
  X86_64.Verified.stackScratch (hpostOut := Proof.Sm4Gcm.streamFinishPostOut_local _) (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
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
  X86_64.Verified.stackArgScratch (hpostOut := Proof.Sm4Gcm.streamVerifyPostOut_local _) (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
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
  X86_64.Verified.stackArgScratch (hpostOut := Proof.Sm4Gcm.sealPostOut_local _) (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
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
  X86_64.Verified.stackArgScratch (hpostOut := Proof.Sm4Gcm.openPostOut_local _) (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
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
      obtain ha := Proof.AesGcm.agree_of hb.2
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
  scrubAllOf {
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rdx init
    stack := 5792
    verified := init_framed
    spSafe := X86_64.withStackScratch_spSafe_of init_spSafe } .sse false [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (initOut _)
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

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
