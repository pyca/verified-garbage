module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SM4-GCM on x86-64: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `rbx` and `rbp` bytes (AES-GCM's `lens`), copies the accumulator `S`
to `W + o` and XORs `CIPH_K(J₀)` into it with `vg_sm4_ctr32`, from the
counter block `J₀` at the state (`tag_ok`), as AES-GCM's
(`Proof/AesGcm/X86_64/Tag.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr lens)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env tFrame lens_ok blockAt_frame blocksAt_one ctr32_single
  bytesAt_copy2 covers_left covers_cons add_ofNat_assoc)

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W SP : Addr) (o : Nat) : List Region :=
  [⟨St, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP stkN]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (Ctx St W SP : Addr) (o : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  out : bytesAt s.mem (W + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ Ctx J)
  frame : Frame (tagFrame St W SP o) m₀ s.mem
  /-- The call of `vg_sm4_ctr32` left the next counter block, the first one of
  the data, at `St`. -/
  j : blockAt s.mem St = Spec.Gcm.inc32 J

/-- `tag o` before the call of `vg_sm4_ctr32`, from `m₀`: its arguments, and
the accumulator with the lengths block at `W + o`. -/
structure TagMid (Ctx St W SP : Addr) (o : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  call : CtrCall s Ctx St (W + BitVec.ofNat 64 o) 1
  ciph : ciphOf s.mem Ctx = ciphOf m₀ Ctx
  j : blockAt s.mem St = J
  y : blockAt s.mem (W + BitVec.ofNat 64 o) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  frame : Frame (tagFrame St W SP o) m₀ s.mem

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

/-- `tag o` up to the call of `vg_sm4_ctr32`. -/
theorem tagMid_ok {o : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem St = J) :
    WP isa (.seq (lens v.callees 16) (.block (([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax,
        .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.reg .r14)] : List Instr) ++ ptr .rdx .r15 o ++ ([.mov32 .rcx (imm 1)] : List Instr)))) s
      (TagMid Ctx St W SP o H (blockAt s.mem (St + BitVec.ofNat 64 16)) J
        (s.gpr .rbx).toNat (s.gpr .rbp).toNat s.mem) := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have La := L.lay
  refine WP.seq (WP.mono (lens_ok v La (yo := 16) (.inr rfl) he hH) fun s₁ ⟨he₁, hH₁, hY₁, f₁⟩ => ?_)
  have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
  have dJ : ∀ r ∈ tFrame St W SP 16, (⟨St, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using La.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using La.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using La.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (La.stk_st (a := 0) (n := 16) (by decide)).symm
  have hJ₁ : blockAt s₁.mem St = J := by rw [blockAt_frame f₁ dJ, hJ]
  have hc₁ : ciphOf s₁.mem Ctx = ciphOf s.mem Ctx := ciph_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact La.cs.sub_right (Lay.stSub (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact La.cw'.sub_right (Lay.wSub (by decide))
    · exact La.kc.symm)
  have r₁ := he₁.perm.stR (show 16 + 8 ≤ 80 by decide)
  have r₂ := he₁.perm.stR (show 24 + 8 ≤ 80 by decide)
  have w₁ := he₁.perm.wW (show o + 8 ≤ 2560 by omega)
  have w₂ := he₁.perm.wW (show o + 8 + 8 ≤ 2560 by omega)
  have dsep : (⟨W + BitVec.ofNat 64 o, 8⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8, 8⟩ := by
    rw [add_ofNat_assoc]
    exact (La.st_w (a := 24) (n := 8) (by decide) (by omega)).symm
  obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)),
        .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13), .mov .rsi (.reg .r14)] ++ ptr .rdx .r15 o ++
        [.mov32 .rcx (imm 1)]) s₁ = some s₂ ∧
      s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 o) (s₁.mem.readW (St + BitVec.ofNat 64 16) 64)).writeW
        (W + BitVec.ofNat 64 o + BitVec.ofNat 64 8)
        ((s₁.mem.writeW (W + BitVec.ofNat 64 o) (s₁.mem.readW (St + BitVec.ofNat 64 16) 64)).readW
          (St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) 64) ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = St ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 o ∧
      s₂.gpr .rcx = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have e24 : St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 = St + BitVec.ofNat 64 24 := add_ofNat_assoc ..
    have eo : W + BitVec.ofNat 64 o + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (o + 8) := add_ofNat_assoc ..
    rw [e24, eo]
    refine ⟨_, by xrun [h13, h14, h15, r₁, r₂, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  have f₂ : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s₁.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (W + BitVec.ofNat 64 o) 16 = bytesAt s₁.mem (St + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, bytesAt_copy2 _ dsep]
  have dJo : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩ := by
    simpa using La.st_w (a := 0) (n := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem St = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, hJ₁]
  have hc₂ : ciphOf s₂.mem Ctx = ciphOf s.mem Ctx := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact La.cw'.sub_right (Lay.wSub (by omega))), hc₁]
  have hcall : CtrCall s₂ Ctx St (W + BitVec.ofNat 64 o) 1 := by
    refine ⟨hdi, hsi, hdx, hcx, by rw [hk]; exact L.sp, by have := La.cw; omega, by have := La.sw; omega,
      by have := La.ww; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
      by simpa using (La.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide)),
      (La.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega)),
      dJo, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
    · rw [hk]; simpa using L.ks.sub_right (Lay.stSub (d := 0) (n := 16) (by decide))
    · rw [hk]; exact L.kw.sub_right (Lay.wSub (by omega))
    · refine covers_cons ?_ (covers_cons ?_ (covers_left (he₂.perm.wC (by omega))))
      · exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · simpa using covers_left (he₂.perm.stC (d := 0) (n := 16) (by decide))
    · exact covers_cons (by simpa using he₂.perm.stC (d := 0) (n := 16) (by decide)) (he₂.perm.wC (by omega))
  refine ⟨he₂, hcall, hc₂, hJ₂, ?_, ?_⟩
  · rw [blockAt, hT, ← blockAt, hY₁]
  · have fA : Frame (tagFrame St W SP o) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, below_stk _ (by have := stkN_eq; omega)⟩
    exact fA.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem St = J) :
    WP isa (tag v.callees o) s (TagOut Ctx St W SP o H (blockAt s.mem (St + BitVec.ofNat 64 16)) J
      (s.gpr .rbx).toNat (s.gpr .rbp).toNat s.mem) := by
  refine WP.assoc (WP.seq (WP.mono (tagMid_ok v L ho he hH hJ) fun s₂ M => ?_))
  have hk := M.env.rsp
  refine WP.mono (ctr_call M.call) fun s₃ g => ?_
  have gout := g.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  refine ⟨M.env.of_saved g.saved g.rd g.wr, ?_, ?_, by rw [g.ctr, M.j]; rfl⟩
  · rw [Cmac.bytesAt_blockAt, gout.1, M.j,
      show Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s₂.mem Ctx) = ciphOf s₂.mem Ctx from rfl, M.ciph, M.y]
  · refine M.frame.trans (g.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Region.sub_prefix (base := St) (show 16 ≤ 32 by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Sm4Gcm.X86_64
