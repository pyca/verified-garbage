module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixI
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM `seal_split` on x86-64: `prefix` with the block index pushed

Untrusted: everything here is checked by Lean. `Fast.prefixI` puts the index
of the first counter block (2, for a 12-byte nonce) into `rax` and pushes it,
then runs `prefix` a word lower, calling the encryption function given the
block index (`prefix_okI`), and pops it: it leaves what `prefix` does, with
the 64 bytes below `SP` (the pushed word and the 56 below it) in place of the
56 (`prefixI_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 ctrIndex)

/-- The stack below `SP - 8`, in the 64 bytes below `SP`. -/
theorem below8_sub64 {SP : Addr} {k : Nat} (hk : k + 8 ≤ 64) :
    Region.Sub (below (SP - BitVec.ofNat 64 8) k) (below SP 64) :=
  fun a h => below_sub (by omega) (by decide) a (below_below SP 8 k a h)

/-- The four stack arguments of the call, right below `SP - 8`'s word and it,
in the 64 bytes below `SP`. -/
theorem args_sub64 (SP : Addr) :
    Region.Sub ⟨SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 24, 32⟩ (below SP 64) := by
  have e : SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 24 = SP - BitVec.ofNat 64 32 := by
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  rw [e]; exact below_sub (by decide) (by decide)

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP M Ctx W SP D S R n sl s)
  (kw : (below SP 64).Disjoint ⟨W, 2560⟩) (kd : (below SP 64).Disjoint ⟨D, n⟩)
  (ks : (below SP 64).Disjoint ⟨S, sl⟩) (kM : (below SP 64).Disjoint ⟨Ctx, M.len⟩) (sp : 64 ≤ SP.toNat)
include h kw kd ks kM sp

/-- The state after the index is put into `rax` (`s₁`, from `s`) and pushed:
what `prefix` needs a word lower, with the index at `SP - 8`. -/
theorem pushedPI (hcb : ctrIndex (blockAt s.mem (cbA W)) = 2) {s₁ : State} (ax₁ : s₁.gpr .rax = BitVec.ofNat 64 2)
    (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd) (wr₁ : s₁.wr = s.wr) :
    PP M Ctx W (SP - BitVec.ofNat 64 8) D S R n sl (pushed [.rax] s₁) ∧
      IdxI Ctx W (SP - BitVec.ofNat 64 8) D n (pushed [.rax] s₁) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have X := h.ext
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := h.env.keep (fun r hr => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₁ wr₁
  have hn8 : 8 * [Reg.rax].length ≤ (s₁.gpr .rsp).toNat := by rw [he₁.rsp]; simp; omega
  obtain ⟨f₀, -⟩ := push_frame he₁ (by omega)
  obtain ⟨-, hpj⟩ := pushRegs_mem s₁ [.rax] (by decide) hn8
  have b8 : Region.Sub (below SP 8) (below SP 64) := below_sub (by decide) (by decide)
  have one : ∀ {r : Region}, (below SP 64).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  have rW : ∀ d, d + 8 ≤ 2560 →
      (pushed [.rax] s₁).mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => by
      rw [f₀.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (one (kw.sub_right (Lay.wSub hd))) (by decide), m₁]
  have cbW : Region.Sub ⟨cbA W, 16⟩ ⟨W, 2560⟩ := by
    simp only [cbA]; rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have bW : ∀ {p : Addr}, Region.Sub ⟨p, 16⟩ ⟨W, 2560⟩ → blockAt (pushed [.rax] s₁).mem p = blockAt s.mem p :=
    fun hs => by rw [blockAt_frame f₀ (one (kw.sub_right hs)), m₁]
  have kc : (below SP 64).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix M.ge)
  have hd₁ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₁ D n := h.data.of_eq rd₁ wr₁
  have k56 : ∀ {r : Region}, (below SP 64).Disjoint r → (below (SP - BitVec.ofNat 64 8) 56).Disjoint r :=
    fun hd => hd.sub_left (below8_sub64 (by decide))
  -- `prefix`'s state, a word lower.
  have P' : PP M Ctx W (SP - BitVec.ofNat 64 8) D S R n sl (pushed [.rax] s₁) :=
    ⟨env_pushed he₁, lay_pushed L (kc.sub_left (below_sub (by decide) (by decide))) (kw.sub_left (below_sub (by decide) (by decide))),
      ⟨by rw [rW 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩,
      by rw [rW 200 (by decide)]; exact h.dat, by rw [rW 208 (by decide)]; exact h.len,
      by rw [rW 224 (by decide)]; exact h.src, by rw [rW 192 (by decide)]; exact h.slen,
      ⟨⟨by rw [pushed_rd, pushed_wr]; exact covers_ins hd₁.ok.rd, hd₁.ok.lt, hd₁.ok.wrap, hd₁.ok.st, hd₁.ok.w,
        kd.sub_left (below8_sub64 (by decide))⟩, by rw [pushed_wr]; exact covers_tail hd₁.wr, hd₁.ctx⟩,
      by rw [pushed_rd, pushed_wr, rd₁, wr₁]; exact covers_ins h.srcCov,
      h.sW, h.sD, h.sWrap, hsl, k56 kw, k56 kd, k56 ks, k56 kM, by rw [toNat_sub_ofNat (by omega)]; omega,
      ⟨X.w, X.cs, X.cw, X.cd, kM.sub_left (below8_sub64 (by decide)),
        by rw [pushed_rd, pushed_wr, rd₁, wr₁]; exact covers_ins X.cov,
        M.frame f₀ (one kM) X.w (by rw [m₁]; exact X.ok)⟩⟩
  have I' : IdxI Ctx W (SP - BitVec.ofNat 64 8) D n (pushed [.rax] s₁) := by
    refine ⟨by rw [bW cbW]; exact hcb, ?_, ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..),
        by rw [he₁.rsp]; exact Region.contains_self _ _⟩,
      kw.sub_left (args_sub64 SP), kd.sub_left (args_sub64 SP), by rw [toNat_sub_ofNat (by omega)]; omega⟩
    have := hpj 0 (by decide)
    rw [he₁.rsp] at this
    have e : (pushed [.rax] s₁).mem.readW (SP - BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 2 := by
      rw [← ax₁]; exact this
    rw [e]; rfl
  exact ⟨P', I'⟩

/-- `prefixI`: `prefix` calling `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`
(`T`), a word lower, with the block index of the counter block, 2, pushed. -/
theorem prefixI_ok (T : BlkToFnI M) (hcb : ctrIndex (blockAt s.mem (cbA W)) = 2) :
    WP isa (Impl.AesGcm.X86_64.Fast.prefixI T.fn) s (PPost Ctx W SP D S R n sl 64 s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  unfold Impl.AesGcm.X86_64.Fast.prefixI
  obtain ⟨s₁, run₁, ax₁, g₁, m₁, rd₁, wr₁⟩ := movIdx_ok s
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain ⟨P', I'⟩ := pushedPI h kw kd ks kM sp hcb ax₁ g₁ m₁ rd₁ wr₁
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := h.env.keep (fun r hr => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₁ wr₁
  have hn8 : 8 * [Reg.rax].length ≤ (s₁.gpr .rsp).toNat := by rw [he₁.rsp]; simp; omega
  obtain ⟨f₀, hP⟩ := push_frame he₁ (by omega)
  have b8 : Region.Sub (below SP 8) (below SP 64) := below_sub (by decide) (by decide)
  have one : ∀ {r : Region}, (below SP 64).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  have cbW : Region.Sub ⟨cbA W, 16⟩ ⟨W, 2560⟩ := by
    simp only [cbA]; rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have yW : Region.Sub ⟨yA W, 16⟩ ⟨W, 2560⟩ := by
    simp only [yA]; rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have bW : ∀ {p : Addr}, Region.Sub ⟨p, 16⟩ ⟨W, 2560⟩ → blockAt (pushed [.rax] s₁).mem p = blockAt s.mem p :=
    fun hs => by rw [blockAt_frame f₀ (one (kw.sub_right hs)), m₁]
  have kc : (below SP 64).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix M.ge)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (prefix_okI P' I' T) fun u Q => ?_)
  have hR' := h.rounds.2
  have sQ : Region.Sub ⟨S, 16 * (sl / 16)⟩ ⟨S, sl⟩ := Region.sub_prefix (by omega)
  have sS : Region.Sub ⟨S + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ ⟨S, sl⟩ := Offset.sub_base S (by omega)
  have eC : ctxCiph (pushed [.rax] s₁).mem Ctx R = ctxCiph s.mem Ctx R := by
    have := ciph_frame f₀ (one kc) hR'
    rw [m₁] at this; exact this
  have eH : ctxH (pushed [.rax] s₁).mem Ctx = ctxH s.mem Ctx := by
    rw [ctxH_eq, ctxH_eq, blockAt_frame f₀ (one (kc.sub_right (Offset.sub_base (d := 240) _ (by decide)))), m₁]
  have eS : blocksAt (pushed [.rax] s₁).mem S (sl / 16) = blocksAt s.mem S (sl / 16) := by
    rw [blocksAt_frame f₀ (one (ks.sub_right sQ)) (by omega), m₁]
  have eT : bytesAt (pushed [.rax] s₁).mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) := by
    rw [bytesAt_frame f₀ (one (ks.sub_right sS)) (by omega), m₁]
  have prd : (popped .r10 1 u).rd = s.rd := by rw [popped_rd, Q.rd, pushed_rd, rd₁]
  have pwr : (popped .r10 1 u).wr = s.wr := by rw [popped_wr, Q.wr, pushed_wr, wr₁]; rfl
  refine ⟨Q.env.rsp.trans hP.symm, Q.wr, ⟨⟨?_, ?_, ?_, ?_, h.env.perm.of_eq prd pwr⟩, prd, pwr, ?_, ?_, ?_, ?_, ?_,
    by rw [popped_mem]; exact Q.dat, by rw [popped_mem]; exact Q.len, by rw [popped_mem]; exact Q.aux⟩⟩
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact Q.env.r13
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact Q.env.r14
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact Q.env.r15
  · rw [popped_rsp, Q.env.rsp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, ← m₁]
    refine (f₀.sub fun r hr => ?_).trans (Q.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below SP 64, by simp, b8⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl
      iterate 6 refine ⟨_, by simp, fun _ h => h⟩
      exact ⟨below SP 64, by simp, below8_sub64 (by decide)⟩
  · rw [popped_mem, Q.blocks, eC, bW cbW, eS]
  · rw [popped_mem, Q.ctr, bW cbW]
  · rw [popped_mem, Q.y, eH, bW yW]
  · rw [popped_mem, Q.tail, eT]

end

end VG.Proof.AesGcm.X86_64.Split
