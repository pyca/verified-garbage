module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.Straight

/-!
# AES-GCM on whole blocks, x86-64: loops that take all the blocks

Untrusted: everything here is checked by Lean. With a `piece` that also
takes the blocks after the last 16 (`full`), `Blocks.fullBody` gives at least
16 blocks all to it, after which nothing is left (`fullBody_ok`), and fewer
to `rest` and the calls, as without `full`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BP M s)
include hp

omit hp in
/-- `r11` at the working space. -/
theorem scratch_ok (s₁ : State) :
    WP isa (.block (Blocks.scratchSetup aligned)) s₁ fun s₃ =>
      s₃.gpr .r11 = AlignedScratch.ptr aligned (s₁.gpr .r11) ∧ (∀ r, r ≠ .r11 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  cases aligned <;> apply WP.of_runBlock
  all_goals refine ⟨_, by xrun [Blocks.scratchSetup], ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro r a; simp [gpr_setReg, gpr_arithFlags, a])
    | simp [AlignedScratch.ptr, gpr_setReg, gpr_arithFlags, mem_arithFlags, mem_setReg,
        rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- With `full`: at least 16 blocks all by `piece` (or, if `small`, at least
`smallMin small4` by `pieceS.getD piece`), which leaves `Done` (`hpost`),
or fewer by `rest` and the calls (`hsmall`). -/
theorem fullBody_ok {small small4 : Bool} {piece first second : Prog isa} {pieceS : Option (Prog isa)}
    {Post : State → State → Prop} {Done : State → Prop}
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ → WP isa piece s₃ (Post s₃))
    (hpieceS : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ (if small then 1 else 16) →
      WP isa (pieceS.getD piece) s₃ (Post s₃))
    (hpost : ∀ s₃ s₄, s₃.gpr .r9 = BitVec.ofNat 64 (n s) → (∀ r ∈ argRegs, s₃.gpr r = s.gpr r) →
      (∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r) →
      s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) → s₃.rd = s.rd →
      s₃.wr = s.wr → Kept s 0 s₃.mem → Frame [kR' s] s.mem s₃.mem → Post s₃ s₄ → Done s₄)
    (hsmall : n s < 16 → ∀ st, Mid s 0 0 [] st → WP isa (.seq (.block rest) (tail first second)) st Done)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem)
    (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (fullBody piece first second aligned small small4 pieceS) s₁ Done := by
  have hmin : 1 ≤ smallMin small4 := by cases small4 <;> decide
  -- The piece, from a state with `s₁`'s registers and memory.
  have pc : ∀ (p : Prog isa) (lo : Nat), (∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ lo → WP isa p s₃ (Post s₃)) →
      lo ≤ n s → ∀ s₂ : State, s₂.gpr = s₁.gpr → s₂.mem = s₁.mem →
      s₂.rd = s₁.rd → s₂.wr = s₁.wr → WP isa (stitchPart p aligned true) s₂ Done := by
    intro p lo hpiece hlo s₂ g₂ m₂ rd₂ wr₂
    refine WP.seq (WP.mono (scratch_ok (aligned := aligned) s₂) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
    have keepR : ∀ r, r ≠ .r11 → s₄.gpr r = s.gpr r := fun r c => by rw [g₄ r c, g₂, hg r c]
    have ga : ∀ r ∈ argRegs, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide)
    have gc : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide)
    have g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₄, g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    have h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
      rw [keepR _ (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm
    have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₂, hrd]
    have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₂, hwr]
    have hk₄ : Kept s 0 s₄.mem := by rw [m₄, m₂]; exact hk
    have hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄, m₂]; exact hf
    exact WP.mono (hpiece s₄ (spreM_of hp hlo (Nat.le_refl _) h9 ga g11 rd₄' wr₄' hf₄)) fun s₅ hP =>
      hpost s₄ s₅ h9 ga gc g11 rd₄' wr₄' hk₄ hf₄ hP
  -- The calls, from a state with `s₁`'s registers and memory.
  have cl : n s < 16 → ∀ s₂ : State, s₂.gpr = s₁.gpr → s₂.mem = s₁.mem → s₂.rd = s₁.rd → s₂.wr = s₁.wr →
      WP isa (.seq (.block rest) (tail first second)) s₂ Done := fun hlt s₂ g₂ m₂ rd₂ wr₂ =>
    hsmall hlt _ (mid_entry hp (fun r hr => by rw [g₂]; exact hg r hr) (by rw [m₂]; exact hk)
      (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have hlt : n s < 16 := by simpa using h
    cases small with
    | false => exact cl hlt s₂ g₂ m₂ rd₂ wr₂
    | true =>
      refine WP.seq (WP.mono (cmpMin_ok (s := s) small4 (by rw [g₂]; exact hg _ (by decide)))
        fun s₃ ⟨g₃, m₃, rd₃, wr₃, cf₃⟩ => ?_)
      refine WP.ite (decide (n s < smallMin small4)) (by simp only [eval, cf₃]) (fun h0 => ?_) (fun h0 => ?_)
      · exact cl hlt s₃ (g₃.trans g₂) (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂)
      · exact pc _ _ hpieceS (by simp at h0 ⊢; omega) s₃ (g₃.trans g₂) (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂)
  · exact pc _ _ hpiece (by simp at h; omega) s₂ g₂ m₂ rd₂ wr₂

/-- After a loop that encrypts all the blocks: the blocks hashed are those
written. -/
theorem stitchEFull_ok {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s)) (ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r)
    (gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (g11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s))) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (hk₃ : Kept s 0 s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (hP : Gcm.X86_64.Stitch.EPost s₃ s₄) :
    Mid s (n s) 0 (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s))) s₄ := by
  refine mid_of_post hp (Nat.le_refl _) h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
    fun eH eY _ eD => ?_
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hy := hP.y
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
    ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
    toNat_ofNat_of_lt hn] at hy
  rw [hy, eH, eY, eD]

/-- After a loop that decrypts all the blocks: those hashed are those read. -/
theorem stitchDFull_ok {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s)) (ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r)
    (gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (g11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s))) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (hk₃ : Kept s 0 s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (hP : Gcm.X86_64.Stitch.DPost s₃ s₄) :
    Mid s (n s) 0 (blocksAt s.mem (D s) (n s)) s₄ := by
  refine mid_of_post hp (Nat.le_refl _) h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
    fun eH eY eD _ => ?_
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hy := hP.y
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
    ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
    toNat_ofNat_of_lt hn] at hy
  rw [hy, eH, eY, eD]

end

end VG.Proof.AesGcm.X86_64.Blocks
