module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Fn
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.R10
public import VerifiedGarbage.Proof.AesGcm.X86_64.AlignedScratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on whole blocks out of place, x86-64: given the block index

Untrusted: everything here is checked by Lean. As `Blocks/Iv96.lean`, out
of place: the block index at `rsp + 32` (`IdxArg`), for a loop that takes all
the blocks (`EncCodeI`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt)

/-- The block index at `rsp + off`: the low word of the counter block,
readable, and apart from the output and `scratch`. -/
structure IdxArg (off : Nat) (s : State) : Prop where
  eq : s.mem.readW (SP s + BitVec.ofNat 64 off) 32 = (blockAt s.mem (C s)).extractLsb' 0 32
  rd : InRegions s.rd (SP s + BitVec.ofNat 64 off) 4
  d : Region.Disjoint ⟨SP s + BitVec.ofNat 64 off, 4⟩ (dR s)
  s : Region.Disjoint ⟨SP s + BitVec.ofNat 64 off, 4⟩ (sR s)

/-- An out-of-place encryption loop taking all the blocks, given the block
index at `rsp + 32`. -/
structure EncCodeI (M : CtxMode) where
  enc : Prog isa
  ok : ∀ s₀, Gcm.X86_64.Stitch.SPreTo M s₀ →
    Gcm.X86_64.StitchZ.IdxOk 32 [Gcm.X86_64.Stitch.oR s₀, Gcm.X86_64.Stitch.pR s₀] s₀ →
    WP isa enc s₀ (Gcm.X86_64.Stitch.EPostTo s₀)
  /-- Constant time, from the arguments in their registers (the output in
  `r10`) and the same index at `rsp + 32` in both runs. -/
  ct : RelCT isa (fun s₁ s₂ => (∀ r ∈ ([.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] : List Reg),
      s₁.gpr r = s₂.gpr r) ∧ Gcm.X86_64.Stitch.SPreTo M s₁ ∧ Gcm.X86_64.Stitch.SPreTo M s₂ ∧
    Gcm.X86_64.StitchZ.IdxOk 32 [Gcm.X86_64.Stitch.oR s₁, Gcm.X86_64.Stitch.pR s₁] s₁ ∧
    Gcm.X86_64.StitchZ.IdxOk 32 [Gcm.X86_64.Stitch.oR s₂, Gcm.X86_64.Stitch.pR s₂] s₂ ∧
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 32 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 32)
    enc fun _ _ => True

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- `IdxArg` at the entry gives `IdxOk` where the loop starts. -/
theorem idxOk_of {aligned : Bool} {off : Nat} (hx : IdxArg off s) {s₃ : State}
    (ga : ∀ r ∈ BlocksTo.argRegs, s₃.gpr r = s.gpr r) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s))
    (h10 : s₃.gpr .r10 = Dst s)
    (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)))
    (hf : Frame [kR' s] s.mem s₃.mem) (hrd : s₃.rd = s.rd) :
    Gcm.X86_64.StitchZ.IdxOk off [Gcm.X86_64.Stitch.oR s₃, Gcm.X86_64.Stitch.pR s₃] s₃ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hb := AlignedScratch.offset_bounds aligned (S s)
  have ek : s₃.gpr .rdx = C s := ga _ (by simp [BlocksTo.argRegs])
  have hsp : s₃.gpr .rsp = s.gpr .rsp := ga _ (by simp [BlocksTo.argRegs])
  have hq : (s₃.gpr .r9).toNat = n s := by rw [h9, toNat_ofNat_of_lt hn]
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp only [Gcm.X86_64.Stitch.cb, Gcm.X86_64.Stitch.cp, ek, hsp]
    rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hx.s.sub_right kR'_sub)
        (show 32 / 8 < 2 ^ 64 by decide),
      VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_s.sub_right kR'_sub)]
    exact hx.eq
  · rw [hrd, hsp]
    obtain ⟨r, hr, hc⟩ := hx.rd
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Gcm.X86_64.Stitch.oR, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.nb, h10, hq, hsp]
      exact hx.d.sub_right (Region.sub_prefix (by omega))
    · simp only [Gcm.X86_64.Stitch.pR, Gcm.X86_64.Stitch.pp, h11, hsp]
      exact hx.s.sub_right (Offset.sub_base _ (by omega))

/-- Taking all the blocks and `r11` at the working space, with at least 16
blocks: what the loop needs, and the index kept. -/
theorem takeScratchI_ok {aligned : Bool} {off : Nat} (hx : IdxArg off s) (h16 : 16 ≤ n s) {s₂ : State}
    (h11 : s₂.gpr .r11 = S s) (h10 : s₂.gpr .r10 = Dst s) (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₂.gpr r = s.gpr r)
    (hk : Kept s 0 s₂.mem) (hf : Frame [kR' s] s.mem s₂.mem) (hrd : s₂.rd = s.rd) (hwr : s₂.wr = s.wr) :
    WP isa (.block (takeAllTo ++ Blocks.scratchSetup aligned)) s₂ fun s₄ => Gcm.X86_64.Stitch.SPreTo M s₄ ∧
      Gcm.X86_64.StitchZ.IdxOk off [Gcm.X86_64.Stitch.oR s₄, Gcm.X86_64.Stitch.pR s₄] s₄ ∧
      s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 off) 32 = s.mem.readW (SP s + BitVec.ofNat 64 off) 32 := by
  rw [WP.block_append_iff]
  refine WP.mono (takeAllTo_ok hp h11 (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) h10 hk hf hwr)
    fun s₃ ⟨_, f₃, g₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (Blocks.scratch_ok (aligned := aligned) s₃) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  have keepR : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [g₄ r c, g₃ r a, hg r c b]
  have ga : ∀ r ∈ BlocksTo.argRegs, s₄.gpr r = s.gpr r := fun r hr => by
    simp only [BlocksTo.argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide)
  have h10₄ : s₄.gpr .r10 = Dst s := by rw [g₄ _ (by decide), g₃ _ (by decide), h10]
  have g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
    rw [h11₄, g₃ _ (by decide), h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
  have h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
    rw [keepR _ (by decide) (by decide) (by decide)]
    exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, hrd]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, hwr]
  have hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄]; exact f₃
  have hsp : s₄.gpr .rsp = s.gpr .rsp := ga _ (by simp [BlocksTo.argRegs])
  refine ⟨spreTo_of hp h16 (Nat.le_refl _) h9 ga h10₄ g11 rd₄' wr₄' hf₄, idxOk_of hp hx ga h9 h10₄ g11 hf₄ rd₄', ?_⟩
  rw [hsp, hf₄.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hx.s.sub_right kR'_sub) (show 32 / 8 < 2 ^ 64 by decide)]

end

/-- `vg_aes_gcm_encrypt_blocks_to` with a loop given the block index. -/
theorem encryptI_wp {M : CtxMode} (B : BlkFn M) (aligned : Bool) (c : EncCodeI M) {s : State}
    (hp : BT M s) (hx : IdxArg 32 s) :
    WP isa (encrypt B.enc (some c.enc) aligned true) s (Done s) := by
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ => ?_)
  exact WP.seq (WP.seq (WP.mono (stitchFullTo_okG hp (aligned := aligned)
    (fun s₄ h ga h9 h10₄ g11 hf₄ rd₄ => c.ok s₄ h (idxOk_of hp hx ga h9 h10₄ g11 hf₄ rd₄))
    h11 h10 hg hk hf hrd hwr) fun st M =>
    WP.mono (restFullTo_ok hp M) fun st' M' => tail_ok hp B M'))

end VG.Proof.AesGcm.X86_64.BlocksTo
