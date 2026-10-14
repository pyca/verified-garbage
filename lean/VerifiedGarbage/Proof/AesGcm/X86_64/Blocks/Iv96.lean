module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.R10
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
public import VerifiedGarbage.Proof.AesGcm.X86_64.AlignedScratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on whole blocks, x86-64: given the block index

Untrusted: everything here is checked by Lean. With the low word of the
counter block also passed on the stack at `rsp + off` (`IdxArg`, a public
argument), a decryption loop that takes all the blocks may read it
(`DecCodeI`): it holds there when the loop starts (`idxOk_of`), since the
entry writes only the arguments kept in `scratch`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt)

/-- The block index at `rsp + off`: the low word of the counter block,
readable, and apart from the data and `scratch`. -/
structure IdxArg (off : Nat) (s : State) : Prop where
  eq : s.mem.readW (SP s + BitVec.ofNat 64 off) 32 = (blockAt s.mem (C s)).extractLsb' 0 32
  rd : InRegions s.rd (SP s + BitVec.ofNat 64 off) 4
  d : Region.Disjoint ⟨SP s + BitVec.ofNat 64 off, 4⟩ (dR s)
  s : Region.Disjoint ⟨SP s + BitVec.ofNat 64 off, 4⟩ (sR s)

/-- A decryption loop taking all the blocks, given the block index at
`rsp + 16`. -/
structure DecCodeI (M : CtxMode) where
  dec : Prog isa
  ok : ∀ s₀, Gcm.X86_64.Stitch.SPreM M s₀ →
    Gcm.X86_64.StitchZ.IdxOk 16 [Gcm.X86_64.Stitch.dR s₀, Gcm.X86_64.Stitch.pR s₀] s₀ →
    WP isa dec s₀ (Gcm.X86_64.Stitch.DPost s₀)

section
variable {M : CtxMode} {s : State} (hp : BP M s)
include hp

/-- `IdxArg` at the entry gives `IdxOk` where the loop starts. -/
theorem idxOk_of {aligned : Bool} {off : Nat} (hx : IdxArg off s) {s₃ : State}
    (ga : ∀ r ∈ Blocks.argRegs, s₃.gpr r = s.gpr r) (hsp : s₃.gpr .rsp = s.gpr .rsp)
    (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s))
    (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)))
    (hf : Frame [kR' s] s.mem s₃.mem) (hrd : s₃.rd = s.rd) :
    Gcm.X86_64.StitchZ.IdxOk off [Gcm.X86_64.Stitch.dR s₃, Gcm.X86_64.Stitch.pR s₃] s₃ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hb := AlignedScratch.offset_bounds aligned (S s)
  have ek : s₃.gpr .rdx = C s := ga _ (by simp [Blocks.argRegs])
  have e8 : s₃.gpr .r8 = D s := ga _ (by simp [Blocks.argRegs])
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
    · simp only [Gcm.X86_64.Stitch.dR, Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, e8, hq, hsp]
      exact hx.d.sub_right (Region.sub_prefix (by omega))
    · simp only [Gcm.X86_64.Stitch.pR, Gcm.X86_64.Stitch.pp, h11, hsp]
      exact hx.s.sub_right (Offset.sub_base _ (by omega))

end

/-- `vg_aes_gcm_decrypt_blocks` with a loop given the block index. -/
theorem decryptI_wp (v : GcmImpl) {M : CtxMode} {aligned : Bool} (c : DecCodeI M) {s : State}
    (hp : BP M s) (hx : IdxArg 16 s) :
    WP isa (decrypt v.callees.ctr v.callees.gh (some c.dec) aligned true) s (DecDone s) := by
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  have tl : ∀ q st, Mid s q q (blocksAt s.mem (D s) q) st →
      WP isa (tail (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st (DecDone s) := fun q st M =>
    tail_calls hp _ _ M (fun _ M' h0 => decDone_of hp M' h0) fun _ M' hlt => decCalls_ok hp v M' hlt
  exact fullBody_ok hp (aligned := aligned)
    (fun _ h ga hsp h9 g11 hf₃ rd₃ => c.ok _ h (idxOk_of hp hx ga hsp h9 g11 hf₃ rd₃))
    (fun _ _ h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP =>
      decDone_of hp (stitchDFull_ok hp h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP) (Nat.sub_self _))
    (fun h16 _ M => WP.seq (WP.mono (rest_ok hp (by omega) M) fun st' M' => tl _ st' M'))
    h11 hg hk hf hrd hwr

end VG.Proof.AesGcm.X86_64.Blocks
