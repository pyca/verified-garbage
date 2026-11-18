module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Body
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Body
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinTag
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinTag
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.J0
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.J0
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! ### `Sm4Gcm.AArch64.PieceCT`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: the pieces are constant time

Untrusted: everything here is checked by Lean. Each piece run from two states
that its correctness proof describes with the same public values (the
addresses, lengths and offsets) leaks the same: its code between calls by the
taint analysis, from the registers those proofs pin, and its calls by their
callees' proofs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ofBytes)
open VG.Proof.Gcm (lensBlock)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem absorb_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block}
    {x₁ x₂ : List Byte} {D : Addr} {n o : Nat} {σ₁ σ₂ : State}
    (h₁ : AbsIn Ctx St W SP k₁ H₁ x₁ D n o σ₁) (h₂ : AbsIn Ctx St W SP k₂ H₂ x₂ D n o σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (absorb v.callees yo) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24, .x25]) (absSeg1 yo) h).isSome = true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24]) (.block (absSeg2 yo)) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23,
        h₁.x24, h₂.x24, h₁.x25, h₂.x25]) t₁)
    (absSeg1_ok L hyo h₁) (absSeg1_ok L hyo h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (absCall1_ok L hyo v a₁ h₁.ho h₁.hH) (absCall1_ok L hyo v a₂ h₂.ho h₂.hH) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24]) t₂)
    (absSeg2_ok L hyo b₁) (absSeg2_ok L hyo b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (absCall2_ok L hyo v c₁) (absCall2_ok L hyo v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.1.env.sp, d₂.1.env.sp])
    (by agree_tac [d₁.1.env.x20, d₂.1.env.x20, d₁.1.x23, d₂.1.x23, d₁.1.x24, d₂.1.x24]) ⟨_, by taint_decide⟩

/-- `absorbAl yo`: `absorb yo` with nothing buffered. -/
theorem absorbAl_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block}
    {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : AbsIn Ctx St W SP k₁ H₁ x₁ D n 0 σ₁) (h₂ : AbsIn Ctx St W SP k₂ H₂ x₂ D n 0 σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbAl v.callees yo) TT := by
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24]) (.block (absSeg2 yo)) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have b₁ := h₁.mid (yo := yo)
  have b₂ := h₂.mid (yo := yo)
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24]) t₂)
    (absSeg2_ok L hyo b₁) (absSeg2_ok L hyo b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (absCall2_ok L hyo v c₁) (absCall2_ok L hyo v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.1.env.sp, d₂.1.env.sp])
    (by agree_tac [d₁.1.env.x20, d₂.1.env.x20, d₁.1.x23, d₂.1.x23, d₁.1.x24, d₂.1.x24]) ⟨_, by taint_decide⟩

/-- `flush yo` of `o` bytes. -/
theorem flush_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {o : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o) (ho : o < 16) :
    RelCT isa (Eq2 σ₁ σ₂) (flush v.callees yo) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x25]) (padSeg yo [ptr .x12 .x20 32]) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pad : ∀ {k : Reg → BitVec 64} {σ : State}, Env Ctx St W SP σ → Kept k σ → σ.gpr .x25 = BitVec.ofNat 64 o →
      WP isa (padSeg yo [ptr .x12 .x20 32]) σ (Pad1 Ctx St W SP k yo o (St + BitVec.ofNat 64 32) σ.mem) :=
    fun he hk h25 => padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 ho
      (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
      (covers_left (he.perm.stC (by omega_using [ho]))) (L.st_w (by omega_using [ho]) (.inr ⟨by decide, by decide⟩))
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x25] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [he₁.x19, he₂.x19, he₁.x20, he₂.x20, he₁.x21, he₂.x21, h25₁, h25₂]) t₁)
    (pad he₁ hk₁ h25₁) (pad he₂ hk₂ h25₂) fun τ₁ τ₂ a₁ a₂ => ?_
  exact rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp])

/-- `lens yo ra rb`. -/
theorem lens_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {ra rb : Reg} (hrb : rb ≠ .x9)
    {k₁ k₂ : Reg → BitVec 64} {o₁ o₂ : Nat} {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂)
    (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o₁) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o₂)
    (ht : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block (lensSeg yo ra rb)) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (lens v.callees yo ra rb) TT := by
  refine rel_seq (rel_taint [.x19, .x20, .x21] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [he₁.x19, he₂.x19, he₁.x20, he₂.x20, he₁.x21, he₂.x21]) ht)
    (lensSeg_ok L hyo he₁ hk₁ h25₁ hrb) (lensSeg_ok L hyo he₂ hk₂ h25₂ hrb) fun τ₁ τ₂ a₁ a₂ => ?_
  exact rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp])

/-- `crypt`. -/
theorem crypt_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {P : Nat} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : CrIn Ctx St W SP k₁ P D n σ₁) (h₂ : CrIn Ctx St W SP k₂ P D n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt v.callees) TT := by
  have hc : ∀ {σ : State} {k : Reg → BitVec 64} (h : CrIn Ctx St W SP k P D n σ) {m' : Mem},
      Frame (crFrame St SP D n) σ.mem m' → ciphOf m' Ctx = ciphOf σ.mem Ctx :=
    fun h _ hf => ciph_frame hf (ctx_crFrame L h.data)
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23, h₁.x24, h₂.x24, h₁.x25, h₂.x25]) ⟨_, by taint_decide⟩)
    (crSeg1_ok L (icb := 0) h₁) (crSeg1_ok L (icb := 0) h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_ctr v.ctr a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (ctrCall1_ok L v a₁ (hc h₁ a₁.frame)) (ctrCall1_ok L v a₂ (hc h₂ a₂.frame)) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [b₁.1.env.sp, b₂.1.env.sp])
      (by agree_tac [b₁.1.env.x19, b₂.1.env.x19, b₁.1.env.x20, b₂.1.env.x20, b₁.1.env.x21, b₂.1.env.x21,
        b₁.1.x23, b₂.1.x23, b₁.1.x24, b₂.1.x24, b₁.1.x25, b₂.1.x25]) ⟨_, by taint_decide⟩)
    (crSeg2_ok L b₁.1 b₁.2) (crSeg2_ok L b₂.1 b₂.2) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_ctr v.ctr c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (ctrCall2_ok L v c₁ (hc h₁ c₁.frame)) (ctrCall2_ok L v c₂ (hc h₂ c₂.frame)) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.env.sp, d₂.env.sp])
    (by agree_tac [d₁.env.x20, d₂.env.x20, d₁.x23, d₂.x23, d₁.x24, d₂.x24]) ⟨_, by taint_decide⟩

/-- `cryptAl`: `crypt` from the start of a keystream block. -/
theorem cryptAl_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {P : Nat} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : CrIn Ctx St W SP k₁ P D n σ₁) (h₂ : CrIn Ctx St W SP k₂ P D n σ₂) (hP : P % 16 = 0) :
    RelCT isa (Eq2 σ₁ σ₂) (cryptAl v.callees) TT := by
  have hc : ∀ {σ : State} {k : Reg → BitVec 64} (h : CrIn Ctx St W SP k P D n σ) {m' : Mem},
      Frame (crFrame St SP D n) σ.mem m' → ciphOf m' Ctx = ciphOf σ.mem Ctx :=
    fun h _ hf => ciph_frame hf (ctx_crFrame L h.data)
  have m₁ := h₁.mid (icb := 0) hP
  have m₂ := h₂.mid (icb := 0) hP
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23, h₁.x24, h₂.x24]) ⟨_, by taint_decide⟩)
    (crArgs_ok L m₁) (crArgs_ok L m₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_ctr v.ctr a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (ctrCall1_ok L v a₁ (hc h₁ a₁.frame)) (ctrCall1_ok L v a₂ (hc h₂ a₂.frame)) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [b₁.1.env.sp, b₂.1.env.sp])
      (by agree_tac [b₁.1.env.x19, b₂.1.env.x19, b₁.1.env.x20, b₂.1.env.x20, b₁.1.env.x21, b₂.1.env.x21,
        b₁.1.x23, b₂.1.x23, b₁.1.x24, b₂.1.x24, b₁.1.x25, b₂.1.x25]) ⟨_, by taint_decide⟩)
    (crSeg2_ok L b₁.1 b₁.2) (crSeg2_ok L b₂.1 b₂.2) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_ctr v.ctr c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (ctrCall2_ok L v c₁ (hc h₁ c₁.frame)) (ctrCall2_ok L v c₂ (hc h₂ c₂.frame)) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.env.sp, d₂.env.sp])
    (by agree_tac [d₁.env.x20, d₂.env.x20, d₁.x23, d₂.x23, d₁.x24, d₂.x24]) ⟨_, by taint_decide⟩

/-- `lens yo ra rb`, run. -/
theorem lens_ok (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {ra rb : Reg} (hrb : rb ≠ .x9)
    {k : Reg → BitVec 64} {o : Nat} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 o) :
    WP isa (lens v.callees yo ra rb) s (TOut Ctx St W SP k yo o
      (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (St + BitVec.ofNat 64 yo))
        [ofBytes (lensBlock (s.gpr ra).toNat (s.gpr rb).toNat)]) s.mem) :=
  WP.seq (WP.mono (lensSeg_ok L hyo he hk h25 hrb) fun _ h₁ => lensCall_ok L hyo v h₁)

/-- `tag o`. -/
theorem tag_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {o₁ o₂ : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o₁) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o₂) :
    RelCT isa (Eq2 σ₁ σ₂) (tag v.callees o) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block (tagSeg o)) h).isSome = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (lens_rel L v (.inr rfl) (by decide) he₁ he₂ hk₁ hk₂ h25₁ h25₂ ⟨_, by taint_decide⟩)
    (lens_ok L v (.inr rfl) (by decide) he₁ hk₁ h25₁) (lens_ok L v (.inr rfl) (by decide) he₂ hk₂ h25₂)
    fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21] (by rw [a₁.env.sp, a₂.env.sp])
      (by agree_tac [a₁.env.x19, a₂.env.x19, a₁.env.x20, a₂.env.x20, a₁.env.x21, a₂.env.x21]) t₁)
    (tagSeg_ok L ho a₁.env a₁.kept)
    (tagSeg_ok L ho a₂.env a₂.kept) fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_ctr v.ctr b₁.call b₂.call (by rw [b₁.env.sp, b₂.env.sp])

/-- `j0hash`. -/
theorem j0hash_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np : Addr} {n : Nat}
    {σ₁ σ₂ : State} (h₁ : J0In Ctx St W SP k₁ H₁ Np n σ₁) (h₂ : J0In Ctx St W SP k₂ H₂ Np n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (j0hash v.callees) TT := by
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23,
        h₁.x24, h₂.x24]) ⟨_, by taint_decide⟩)
    (j0Seg_ok L h₁) (j0Seg_ok L h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (j0Call1_ok L v a₁) (j0Call1_ok L v a₂) fun τ₁ τ₂ b₁ b₂ => ?_
  have hlt := h₁.data.lt
  have pad : ∀ {k : Reg → BitVec 64} {H : Block} {m₀ : Mem} {σ : State}, J2 Ctx St W SP k H Np n m₀ σ →
      WP isa (padSeg 0 [mov .x12 .x23]) σ (Pad1 Ctx St W SP k 0 (n % 16) (Np + BitVec.ofNat 64 (16 * (n / 16)))
        σ.mem) := fun b => by
    have hdr := b.data.drop (k := 16 * (n / 16)) (by omega_using [])
    rw [show n - 16 * (n / 16) = n % 16 by omega_using []] at hdr
    exact padSeg_ok L (yo := 0) (.inl rfl) (P := Np + BitVec.ofNat 64 (16 * (n / 16)))
      b.env b.kept b.x25 (Nat.mod_lt _ (by decide))
      (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, b.x23], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
      hdr.rd (hdr.w.sub_right (Lay.wSub (by decide)))
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x25] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x25, b₂.x25]) ⟨_, by taint_decide⟩)
    (pad b₁) (pad b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (padCall_ok L (.inl rfl) v c₁) (padCall_ok L (.inl rfl) v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact lens_rel L v (.inl rfl) (by decide) d₁.env d₂.env d₁.kept d₂.kept d₁.x25 d₂.x25 ⟨_, by taint_decide⟩

omit L in
/-- The test of the nonce's length. -/
theorem j0pre_ok {s : State} {n : Nat} (h24 : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x9 .x24 12]) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ Regs [.x9] s s' := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  exact ⟨by simp [gpr_write, h24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

omit L in
theorem J0In.of_regs {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s s' : State}
    (h : J0In Ctx St W SP k H Np n s) (r : Regs [.x9] s s') : J0In Ctx St W SP k H Np n s' :=
  ⟨h.env.of_regs r, h.kept.of_others r.others, by rw [r.others _ (by decide)]; exact h.x23,
    by rw [r.others _ (by decide)]; exact h.x24, by rw [r.others _ (by decide)]; exact h.x26,
    by rw [r.others _ (by decide)]; exact h.x27, h.data.of_eq r.rd r.wr, by rw [r.mem]; exact h.hH⟩

omit L in
theorem j0ev {s : State} {n : Nat} (hlt : n < 2 ^ 64) (h9 : s.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) :
    isa.eval (.zero .x .x9) s = some (decide (n = 12)) := by
  show some (s.read .x .x9 == 0) = _
  rw [State.read, h9, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq hlt (by decide)]

/-- The branch of `j0`, run. -/
theorem j0ite_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) (h9 : s.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) :
    WP isa (.ite (.zero .x .x9) (.block j012) (j0hash v.callees)) s
      (J0Mid Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  refine WP.ite (decide (n = 12)) (j0ev h.data.lt h9) (fun ht => ?_) (fun hf => ?_)
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact j012_ok L h
  · exact j0hash_ok L v h (by simpa using hf)

/-- `j0`. -/
theorem j0_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np : Addr} {n : Nat}
    {σ₁ σ₂ : State} (h₁ : J0In Ctx St W SP k₁ H₁ Np n σ₁) (h₂ : J0In Ctx St W SP k₂ H₂ Np n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (j0 v.callees) TT := by
  refine rel_seq (rel_taint [.x24] (by rw [h₁.env.sp, h₂.env.sp]) (by agree_tac [h₁.x24, h₂.x24])
      ⟨_, by taint_decide⟩) (j0pre_ok h₁.x24) (j0pre_ok h₂.x24) fun τ₁ τ₂ ⟨a₁, r₁⟩ ⟨a₂, r₂⟩ => ?_
  have g₁ := h₁.of_regs r₁
  have g₂ := h₂.of_regs r₂
  refine rel_seq (rel_ite (j0ev h₁.data.lt a₁) (j0ev h₁.data.lt a₂) (fun ht => ?_) (fun _ => ?_))
    (j0ite_ok L v g₁ a₁) (j0ite_ok L v g₂ a₂) fun τ₁ τ₂ b₁ b₂ => ?_
  · have h12 : n = 12 := by simpa using ht
    exact rel_taint [.x20, .x23] (by rw [g₁.env.sp, g₂.env.sp])
      (by agree_tac [g₁.env.x20, g₂.env.x20, g₁.x23, g₂.x23]) ⟨_, by taint_decide⟩
  · exact j0hash_rel L v g₁ g₂
  · exact rel_taint [.x20] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x20, b₂.env.x20])
      ⟨_, by taint_decide⟩

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: the bodies are constant time

Untrusted: everything here is checked by Lean. Two runs of `encBody`,
`decAbs`, `decBody` or `finBody` from states with the same public values (the
lengths and the offset of the buffered additional data) leak the same.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem hz_mod (o : Nat) (ho : o < 16) : (Spec.Gcm.zeros o).length % 16 = o := by
  rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt ho

/-- `fo`, `flush` and `textArgs` in two runs, and what each leaves. -/
theorem padArgs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, CrIn Ctx St W SP k₁ P D n τ₁ → CrIn Ctx St W SP k₂ P D n τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq fo (.seq (flush v.callees 16) (.seq (.block textArgs) rest))) TT := by
  have hn := h₁.data.ok.lt
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k27₁ : k₁ .x27 = BitVec.ofNat 64 P := (h₁.kept .x27 (by decide)).symm.trans h₁.x27
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k27₂ : k₂ .x27 = BitVec.ofNat 64 P := (h₂.kept .x27 (by decide)).symm.trans h₂.x27
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine rel_seq (rel_taint [.x25, .x26, .x27] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.x25, h₂.x25, hq, h₁.x26, h₂.x26, h₁.x27, h₂.x27]) ⟨_, by taint_decide⟩)
    (fo_ok h₁.x25 h₁.x26 h₁.x27 hn h₁.hP) (fo_ok h₂.x25 h₂.x26 h₂.x27 hn h₂.hP)
    fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have he₁ := h₁.env.of_regs r₁
  have he₂ := h₂.env.of_regs r₂
  have hk₁ := h₁.kept.of_others r₁.others
  have hk₂ := h₂.kept.of_others r₂.others
  rw [← hq] at x25₂
  refine rel_seq (flush_rel L v (.inr rfl) he₁ he₂ hk₁ hk₂ x25₁ x25₂ (by split <;> omega_using []))
    (WP.with_rdwr (flushStep_ok L v (a := a₁) (c := c₁) (n := n) he₁ hk₁ (by rw [x25₁, h₁.hc]) rfl))
    (WP.with_rdwr (flushStep_ok L v (a := a₂) (c := c₂) (n := n) he₂ hk₂ (by rw [x25₂, h₂.hc, hq]) rfl))
    fun τ₁ τ₂ ⟨⟨fe₁, fk₁, _, _, _⟩, frd₁, fwr₁⟩ ⟨⟨fe₂, fk₂, _, _, _⟩, frd₂, fwr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x27, .x28] (by rw [fe₁.sp, fe₂.sp])
      (by agree_tac [fk₁ .x26 (by decide), fk₂ .x26 (by decide), fk₁ .x27 (by decide), fk₂ .x27 (by decide),
        fk₁ .x28 (by decide), fk₂ .x28 (by decide), k26₁, k26₂, k27₁, k27₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textArgs_ok fk₁ k26₁ k27₁ k28₁ h₁.hP) (textArgs_ok fk₂ k26₂ k27₂ k28₂ h₂.hP)
    fun τ₁ τ₂ ⟨a25₁, a23₁, a24₁, ra₁⟩ ⟨a25₂, a23₂, a24₂, ra₂⟩ => ?_
  have ge₁ := fe₁.of_regs ra₁
  have ge₂ := fe₂.of_regs ra₂
  have gk₁ := fk₁.of_others ra₁.others
  have gk₂ := fk₂.of_others ra₂.others
  exact hr τ₁ τ₂
    ⟨ge₁, gk₁, a23₁, a24₁, a25₁,
      h₁.data.of_eq (by rw [ra₁.rd, frd₁, r₁.rd]) (by rw [ra₁.wr, fwr₁, r₁.wr])⟩
    ⟨ge₂, gk₂, a23₂, a24₂, a25₂,
      h₂.data.of_eq (by rw [ra₂.rd, frd₂, r₂.rd]) (by rw [ra₂.wr, fwr₂, r₂.wr])⟩

/-- `textAbs` in two runs. -/
theorem textAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {σ₁ σ₂ : State}
    (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h23₁ : σ₁.gpr .x23 = D) (h23₂ : σ₂.gpr .x23 = D)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 n) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 n)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (P % 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (P % 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 n) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 n)
    (hd₁ : DataOk St W σ₁ D n) (hd₂ : DataOk St W σ₂ D n) :
    RelCT isa (Eq2 σ₁ σ₂) (textAbs v.callees) TT := by
  refine rel_ite (eval_zero h26₁ hd₁.lt) (eval_zero h26₂ hd₁.lt) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [he₁.sp, he₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact absorb_rel L v (.inr rfl)
      (⟨he₁, hk₁, h23₁, h24₁, h25₁, hz_mod _ (Nat.mod_lt _ (by decide)), hd₁, rfl⟩ :
        AbsIn Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₁)
      (⟨he₂, hk₂, h23₂, h24₂, h25₂, hz_mod _ (Nat.mod_lt _ (by decide)), hd₂, rfl⟩ :
        AbsIn Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₂)

/-- `encBody` in two runs. -/
theorem encBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (encBody v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (crypt_rel L v c₁ c₂) (WP.with_rdwr (crypt_ok L v (icb := 0) c₁))
    (WP.with_rdwr (crypt_ok L v (icb := 0) c₂)) fun τ₁' τ₂' ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [o₁.env.sp, o₂.env.sp])
      (by agree_tac [o₁.kept .x26 (by decide), o₂.kept .x26 (by decide), o₁.kept .x28 (by decide),
        o₂.kept .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok o₁.kept k26₁ k28₁) (textPiece_ok o₂.kept k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := o₁.kept.of_others rp₁.others
  have pk₂ := o₂.kept.of_others rp₂.others
  exact textAbs_rel L v (o₁.env.of_regs rp₁) (o₂.env.of_regs rp₂) pk₁ pk₂ p23₁ p23₂ p24₁ p24₂
    (by rw [rp₁.others _ (by decide), o₁.x25]) (by rw [rp₂.others _ (by decide), o₂.x25])
    ((pk₁ .x26 (by decide)).trans k26₁) ((pk₂ .x26 (by decide)).trans k26₂)
    (c₁.data.ok.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁]))
    (c₂.data.ok.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂]))

/-- `finBody o` in two runs. -/
theorem finBody_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {A P : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 A) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 A)
    (h27₁ : σ₁.gpr .x27 = BitVec.ofNat 64 P) (h27₂ : σ₂.gpr .x27 = BitVec.ofNat 64 P)
    (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    RelCT isa (Eq2 σ₁ σ₂) (finBody v.callees o) TT := by
  have ho' : (if P = 0 then A % 16 else P % 16) < 16 := by split <;> exact Nat.mod_lt _ (by decide)
  refine rel_seq (rel_taint [.x26, .x27] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [h26₁, h26₂, h27₁, h27₂]) ⟨_, by taint_decide⟩)
    (finOff_ok h26₁ h27₁ hA hP) (finOff_ok h26₂ h27₂ hA hP) fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have fe₁ := he₁.of_regs r₁
  have fe₂ := he₂.of_regs r₂
  have fk₁ := hk₁.of_others r₁.others
  have fk₂ := hk₂.of_others r₂.others
  refine rel_seq (flush_rel L v (.inr rfl) fe₁ fe₂ fk₁ fk₂ x25₁ x25₂ ho')
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₁.mem (Ctx + BitVec.ofNat 64 240)) fe₁ fk₁
      x25₁ (hz_mod _ ho') rfl)
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₂.mem (Ctx + BitVec.ofNat 64 240)) fe₂ fk₂
      x25₂ (hz_mod _ ho') rfl) fun τ₁ τ₂ ⟨t₁, _, _⟩ ⟨t₂, _, _⟩ => ?_
  exact tag_rel L v ho t₁.env t₂.env t₁.kept t₂.kept t₁.x25 t₂.x25

end

end VG.Proof.Sm4Gcm.AArch64
