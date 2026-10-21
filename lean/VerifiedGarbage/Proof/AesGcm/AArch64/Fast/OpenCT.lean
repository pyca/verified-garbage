module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits

/-!
# AES-GCM on AArch64: `open` with the path for TLS records is constant time

Untrusted: everything here is checked by Lean. The code of `openRunA` between
its calls by the taint analysis, from the registers that hold the pointers
and lengths (public in both runs), the call of `gh` by a hypothesis
(`hrel`), the tag's by `rel_ctr`; at each call, the correctness lemmas give
both runs' states (`Mid`, from `openA1_ok`). The rest of the path is
`openMain`'s (`omB_rel`), and the rest of `open` is `open`'s
(`openRestWith_rel`, `open_ct_of`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen ctxH ctxCiph)

/-- `omB_relD`, decrypting with `Tail.cryptAlT`, for a text of `x26` bytes. -/
theorem omB_relDT (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s' m₁ m₂ : State}
    (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo₁ : MidO fr Ctx W SP D Np A R nl al n tl s m₁) (mo₂ : MidO fr Ctx W SP D Np A R nl al n tl s' m₂)
    (x26₁ : m₁.gpr .x26 = BitVec.ofNat 64 n) (x26₂ : m₂.gpr .x26 = BitVec.ofNat 64 n)
    (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r) (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (omBWith (Impl.AesGcm.AArch64.Tail.cryptAlT v.callees)) TT := by
  unfold omBWith
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have hcr : ∀ {m : State} {σ : State} (mo : MidO fr Ctx W SP D Np A R nl al n tl σ m),
      m.gpr .x26 = BitVec.ofNat 64 n → ∀ {s₈ : State}, CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D n s₈ →
      s₈.gpr .x26 = m.gpr .x26 → s₈.wr = m.wr → ∀ icb, WP isa (Impl.AesGcm.AArch64.Tail.cryptAlT v.callees) s₈
        (CrOut Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R icb 0 D n s₈.mem) :=
    fun mo h26 _ h e26 hwr icb => cryptAlT_ok L v (icb := icb) h rfl (by rw [e26, h26])
      mo.data.ok.lt (tail_big (by rw [hwr]; exact mo.data.wr) mo.data.ok.lt (by simp) (Nat.zero_add n))
  refine rel_seq ?_ (omIteWith_ok _ hR mo₁ dD dC (hcr mo₁ x26₁)) (omIteWith_ok _ hR mo₂ dD dC (hcr mo₂ x26₂))
    fun a b ⟨ea, xa, _, _⟩ ⟨eb, xb, _, _⟩ =>
      rel_taint [.x27] (by rw [ea.sp, eb.sp]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp]) (by agree_tac [mo₁.env.x19, mo₂.env.x19])
      ⟨_, by taint_decide⟩) (ocLdr_ok mo₁.env mo₁.sD mo₁.sN) (ocLdr_ok mo₂.env mo₂.sD mo₂.sN)
      fun c₁ c₂ h₁ h₂ => ?_
    exact cryptAlT_rel L v (oc_in hR mo₁ h₁) (oc_in hR mo₂ h₂) rfl
      (by rw [h₁.2.2.2.others _ (by decide), h₂.2.2.2.others _ (by decide), x26₁, x26₂])

section
variable {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `front` and the arguments of the call on the whole blocks: `Mid` after
`front`, and `Abs3`. -/
theorem openA1_ok (hMK : MulKey) {s₀ t : State} (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) :
    WP isa (.seq Impl.AesGcm.AArch64.Fast.front (.block ([mov .x24 .x26, imm .x25 0] ++ absSeg2 16))) t
      fun s₆ => ∃ s₂ : State, ∃ X : Addr,
        Mid Ctx W SP (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) R n D (BitVec.ofNat 64 tl) X t s₂ ∧
        Abs3 Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr 16 (blockAt t.mem (Ctx + BitVec.ofNat 64 240))
          (bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length)) D n 0 s₂.mem 0 s₆ ∧
        s₆.rd = s₂.rd ∧ s₆.wr = s₂.wr := by
  have L := o.lay
  have hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t :=
    ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, rfl⟩
  refine WP.seq (WP.mono (front_ok L hMK hJ o.aad hal h4 h5 h6 h7) fun s₂ h₂ => ?_)
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, x24₃, x25₃, r₃⟩ : ∃ s₃, runBlock isa [mov .x24 .x26, imm .x25 0] s₂ =
      some s₃ ∧ s₃.gpr .x24 = BitVec.ofNat 64 n ∧ s₃.gpr .x25 = BitVec.ofNat 64 0 ∧ Regs [.x24, .x25] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h₂.x26], by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := h₂.env.of_regs r₃
  have hdat₃ : DataOk (W + BitVec.ofNat 64 16) W s₃ D n :=
    o.dat.ok.of_eq (by rw [r₃.rd, h₂.rd]) (by rw [r₃.wr, h₂.wr])
  have hx₁0 : (bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length)).length % 16 = 0 := by
    rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr 16 (blockAt t.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length)) D n 0 s₂.mem 0 s₃ :=
    ⟨he₃, fun r hr => r₃.others r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide), Nat.zero_le _, by rw [r₃.others _ (by decide), h₂.x23]; simp,
      by rw [x24₃, Nat.sub_zero], x25₃, hdat₃, by rw [r₃.mem]; exact h₂.hH,
      fun ha => by rw [r₃.mem]; simpa [bytesAt] using ha, .inr (by omega), by rw [r₃.mem]; exact Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  refine ⟨s₂, s₂.gpr .x27, ⟨h₂.env, h₂.x22.trans o.x22, o.rounds, h₂.x26, rfl, h₂.x28.trans o.x28, h₂.hH,
    h₂.key, o.dat.of_eq h₂.rd h₂.wr, h₂.frame.sub fun r hr => ⟨_, List.mem_cons_self .., ?_⟩, h₂.rd, h₂.wr⟩, h₆,
    by rw [rd₆, r₃.rd], by rw [wr₆, r₃.wr]⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide)

/-- `openRunA` in two runs, from the same public pointers and lengths. -/
theorem openRunA_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {s₀₁ s₀₂ t₁ t₂ : State}
    {ex : List Region} (hexW : ∀ r ∈ ex, (workR W).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (o₁ : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀₂ t₂)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = D ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = D ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (hal : al ≤ 16)
    (hgh₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₁.rd → s'.wr = t₁.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] t₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hgh₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₂.rd → s'.wr = t₂.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] t₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hrel : ∀ {s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) → s₁.sp = SP → s₂.sp = SP →
      s₁.rd = t₁.rd → s₁.wr = t₁.wr → Frame [workR W, ⟨D, n⟩] t₁.mem s₁.mem →
      s₂.rd = t₂.rd → s₂.wr = t₂.wr → Frame [workR W, ⟨D, n⟩] t₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT) :
    RelCT isa (Eq2 t₁ t₂) (openRunA v.callees cl) TT := by
  have L := o₁.lay
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  unfold openRunA
  refine RelCT.seq_assoc (rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
      (by rw [o₁.env.sp, o₂.env.sp])
      (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, o₁.env.x19, o₂.env.x19, o₁.env.x20, o₂.env.x20,
        o₁.env.x21, o₂.env.x21, o₁.x23, o₂.x23]) ⟨_, by taint_decide⟩)
    (openA1_ok hMK o₁ x4₁ x5₁ x6₁ x7₁ hal) (openA1_ok hMK o₂ x4₂ x5₂ x6₂ x7₂ hal)
    fun u₁ u₂ ⟨q₁, X₁, M₁, a₁, rd₁, wr₁⟩ ⟨q₂, X₂, M₂, a₂, rd₂, wr₂⟩ => ?_)
  have fr₁ : Frame [workR W, ⟨D, n⟩] t₁.mem u₁.mem := M₁.fr.trans (absFrame_wd a₁.frame)
  have fr₂ : Frame [workR W, ⟨D, n⟩] t₂.mem u₂.mem := M₂.fr.trans (absFrame_wd a₂.frame)
  have r₁ : u₁.rd = t₁.rd := rd₁.trans M₁.rd
  have w₁ : u₁.wr = t₁.wr := wr₁.trans M₁.wr
  have r₂ : u₂.rd = t₂.rd := rd₂.trans M₂.rd
  have w₂ : u₂.wr = t₂.wr := wr₂.trans M₂.wr
  have sY : Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ (workR W) := stW (by decide)
  have sS : Region.Sub ⟨W + BitVec.ofNat 64 512, 256⟩ (workR W) := Lay.wSub (by decide)
  have hexH : ∀ r ∈ ex, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := fun r hr =>
    (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
  have hexB : ∀ r ∈ ex, (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint r := fun r hr =>
    (hexW r hr).sub_left (stW (by decide))
  have hexK : ∀ r ∈ ex, (keyR W).Disjoint r := fun r hr => (hexW r hr).sub_left (Lay.wSub (by decide))
  have hDd : Region.Sub ⟨D + BitVec.ofNat 64 0, 16 * ((n - 0) / 16)⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
  refine rel_seq (hrel a₁.call a₂.call sY sS a₁.env.sp a₂.env.sp r₁ w₁ fr₁ r₂ w₂ fr₂ hDd)
    (WP.with_rdwr (absCall2WithX_ok L (.inr rfl) (Q := fun _ => True) hexH hexB a₁
      (WP.mono (hgh₁ _ a₁.call sY sS r₁ w₁ a₁.env.sp fr₁ hDd) fun _ g => ⟨g, trivial⟩)))
    (WP.with_rdwr (absCall2WithX_ok L (.inr rfl) (Q := fun _ => True) hexH hexB a₂
      (WP.mono (hgh₂ _ a₂.call sY sS r₂ w₂ a₂.env.sp fr₂ hDd) fun _ g => ⟨g, trivial⟩)))
    fun s₇ t₇ ⟨⟨⟨b₁, l₁⟩, _⟩, rd₇, wr₇⟩ ⟨⟨⟨b₂, l₂⟩, _⟩, rd₇', wr₇'⟩ => ?_
  have N₁ := Mid.absorbX L M₁ b₁ (by rw [rd₇, rd₁]) (by rw [wr₇, wr₁]) hexK
  have N₂ := Mid.absorbX L M₂ b₂ (by rw [rd₇', rd₂]) (by rw [wr₇', wr₂]) hexK
  refine RelCT.seq_assoc3 (rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x26] (by rw [N₁.env.sp, N₂.env.sp])
      (by agree_tac [N₁.env.x19, N₂.env.x19, N₁.env.x20, N₂.env.x20, N₁.env.x21, N₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24, N₁.x26, N₂.x26]) ⟨_, by taint_decide⟩)
    (ctE_ok L hMK (.inr rfl) N₁ b₁ l₁) (ctE_ok L hMK (.inr rfl) N₂ b₂ l₂)
    fun s₁₆ t₁₆ ⟨_, _, _, _, T₁, k28₁⟩ ⟨_, _, _, _, T₂, k28₂⟩ => ?_)
  refine rel_seq (rel_ctr v.ctr T₁.call T₂.call (by rw [T₁.env.sp, T₂.env.sp]))
    (tagCall_ok L v (.inr rfl) T₁) (tagCall_ok L v (.inr rfl) T₂) fun s₁₇ t₁₇ O₁ O₂ => ?_
  exact rel_taint [.x19, .x28] (by rw [O₁.env.sp, O₂.env.sp])
    (by agree_tac [O₁.env.x19, O₂.env.x19, O₁.kept .x28 (by decide), O₂.kept .x28 (by decide), k28₁, k28₂])
    ⟨_, by taint_decide⟩

/-- `openRunWith` in two runs, after `tagIn`, whose tags compare alike, with
`gh` called with memory changed since the entries `s₀₁`, `s₀₂` only in the
working space and the text. -/
theorem openRunWith_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {nl : Nat} {s₀₁ s₀₂ t₁ t₂ : State}
    {ex : List Region} (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (o₁ : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀₂ t₂)
    (h12 : nl = 12)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = D ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = D ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (hal : al ≤ 16) (rt₁ : bytesAt t₁.mem W tl = bytesAt s₀₁.mem Tg tl)
    (rt₂ : bytesAt t₂.mem W tl = bytesAt s₀₂.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true)
    (hb : (Spec.Gcm.openResult (ctxCiph s₀₁.mem Ctx R) (ctxH s₀₁.mem Ctx) tl (bytesAt s₀₁.mem Np nl)
        (bytesAt s₀₁.mem D n) (bytesAt s₀₁.mem A al) (bytesAt s₀₁.mem Tg tl)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀₂.mem Ctx R) (ctxH s₀₂.mem Ctx) tl (bytesAt s₀₂.mem Np nl)
        (bytesAt s₀₂.mem D n) (bytesAt s₀₂.mem A al) (bytesAt s₀₂.mem Tg tl)).isSome)
    (hgh₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀₁.rd → s'.wr = s₀₁.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hgh₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀₂.rd → s'.wr = s₀₂.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hrel : ∀ {s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) → s₁.sp = SP → s₂.sp = SP →
      s₁.rd = s₀₁.rd → s₁.wr = s₀₁.wr → Frame [workR W, ⟨D, n⟩] s₀₁.mem s₁.mem →
      s₂.rd = s₀₂.rd → s₂.wr = s₀₂.wr → Frame [workR W, ⟨D, n⟩] s₀₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT) :
    RelCT isa (Eq2 t₁ t₂) (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) TT := by
  subst h12
  have L := o₁.lay
  have F₁ : Frame [workR W, ⟨D, n⟩] s₀₁.mem t₁.mem :=
    o₁.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  have F₂ : Frame [workR W, ⟨D, n⟩] s₀₂.mem t₂.mem :=
    o₂.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  have g₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₁.rd → s'.wr = t₁.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] t₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex :=
    fun s' _ _ _ _ hc sY sS hr hw hsp hf hd =>
      hgh₁ s' hc sY sS (hr.trans o₁.rd₀) (hw.trans o₁.wr₀) hsp (F₁.trans hf) hd
  have g₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₂.rd → s'.wr = t₂.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] t₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex :=
    fun s' _ _ _ _ hc sY sS hr hw hsp hf hd =>
      hgh₂ s' hc sY sS (hr.trans o₂.rd₀) (hw.trans o₂.wr₀) hsp (F₂.trans hf) hd
  refine (openRunWith_split v.callees cl).symm.rel (rel_seq
    (openRunA_relX v cl hMK hexW hexC o₁ o₂ hx₁ hx₂ hal g₁ g₂ fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd =>
      hrel c₁ c₂ sY sS sp₁ sp₂ (r₁.trans o₁.rd₀) (w₁.trans o₁.wr₀) (F₁.trans f₁) (r₂.trans o₂.rd₀) (w₂.trans o₂.wr₀)
        (F₂.trans f₂) hd)
    (WP.mono (openRunAX_ok cl v hMK (I := fun _ => True) o₁ hx₁.1 hx₁.2.1 hx₁.2.2.1 hx₁.2.2.2 hal hok
      hexW hexD hexC (fun _ _ => trivial) fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₁ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) fun _ q => q.1)
    (WP.mono (openRunAX_ok cl v hMK (I := fun _ => True) o₂ hx₂.1 hx₂.2.1 hx₂.2.2.1 hx₂.2.2.2 hal hok
      hexW hexD hexC (fun _ _ => trivial) fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₂ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) fun _ q => q.1)
    fun m₁ m₂ ⟨mo₁, x26₁⟩ ⟨mo₂, x26₂⟩ => ?_)
  refine omB_relDT v L o₁.rounds mo₁ mo₂ x26₁ x26₂ (disj_ex (keep_of_sub (fastFrame_work W) o₁.ddW) hexD)
    (disj_ex (keep_of_sub (fastFrame_work W) o₁.dcW) hexC) ?_
  rw [mo₁.x27, mo₂.x27, tagBit o₁ rt₁ hok, tagBit o₂ rt₂ hok, hb]

end

/-- `vg_aes_gcm_open` with the path for TLS records, its whole blocks hashed
by `gh`, is constant time, for a `gh` that hashes as `vg_ghash` and leaks the
same in two runs, called with memory changed since the entry only in the
working space and the text. -/
theorem openWithEX_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {w : Nat} (hw : w = 2 ∨ w = 3)
    {pre : State → Prop} {extra extraW : State → List Region}
    (hpre : ∀ s, pre s → openPreXW w (extra s) s (extraW s))
    {ex : State → List Region}
    (hexW : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (workR (stackArg σ w)).Disjoint r)
    (hexD : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ {σ : State}, pre σ → ∀ r ∈ ex σ, (⟨σ.gpr .x0, 256⟩ : Region).Disjoint r)
    (hexq : ∀ {σ₁ σ₂ : State}, onePub (w + 1) σ₁ σ₂ → ex σ₂ = ex σ₁)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩ : Region) →
      WP isa cl s fun u => GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u (ex σ))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Fast.openWithE v.callees (8 * w) cl) := by
  unfold Impl.AesGcm.AArch64.Fast.openWithE
  refine open_ct_ofW hw hpre fun {σ₁ σ₂ s₁ s₂} p₁ p₂ hq o₁ o₂ x12₁ x12₂ k₁ k₂ hb => ?_
  have hq₀ := hq
  have exq := hexq hq
  obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
  have k5₁ : s₁.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₁ .x5 (by simp), ofNat_toNat']
  have k5₂ : s₂.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₂ .x5 (by simp), ofNat_toNat']
  refine rel_seq (rel_taint [.x5, .x24] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [k5₁, k5₂, o₁.x24, o₂.x24])
      ⟨_, by taint_decide⟩)
    (cond_ok k5₁ (σ₁.gpr .x5).isLt o₁.x24 (σ₁.gpr .x3).isLt) (cond_ok k5₂ (σ₁.gpr .x5).isLt o₂.x24 (σ₁.gpr .x3).isLt)
    fun u₁ u₂ ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ => ?_
  have v₁ := o₁.of_regs r₁
  have v₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = stackArg σ₁ 0 := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = stackArg σ₁ 0 := by rw [r₂.others _ (by decide), x12₂]
  have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr]
  have hlt : ((if (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 then 0 else 1 : Nat)) < 2 ^ 64 := by
    split <;> decide
  refine rel_ite (eval_zero c₁ hlt) (eval_zero c₂ hlt) (fun ht => ?_) (fun _ => ?_)
  · have hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 := by
      by_contra hc; simp [hc] at ht
    have hgh₂ := @hgh σ₂
    rw [exq, ← q0, ← qa w (by omega), ← q6, ← q7] at hgh₂
    have regs : ∀ {u t : State}, (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u.gpr r = σ₁.gpr r) →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = u.gpr r) →
        t.gpr .x4 = σ₁.gpr .x4 ∧ t.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat ∧ t.gpr .x6 = σ₁.gpr .x6 ∧
          t.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := fun ku kt =>
      ⟨by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat'],
        by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat']⟩
    unfold Impl.AesGcm.AArch64.Fast.openFastP
    refine openRestWith_rel v₁ v₂ y12₁ y12₂
      (fun o' hT hok hx => have e := regs kk₁ hx
        openRunWith_postE cl v hMK o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (hexW p₁) (hexD p₁) (hexC p₁)
          fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh p₁ c sY sS hr hw hsp hf hd)
      (fun o' hT hok hx => have e := regs kk₂ hx
        openRunWith_postE cl v hMK o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (hexW p₁) (hexD p₁) (hexC p₁)
          fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd)
      fun p₁' p₂' rt₁ rt₂ hok hx₁ hx₂ => openRunWith_relX v cl hMK (hexW p₁) (hexD p₁) (hexC p₁) p₁' p₂' hc.2 (regs kk₁ hx₁) (regs kk₂ hx₂)
        hc.1 rt₁ rt₂ hok hb (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh p₁ c sY sS hr hw hsp hf hd)
        (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd)
        fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd
  · exact openRestWith_rel v₁ v₂ y12₁ y12₂ (fun o' hT hok _ => openMain_post v o' hT hok)
      (fun o' hT hok _ => openMain_post v o' hT hok) fun p₁' p₂' rt₁ rt₂ hok _ _ =>
        openMain_rel v p₁' p₂' rt₁ rt₂ hok hb

theorem openWithE_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) {w : Nat} (hw : w = 2 ∨ w = 3)
    {pre : State → Prop} {extra : State → List Region} (hpre : ∀ s, pre s → openPreXW w (extra s) s)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      WP isa cl s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) cl TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Fast.openWithE v.callees (8 * w) cl) :=
  openWithEX_ct v cl hMK hw hpre (ex := fun _ => []) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => rfl) (fun p c y z r w sp f _ => hgh p c y z r w sp f)
    fun p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂

/-- `vg_aes_gcm_open` with the path for TLS records, its whole blocks hashed
by `gh`, is constant time, for a `gh` that hashes as `vg_ghash` and leaks the
same in two runs, called with memory changed since the entry only in the
working space and the text. -/
theorem openWith_ct (v : GcmImpl) (gh : Fn) (hMK : MulKey) {pre : State → Prop} {extra : State → List Region}
    (hpre : ∀ s, pre s → openPreX (extra s) s)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 2)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ 2)) →
      s.rd = σ.rd → s.wr = σ.wr →
      Frame [workR (stackArg σ 2), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      WP isa (.call gh.name gh.code) s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub 3 σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ 2)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ 2)) → s₁.sp = s₂.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ 2), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ 2), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) (.call gh.name gh.code) TT) :
    ConstantTime isa pre openAArch64.pub (Impl.AesGcm.AArch64.Fast.openWith v.callees gh) :=
  openWithE_ct (w := 2) v _ hMK (.inl rfl) (fun s h => openPreX_W (hpre s h))
    (fun p c y z r w _ f => hgh p c y z r w f)
    (fun p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ =>
      hrel p₁ p₂ hq c₁ c₂ y z (sp₁.trans sp₂.symm) r₁ w₁ f₁ r₂ w₂ f₂)

/-- `vg_aes_gcm_open` with the path for TLS records is constant time. -/
theorem open_fast_ct (v : GcmImpl) (hMK : MulKey) :
    ConstantTime isa openAArch64.pre openAArch64.pub (Impl.AesGcm.AArch64.Fast.«open» v.callees) :=
  openWith_ct (extra := fun _ => []) v v.gh.fn hMK (fun _ h => h) (fun _ hc _ _ _ _ _ => gh_call v.gh hc)
    (fun _ _ _ c₁ c₂ _ _ sp _ _ _ _ _ _ => rel_gh v.gh c₁ c₂ sp)

end VG.Proof.AesGcm.AArch64.Fast
