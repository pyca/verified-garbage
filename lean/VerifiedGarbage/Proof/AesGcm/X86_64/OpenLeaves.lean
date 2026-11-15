module

public import VerifiedGarbage.Proof.AesGcm.X86_64.SealLeaves
public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Undo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenTag
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Leaves
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-GCM on x86-64: what `vg_aes_gcm_open` leaves in `work`

Untrusted: everything here is checked by Lean. With implementations of
`vg_aes_ctr32` and `vg_ghash` that never touch their working space, and a
`vg_aes_gcm_decrypt_blocks` that leaves in its `scratch` a function of its
arguments (`BlkLeft`), `open` leaves in `work` from byte 272 on, whether or
not the tags match, a function of its argument registers and stack
arguments (`open_leaves`, `openL`): in the blocks function's `scratch` at
448 what it leaves there, if the tag length is allowed and there was a whole
block, and elsewhere what was there. Each piece's frame: `J₀` and the
additional data (`oneAad_okF`), the whole blocks (`oneBlocksD_okL`), the tag
(`oneTagU_okF`), the received tag and the comparison (`recv_ok`, `cmp_ok`),
and the rest decrypted (`oneCrypt_okF`) or the whole blocks encrypted again
(`oneUndo_okF`).
-/

-- separate module: its one importer imports `Instances`, and with it every proof of AES-GCM on x86-64; these generic proofs need no re-checking when one of those changes

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-! ## The whole blocks -/

/-- A call of `vg_aes_gcm_decrypt_blocks` that leaves `Lb` in its `scratch`. -/
theorem blkD_callL {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Lb : BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb B.dec.code M)
    {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall M s K C Y D S R q) :
    WP isa (.call B.dec.name B.dec.code) s fun s' => BlkPost s C Y D S q s' ∧
      ∀ x, (⟨S, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (Lb K (BitVec.ofNat 64 R) C Y D (BitVec.ofNat 64 q) S x).getD (s.mem x) := by
  let k : Contract isa := ⟨(Proof.AesGcm.decryptBlocksX86_64M M).pre, fun s s' => ∀ x,
    (⟨stackArg s 0, 2112⟩ : Region).Contains x 1 → s'.mem x = (Lb (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) x).getD (s.mem x), Proof.AesGcm.blocksPub⟩
  refine WP.call (k := k) (fun s' hs => ?_) B.decNosp (by rw [B.decDepth]; decide)
    (rd := BlkCall.rd M s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  · obtain ⟨t, s'', e, ha, -⟩ := B.decOk s' hs
    exact ⟨t, s'', e, ha, hL s' t s'' hs e⟩
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [B.decDepth] at hf
  refine ⟨⟨hrd, hwr, hcs, hf⟩, fun x hx => ?_⟩
  have e := hpost x (by rw [h.arg_eq]; exact hx)
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.arg_eq] at e
  rw [← hm₂, e, frame_at (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.t_s.sub_left (BlkCall.ret_sub (s := s))).symm) hx]

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- The frame of the call of `vg_aes_gcm_decrypt_blocks` that leaves `Lb` in
its `scratch`. -/
theorem obFrameD_okL {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Lb : BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb B.dec.code M)
    {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn M Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call B.dec.name B.dec.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s₄.mem x = (Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 16) D
          (BitVec.ofNat 64 q) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega_arith
  obtain ⟨hfp, -⟩ := pushRegs_mem s [.rax] (by decide) hn8
  have hfp' : Frame [below SP 8] s.mem (pushed [.rax] s).mem := by rw [← hsp]; exact hfp
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (blkD_callL B hL (ObIn.call L h))
    fun s₃ ⟨bp, o⟩ => ?_)
  obtain ⟨r₃, w₃, cs, rd, wr, fr⟩ := ObIn.popped L h bp
  refine ⟨r₃, w₃, cs, rd, wr, fr, fun x hx => ?_⟩
  rw [popped_mem, o x hx, frame_at hfp' (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.t_w.sub_left (below_sub (by decide) (by decide))).sub_right (Lay.wSub (by decide))).symm) hx]

end

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneBlocks` of the decrypting function that leaves `Lb` in its
`scratch` at `W + 448`: there, if there was a whole block, what `Lb` says. -/
theorem oneBlocksD_okL {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Lb : BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb B.dec.code M)
    {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) :
    WP isa (oneBlocks B.dec) s fun s' => ObPost Ctx W SP D n s s' ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (if n / 16 = 0 then none else Lb Ctx (BitVec.ofNat 64 R)
          (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) D
          (BitVec.ofNat 64 (n / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have d192 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 192, 8⟩ : Region)],
      (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have f192 : ∀ v : BitVec 64, Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem (s.mem.writeW (W + BitVec.ofNat 64 192) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine oneBlocks_coreZ L _ h (Out := fun s s' => ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
      s'.mem x = (if n / 16 = 0 then none else Lb Ctx (BitVec.ofNat 64 R)
        (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) D
        (BitVec.ofNat 64 (n / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x)) (fun s₂ hz hi => WP.mono (obFrameD_okL L B hL hi) fun s₄ ⟨a, b, c, d, e⟩ =>
    ⟨a, b, c, d, fun x hx => by rw [ite_eq_right hz]; exact e x hx⟩) (fun hz s₁ m₁ x hx => ?_)
    (fun s₂ s₄ s₅ m₂ o f x hx => ?_)
  · rw [ite_eq_left hz, Option.getD_none, m₁, frame_at (f192 _) d192 hx]
  · rw [frame_at f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)) hx,
      o x hx, m₂, frame_at (f192 _) d192 hx]

/-! ## The tag at `W + 112` -/

/-- What `oneTag 112` writes, with implementations of `vg_ghash` and
`vg_aes_ctr32` that write none of their working space: `W` from byte 16 to
128 and the stack. -/
abbrev tagFU (W SP : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 112⟩, below SP 8]

/-- `oneTag 112`, with implementations of `vg_ghash` and `vg_aes_ctr32` that
never touch their working space: what it writes (`tagFU`). -/
theorem oneTagU_okF (v : GcmImpl) (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) {R : Nat}
    {D : Addr} {n : Nat} {a t : BitVec 64} {H : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = t) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = a)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneTag v.callees uO) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame (tagFU W SP) s.mem s'.mem ∧
      s'.mem.readW (W + BitVec.ofNat 64 96) 64 = byteRev64 (BitVec.ofNat 64 (8 * a.toNat)) ∧
      s'.mem.readW (W + BitVec.ofNat 64 104) 64 = byteRev64 (BitVec.ofNat 64 (8 * t.toNat)) := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (([] : List Byte).length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have hai : AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H [] D n s₁ :=
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁, hH]⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorbPad_ok v (G := GhFits.free v gf 2560) L (yo := 16) (.inr rfl) hai rfl))
    fun s₄ ⟨hf, hrd₄, hwr₄⟩ => ?_)
  rw [hm₁] at hf
  obtain ⟨m₂, fa, ft⟩ := hf.frame
  have he₄ := hf.env
  have kp : ∀ d, 112 ≤ d → d + 8 ≤ 512 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => by
      rw [ft.readW (Region.contains_self _ _) (fun r hr => slot_abs16 L h₁ h₂ r (List.mem_append_right _ hr)) (by decide),
        fa.readW (Region.contains_self _ _) (fun r hr => slot_abs16 L h₁ h₂ r (List.mem_append_left _ hr)) (by decide)]
  have q₄ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have q₅ := he₄.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧ s₅.gpr .rbx = a ∧
      s₅.gpr .rbp = t ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧
      s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, q₄, q₅], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, kp 184 (by decide) (by decide), hal]
    · simp [gpr_setReg, kp 192 (by decide) (by decide), htl]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have hR₅ : RoundsAt s₅.mem W R := ⟨by rw [hm₅, kp 176 (by decide) (by decide)]; exact hR.1, hR.2⟩
  have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by rw [hm₅, hf.hH]
  refine WP.mono (WP.with_rdwr (tag_okL v (G := GhFits.free v gf 512) L.to512 (by decide) (TagCall.free v cf 512)
    (o := 112) (.inr rfl) he₅.to512 hH₅ hR₅ rfl)) fun s₆ ⟨⟨ht, h96, h104⟩, hrd₆, hwr₆⟩ => ?_
  have hS : ∀ {d k : Nat}, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 16, 112⟩ := fun {d k} h =>
    Offset.sub_base _ (by omega_arith)
  refine ⟨⟨ht.env.r13, ht.env.r14, ht.env.r15, ht.env.rsp, he₅.perm.of_eq hrd₆ hwr₆⟩,
    by rw [hrd₆, hrd₅, hrd₄, hrd₁], by rw [hwr₆, hwr₅, hwr₄, hwr₁], ?_, by rw [h96, hbx₅], by rw [h104, hbp₅]⟩
  refine ((fa.sub fun r hr => ?_).trans (ft.sub fun r hr => ?_)).trans (hm₅ ▸ ht.frame.sub fun r hr => ?_) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using hS (d := 0) (k := 32) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-! ## The whole blocks encrypted again -/

/-- What `oneUndo` writes, with an implementation of `vg_aes_ctr32` that never
touches its working space: the counter block, the whole blocks and the stack. -/
abbrev undoFrameF (W SP D : Addr) (q : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16 * q⟩, below SP 8]

/-- `oneUndo`, with an implementation of `vg_aes_ctr32` that never touches its
working space: what it writes (`undoFrameF`). -/
theorem oneUndo_okF (v : GcmImpl) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) {R : Nat} {D : Addr} {n : Nat}
    {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)))
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneUndo v.callees) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame (undoFrameF W SP D (n / 16)) s.mem s'.mem := by
  have hn := hd.ok.lt
  rw [oneUndo_eq]
  refine WP.seq (WP.mono (undo1_ok hn he htl hdat) fun s₁ ⟨hcx, h8, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun _ => ?_) (fun _ => ?_)
  · exact WP.block_nil ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _⟩
  · refine WP.seq (WP.mono (undo2_ok L he₁ ⟨by rw [m₁]; exact hR.1, hR.2⟩ (hd.of_eq rd₁ wr₁) hcx h8)
      fun s₂ ⟨hcall, he₂, hm₂, hrd₂, hwr₂⟩ => ?_)
    have hk := he₂.rsp
    refine WP.mono (ctr_callF v.ctr cf (Blocks.CtrCall.toF hcall)) fun s₃ g => ?_
    refine ⟨he₂.of_saved g.saved g.rd g.wr, g.rd.trans (hrd₂.trans rd₁), g.wr.trans (hwr₂.trans wr₁), ?_⟩
    rw [← m₁, ← hm₂, ← hk]; exact g.frame

end

/-! ## After the entry -/

/-- What `open`'s body for a tag length it allows leaves at `x` in `W` from
byte 272 on: in the blocks function's `scratch` (from 448) what `Lb` says,
if there was a whole block; elsewhere nothing written (`none`). -/
def openLW (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (Ctx : Addr) (R : Nat) (W D : Addr) (n : Nat) (x : Addr) : Option (BitVec 8) :=
  if n / 16 = 0 ∨ (x - W).toNat < 448 then none
  else Lb Ctx (BitVec.ofNat 64 R) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) D (BitVec.ofNat 64 (n / 16)) (W + BitVec.ofNat 64 448) x

/-- A byte of `W` from 272 on is in the blocks function's `scratch` (from 448)
or in the 176 bytes before it. -/
theorem rg_split {W x : Addr} (hx : (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Contains x 1) :
    ((⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 ∧ ¬ (x - W).toNat < 448) ∨
      ((⟨W + BitVec.ofNat 64 272, 176⟩ : Region).Contains x 1 ∧ (x - W).toNat < 448) := by
  have hx' : (x - (W + BitVec.ofNat 64 272)).toNat < 2288 := by simp only [Region.Contains] at hx; omega_using [hx]
  have hlt := (Offset.lt_iff x W (d := 272) (n := 2288) (by decide)).1 hx'
  by_cases h : (x - W).toNat < 448
  · refine .inr ⟨?_, h⟩
    have := (Offset.lt_iff x W (d := 272) (n := 176) (by decide)).2 ⟨hlt.1, by omega_arith⟩
    simp only [Region.Contains]; omega_using [this]
  · refine .inl ⟨?_, h⟩
    have := (Offset.lt_iff x W (d := 448) (n := 2112) (by decide)).2 ⟨by omega_arith, by omega_arith⟩
    simp only [Region.Contains]; omega_using [this]

/-- What `open`'s body for a tag length it allows leaves, from `s₂` (after
the entry) to `s'`: `W` from byte 272 on as `openLW` says, everything it
writes in `W` from byte 16 on, the data and the stack below `SP`, the saved
registers and kept values from 128 to 192 and the tag length and the
additional data's address at 224 and 232 as they were, the lengths and data
left at 192, 200 and 208, and the lengths block at 96. -/
structure OpenRunL (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (Ctx W SP D : Addr) (R n : Nat) (s₂ s' : State) : Prop where
  rg : ∀ x, (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Contains x 1 →
    s'.mem x = (openLW Lb Ctx R W D n x).getD (s₂.mem x)
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, n⟩, below SP 24] s₂.mem s'.mem
  kept : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
    s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64
  tlen : s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16))
  lens96 : s'.mem.readW (W + BitVec.ofNat 64 96) 64 =
    byteRev64 (BitVec.ofNat 64 (8 * (s₂.mem.readW (W + BitVec.ofNat 64 184) 64).toNat))
  lens104 : s'.mem.readW (W + BitVec.ofNat 64 104) 64 = byteRev64 (BitVec.ofNat 64 (8 * n))

/-- After the entry, `open`'s body for a tag length it allows, with
implementations of `vg_ghash` and `vg_aes_ctr32` that write none of their
working space and a `vg_aes_gcm_decrypt_blocks` that leaves `Lb` in its
`scratch`: what it leaves in `W` from byte 272 on (`openLW`), whether or not
the tags match. -/
theorem openRun_leaves (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code M) (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    {s₀ s₂ : State} {Ctx W SP Np A D T : Addr} {nl al n t : Nat} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (E : OneEntry s₀ Ctx W SP A D n s₂)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTr : Covers [⟨T, t⟩] (s₀.rd ++ s₀.wr)) (oT : OutWDS W D SP n ⟨T, t⟩)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (htl : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (.seq (oneAad (v.withBlk B)) (.seq (oneBlocks (v.withBlk B).dec) (.seq (oneTag (v.withBlk B) uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
      (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (oneUndo (v.withBlk B)) (oneCrypt (v.withBlk B)))
        (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))) s₂
      (OpenRunL Lb Ctx W SP D (s₀.gpr .rsi).toNat n s₂) := by
  have L := C.lay
  have hD := C.dE
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega_arith
  have hq : 16 * (n / 16) ≤ n := by omega_arith
  have hbp : s₂.gpr .rbp = BitVec.ofNat 64 nl := by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal' : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `[SP + 24]`, through frames in `W`, the data and the stack below `SP`.
  have oAr : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
      (∀ r ∈ rs, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 24)) →
      m'.readW (SP + BitVec.ofNat 64 24) 64 = m.readW (SP + BitVec.ofNat 64 24) 64 :=
    fun hf hs => hf.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => oA r (hs r hr))
      (by decide)
  have b24 : Region.Sub (below SP 8) (below SP 24) := below_sub (by decide) (by decide)
  -- `J₀` and the additional data.
  refine WP.seq (WP.mono (wp_both (oneMid_ok v C E hNp hnl hal) (oneAad_okF v L gf E.env rfl (E.r12.trans hNp) hbp
    (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr) E.aad hal')) fun s₃ ⟨Mi, fA, _⟩ => ?_)
  have kA : ∀ d, 112 ≤ d → d + 8 ≤ 2560 → (d + 8 ≤ 216 ∨ 224 ≤ d ∨ nl = 12) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ h₃ => fA.readW (Region.contains_self _ _) (disj_aadF L nl h₁ h₂ h₃) (by decide)
  have hRo : RoundsAt s₃.mem W R := hR ▸ Mi.rounds
  have hd₃ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₃ D n := C.data.of_eq Mi.rd Mi.wr
  have X₃ := X.keep Mi.rd Mi.wr Mi.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  have hob : ObPre M Ctx W SP R D n s₃ := ⟨Mi.env, hRo, Mi.dat, Mi.len, hd₃, C.t_c, C.t_w, C.t_d, C.sp24, X₃⟩
  -- The whole blocks.
  refine WP.seq (WP.mono (oneBlocksD_okL L B hL hob) fun s₄ ⟨P, hB⟩ => ?_)
  have kB : ∀ d, (112 ≤ d ∧ d + 8 ≤ 192) ∨ (216 ≤ d ∧ d + 8 ≤ 448) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => P.frame.readW (Region.contains_self _ _) (disj_obF L hD C.t_w h) (by decide)
  have hdw := (hd₃.of_eq P.rd P.wr).drop hq
  have hR₄ : RoundsAt s₄.mem W R := ⟨by rw [kB 176 (.inl ⟨by decide, by decide⟩)]; exact hRo.1, hRo.2⟩
  have hlen₄ : s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [P.len]; congr 1; omega_arith
  have h184 : s₄.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [kB 184 (.inl ⟨by decide, by decide⟩), kA 184 (by decide) (by decide) (.inl (by decide)), hal']
  -- The tag.
  refine WP.seq (WP.mono (oneTagU_okF L v gf cf (t := BitVec.ofNat 64 n) P.env rfl hR₄ P.dat hlen₄ P.tlen h184 hdw.ok)
    fun s₅ ⟨he₅, rd₅, wr₅, fT, l96, l104⟩ => ?_)
  have dT : ∀ {d k : Nat}, 128 ≤ d → d + k ≤ 2560 → ∀ r ∈ tagFU W SP,
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inr (by omega_arith)) h₂ (by decide)
    · exact (L.stk_w h₂).symm
  have kT : ∀ d, 128 ≤ d → d + 8 ≤ 2560 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fT.readW (Region.contains_self _ _) (dT h₁ h₂) (by decide)
  have htl₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [kT 224 (by decide) (by decide), kB 224 (.inr ⟨by decide, by decide⟩),
      kA 224 (by decide) (by decide) (.inr (.inl (by decide))), htl]
  have hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by
    rw [oAr fT (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inr (.inr b24)),
      oAr P.frame (fun r hr => by
        simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · rw [add_ofNat_assoc]; exact .inl (Lay.wSub (by decide))
        · rw [add_ofNat_assoc]; exact .inl (Lay.wSub (by decide))
        · exact .inr (.inl (Region.sub_prefix (by omega_arith)))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr (.inr fun _ h => h)),
      oAr fA (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by split <;> decide))
        · exact .inr (.inr b24)),
      oAr E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl (Lay.wSub (by decide))), hTa]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, P.rd, Mi.rd]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, P.wr, Mi.wr]
  -- The tag length and the received tag's address.
  have q₁ := he₅.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [rd₅', wr₅']; exact hTar
  obtain ⟨s₆, run₆, hbx₆, hsi₆, hg₆, hm₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s₅ = some s₆ ∧ s₆.gpr .rbx = BitVec.ofNat 64 t ∧ s₆.gpr .rsi = T ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by xrun [he₅.r15, he₅.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₅]
    · simp [gpr_setReg, he₅.rsp, hTa₅]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₆ _ (by decide) (by decide)) hrd₆ hwr₆
  -- The received tag, padded, and the comparison.
  refine WP.seq (WP.mono (WP.with_rdwr (recv_ok he₆ hbx₆ hb.1 hb.2 hsi₆
    (by rw [hrd₆, hwr₆, rd₅', wr₅']; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₇ ⟨⟨he₇, hr₇, f₇, hbx₇⟩, hrd₇, hwr₇⟩ => ?_)
  rw [hbx₆] at hbx₇
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L (by decide) (o := 112) (.inr rfl) he₇ hbx₇ hb.1 hb.2
    (length_bytesAt _ _ _) hr₇)) fun s₈ ⟨⟨he₈, hax₈, f₈⟩, hrd₈, hwr₈⟩ => ?_)
  obtain ⟨k, hk2, hax₈'⟩ : ∃ k, k < 2 ∧ s₈.gpr .rax = BitVec.ofNat 64 k := by
    rw [hax₈]; split
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
  -- The result kept at `W + 216`.
  have w₉ := he₈.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₉, run₉, hz₉, hg₉, hm₉, hrd₉, hwr₉⟩ : ∃ s₉, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₈ = some s₉ ∧ s₉.zf = some (decide (k = 0)) ∧ (∀ r, s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine ⟨_, by xrun [he₈.r15, w₉], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₈', mem_setReg]
      exact congrArg some (and_self_beq (by omega_arith))
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₈']
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => hg₉ r) hrd₉ hwr₉
  have f₉ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩] s₈.mem s₉.mem := by
    rw [hm₉]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₉ : s₉.rd = s₀.rd := by rw [hrd₉, hrd₈, hrd₇, hrd₆, rd₅']
  have wr₉ : s₉.wr = s₀.wr := by rw [hwr₉, hwr₈, hwr₇, hwr₆, wr₅']
  have dW1 : ∀ {a k d : Nat}, a + k ≤ d → d + 8 ≤ 2560 → a + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 a, k⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun h h₂ h₃ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr h) h₂ h₃
  have dW2 : ∀ {a k d : Nat}, d + 8 ≤ a → a + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 a, k⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun h h₃ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega_arith) h₃
  have k9' : ∀ d, 96 ≤ d → (d + 8 ≤ 216 ∨ (224 ≤ d ∧ d + 8 ≤ 240)) →
      s₉.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d _ h₂ => by
    have e₉ : s₉.mem.readW (W + BitVec.ofNat 64 d) 64 = s₈.mem.readW (W + BitVec.ofNat 64 d) 64 := by
      rcases h₂ with h₂ | h₂
      · exact f₉.readW (Region.contains_self _ _) (dW2 h₂ (by decide)) (by decide)
      · exact f₉.readW (Region.contains_self _ _) (dW1 h₂.1 (by omega_arith) (by decide)) (by decide)
    rw [e₉, f₈.readW (Region.contains_self _ _) (dW2 (by omega_arith) (by decide)) (by decide),
      f₇.readW (Region.contains_self _ _) (dW2 (by omega_arith) (by decide)) (by decide), hm₆]
  have k9 : ∀ d, 128 ≤ d → d + 8 ≤ 216 →
      s₉.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [k9' d (by omega_arith) (.inl h₂), kT d h₁ (by omega_arith)]
  have hR₉ : RoundsAt s₉.mem W R := ⟨by rw [k9 176 (by decide) (by decide)]; exact hR₄.1, hR₄.2⟩
  -- The rest decrypted, or the whole blocks encrypted again, and the result.
  have dRg : ∀ {a k : Nat}, a + k ≤ 272 →
      (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 a, k⟩ :=
    fun h => L.w_w (.inr h) (by decide) (by omega_arith)
  have FW : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 2560 → ∃ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, n⟩,
      below SP 24], Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r :=
    fun h₁ h₂ => ⟨_, List.mem_cons_self .., Offset.sub _ h₁ (by omega_arith)⟩
  have FD : ∀ {p : Addr} {k : Nat}, Region.Sub ⟨p, k⟩ ⟨D, n⟩ → ∃ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region),
      ⟨D, n⟩, below SP 24], Region.Sub ⟨p, k⟩ r := fun h => ⟨_, by simp, h⟩
  have FS : ∀ {k : Nat}, k ≤ 24 → ∃ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, n⟩,
      below SP 24], Region.Sub (below SP k) r := fun h => ⟨_, by simp, below_sub h (by decide)⟩
  have dS : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 240 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 16⟩ : Region),
      ⟨D, 16 * (n / 16)⟩, below SP 8], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by omega_arith))).symm
    · exact (L.stk_w (by omega_arith)).symm
  refine WP.seq (WP.mono (Q := fun s₁₀ : State => (Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₀ ∧
      ∀ x, (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Contains x 1 → s₁₀.mem x = s₉.mem x) ∧
      Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, n⟩, below SP 24] s₉.mem s₁₀.mem ∧
      ∀ d, 96 ≤ d → d + 8 ≤ 240 → s₁₀.mem.readW (W + BitVec.ofNat 64 d) 64 = s₉.mem.readW (W + BitVec.ofNat 64 d) 64)
    (WP.ite (decide (k = 0)) (eval_e hz₉) (fun _ => ?_) (fun _ => ?_)) fun s₁₀ ⟨⟨he₁₀, hm₁₀⟩, F₁₀, K₁₀⟩ => ?_)
  · refine WP.mono (oneUndo_okF L v cf he₉ hR₉ (by rw [k9 192 (by decide) (by decide)]; exact P.tlen)
      (by rw [k9 200 (by decide) (by decide)]; exact P.dat) (C.data.of_eq rd₉ wr₉)) fun s' ⟨he', _, _, f'⟩ =>
      ⟨⟨he', fun x hx => frame_at f' (fun r hr => ?_) hx⟩, f'.sub fun r hr => ?_,
        fun d h₁ h₂ => f'.readW (Region.contains_self _ _) (dS h₁ h₂) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dRg (by decide)
      · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by decide))).symm
      · exact (L.stk_w (by decide)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact FW (by decide) (by decide)
      · exact FD (Region.sub_prefix hq)
      · exact FS (by decide)
  · refine WP.mono (oneCrypt_okF v L cf (icb := 0) (P := 0) rfl he₉ hR₉
      (by rw [k9 200 (by decide) (by decide)]; exact P.dat) (by rw [k9 208 (by decide) (by decide)]; exact hlen₄)
      (hdw.of_eq (by rw [rd₉, P.rd, Mi.rd]) (by rw [wr₉, P.wr, Mi.wr])))
      fun s' ⟨⟨co, _, _⟩, f'⟩ =>
      ⟨⟨co.env, fun x hx => frame_at f' (disj_crF L hdw.ok.w (d := 272) (k := 2288) (by decide) (by decide)) hx⟩,
        f'.sub fun r hr => ?_,
        fun d h₁ h₂ => f'.readW (Region.contains_self _ _) (disj_crF L hdw.ok.w (by omega_arith) (by omega_arith))
          (by decide)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact FD (Offset.sub_base D (by omega_arith))
    · rw [add_ofNat_assoc]; exact FW (by decide) (by decide)
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact FS (by decide)
  · have q₁₁ := he₁₀.perm.wR (show 216 + 8 ≤ 2560 by decide)
    refine WP.run (Q := fun s₁₁ => s₁₁.mem = s₁₀.mem)
      ⟨_, by xrun [he₁₀.r15, q₁₁], by rfl⟩ fun s₁₁ hm₁₁ => ?_
    -- The slots from 96 to 240 but the result, from `s₅`, and from 128 from `s₄`.
    have k11' : ∀ d, 96 ≤ d → (d + 8 ≤ 216 ∨ (224 ≤ d ∧ d + 8 ≤ 240)) →
        s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [hm₁₁, K₁₀ d h₁ (by omega_arith), k9' d h₁ h₂]
    have k11 : ∀ d, 128 ≤ d → (d + 8 ≤ 216 ∨ (224 ≤ d ∧ d + 8 ≤ 240)) →
        s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [k11' d (by omega_arith) h₂, kT d h₁ (by omega_arith)]
    refine ⟨fun x hx => ?_, ?_, fun d h => ?_, by rw [k11 192 (by decide) (.inl (by decide))]; exact P.tlen,
      by rw [k11 200 (by decide) (.inl (by decide))]; exact P.dat,
      by rw [k11 208 (by decide) (.inl (by decide))]; exact hlen₄,
      by rw [k11' 96 (by decide) (.inl (by decide)), l96, hal'],
      by rw [k11' 104 (by decide) (.inl (by decide)), l104, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd₃.ok.lt]⟩
    · have e₈ : s₉.mem x = s₄.mem x := by
        rw [frame_at f₉ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRg (by decide)) hx,
          frame_at f₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRg (by decide)) hx,
          frame_at f₇ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRg (by decide)) hx, hm₆,
          frame_at fT (dT (d := 272) (k := 2288) (by decide) (by decide)) hx]
      rw [hm₁₁, hm₁₀ x hx, e₈]
      simp only [openLW]
      rcases rg_split hx with ⟨hs, h448⟩ | ⟨hs, h448⟩
      · rw [hB x hs, frame_at fA (disj_aadF L nl (d := 448) (k := 2112) (by decide) (by decide) (.inr (.inl (by decide)))) hs]
        by_cases hz : n / 16 = 0
        · simp only [hz, true_or, ↓reduceIte]
        · simp only [hz, h448, or_self, ↓reduceIte, false_or]
      · rw [frame_at P.frame (disj_obF L hD C.t_w (d := 272) (k := 176) (.inr ⟨by decide, by decide⟩)) hs,
          frame_at fA (disj_aadF L nl (d := 272) (k := 176) (by decide) (by decide) (.inr (.inl (by decide)))) hs]
        simp only [h448, or_true, ↓reduceIte, Option.getD_none]
    · -- What is written.
      rw [hm₁₁]
      refine ((((((fA.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)).trans (fT.sub fun r hr => ?_)).trans
        (hm₆ ▸ f₇.sub fun r hr => ?_)).trans (f₈.sub fun r hr => ?_)).trans (f₉.sub fun r hr => ?_)).trans F₁₀
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact FW (by decide) (by decide)
        · exact FW (by decide) (by split <;> decide)
        · exact FS (by decide)
      · simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact FW (by decide) (by decide)
        · rw [add_ofNat_assoc]; exact FW (by decide) (by decide)
        · rw [add_ofNat_assoc]; exact FW (by decide) (by decide)
        · exact FD (Region.sub_prefix (by omega_arith))
        · exact FW (by decide) (by decide)
        · exact FS (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact FW (by decide) (by decide)
        · exact FS (by decide)
      all_goals (simp only [List.mem_singleton] at hr; subst hr; exact FW (by decide) (by decide))
    · -- The saved registers and the kept values.
      rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [k11 d h₁ (.inl (by omega_arith)), kB d (.inl ⟨by omega_arith, h₂⟩),
          kA d (by omega_arith) (by omega_arith) (.inl (by omega_arith))]
      · rw [k11 d (by omega_arith) (.inr ⟨h₁, h₂⟩), kB d (.inr ⟨by omega_arith, by omega_arith⟩),
          kA d (by omega_arith) (by omega_arith) (.inr (.inl h₁))]

/-! ## The path for TLS records -/

/-- A region `W + d`, `k` bytes, from byte 272 on that the path for TLS
records (`FastOpen.run`) leaves as `open` does: apart from `G` (`W + 512`, 32
bytes) and the keystream `K` (`W + 1024`, 64 bytes), which only that path
writes. -/
def RunOk (d k : Nat) : Prop := 272 ≤ d ∧ d + k ≤ 2560 ∧ (d + k ≤ 512 ∨ (544 ≤ d ∧ d + k ≤ 1024) ∨ 1088 ≤ d)

/-- What the path for TLS records leaves, from `s₂` (after the entry) to
`s'`: what `OpenRunL` says, but in `W` from byte 272 on only where `RunOk`
says, and without the lengths block. -/
structure OpenRunLF (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (Ctx W SP D : Addr) (R n : Nat) (s₂ s' : State) : Prop where
  rg : ∀ {d k : Nat}, RunOk d k → ∀ x, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
    s'.mem x = (openLW Lb Ctx R W D n x).getD (s₂.mem x)
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, n⟩, below SP 24] s₂.mem s'.mem
  kept : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
    s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64
  tlen : s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16))

theorem RunOk.sub {W : Addr} {d k : Nat} (h : RunOk d k) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ ⟨W + BitVec.ofNat 64 272, 2288⟩ :=
  Offset.sub W h.1 (by have := h.2.1; omega_arith)

theorem OpenRunL.toF {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {Ctx W SP D : Addr} {R n : Nat} {s₂ s' : State} (h : OpenRunL Lb Ctx W SP D R n s₂ s') :
    OpenRunLF Lb Ctx W SP D R n s₂ s' :=
  ⟨fun hk x hx => h.rg x (hk.sub x hx), h.frame, h.kept, h.tlen, h.dat, h.len⟩

open Short (ShortFacts KsOk) in
/-- After the entry, the path for TLS records (`FastOpen.run`), with an
implementation of `vg_aes_ctr32` that writes none of its working space and
a `vg_aes_gcm_decrypt_blocks` that leaves `Lb` in its `scratch`: what it
leaves in `W` from byte 272 on (`openLW`) but in `G` and `K`, whether or not
the tags match. -/
theorem fastRun_leaves (hF : ShortFacts) (v : GcmImpl) {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}
    (B : BlkFn (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn))
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn)) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    {ks : Prog isa} (hks : KsOk ks)
    {s₀ s₂ : State} {Ctx W SP Np A D T : Addr} {al n t : Nat} (C : OneCtx s₀ 5 Ctx W SP Np A D 12 al n)
    (X : CtxExt (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (E : OneEntry s₀ Ctx W SP A D n s₂)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = 12) (hal : (s₀.gpr .r9).toNat = al) (h16 : al ≤ 16)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTr : Covers [⟨T, t⟩] (s₀.rd ++ s₀.wr)) (oT : OutWDS W D SP n ⟨T, t⟩)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (htl : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (hok : Spec.Gcm.tagLenOk t = true) :
    WP isa (FastOpen.run (v.withBlk B) ks) s₂ (OpenRunLF Lb Ctx W SP D (s₀.gpr .rsi).toNat n s₂) := by
  have L := C.lay
  have hD := C.dE
  have hlt := C.data.ok.lt
  unfold FastOpen.run
  have hAM := Fast.aad_midF hF C X E hNp hnl hal h16
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega_arith
  have hq : 16 * (n / 16) ≤ n := by omega_arith
  have hal' : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `[SP + 24]`, through frames in `W`, the data and the stack below `SP`.
  have oAr : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
      (∀ r ∈ rs, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 24)) →
      m'.readW (SP + BitVec.ofNat 64 24) 64 = m.readW (SP + BitVec.ofNat 64 24) 64 :=
    fun hf hs => hf.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => oA r (hs r hr))
      (by decide)
  -- The regions the tag writes.
  have dTP : ∀ {d k : Nat}, 128 ≤ d → d + k ≤ 2560 → (d + k ≤ 512 ∨ (544 ≤ d ∧ d + k ≤ 1024) ∨ 1088 ≤ d) →
      ∀ r ∈ FastOpen.tagPFrame W, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ h₃ r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by omega_arith) h₂ (by decide)
    · exact (L.st_w (a := 12) (n := 4) (by decide) (.inr ⟨by omega_arith, h₂⟩)).symm
    · exact L.w_w (.inr (by omega_arith)) h₂ (by decide)
    · exact L.w_w (by omega_arith) h₂ (by decide)
  -- `J₀` and the additional data.
  refine WP.seq (WP.mono hAM fun s₃ ⟨Mi, fA⟩ => ?_)
  have dA : ∀ {d k : Nat}, 112 ≤ d → d + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 96⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega_arith)) h₂ (by decide)
  have kA : ∀ d, 112 ≤ d → d + 8 ≤ 2560 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fA.readW (Region.contains_self _ _) (dA h₁ h₂) (by decide)
  have hRo : RoundsAt s₃.mem W R := hR ▸ Mi.rounds
  have hd₃ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₃ D n := C.data.of_eq Mi.rd Mi.wr
  have X₃ := X.keep Mi.rd Mi.wr Mi.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  have hob : ObPre (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn) Ctx W SP R D n s₃ :=
    ⟨Mi.env, hRo, Mi.dat, Mi.len, hd₃, C.t_c, C.t_w, C.t_d, C.sp24, X₃⟩
  -- The whole blocks.
  refine WP.seq (WP.mono (oneBlocksD_okL L B hL hob) fun s₄ ⟨P, hB⟩ => ?_)
  have kB : ∀ d, (112 ≤ d ∧ d + 8 ≤ 192) ∨ (216 ≤ d ∧ d + 8 ≤ 448) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => P.frame.readW (Region.contains_self _ _) (disj_obF L hD C.t_w h) (by decide)
  have hdw := (hd₃.of_eq P.rd P.wr).drop hq
  have hR₄ : RoundsAt s₄.mem W R := ⟨by rw [kB 176 (.inl ⟨by decide, by decide⟩)]; exact hRo.1, hRo.2⟩
  have hlen₄ : s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [P.len]; congr 1; omega_arith
  have h184 : s₄.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [kB 184 (.inl ⟨by decide, by decide⟩), kA 184 (by decide) (by decide), hal']
  have X₄ := X₃.keep P.rd P.wr P.frame fun r hr => by
    simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact X₃.cw.sub_right (Lay.wSub (by decide))
    · rw [add_ofNat_assoc]; exact X₃.cw.sub_right (Lay.wSub (by decide))
    · rw [add_ofNat_assoc]; exact X₃.cw.sub_right (Lay.wSub (by decide))
    · exact X₃.cd.sub_right (Region.sub_prefix (by omega_arith))
    · exact X₃.cw.sub_right (Lay.wSub (by decide))
    · exact X₃.ct.symm
  -- The tag.
  refine WP.seq (WP.mono (FastOpen.tagP_okPF hF hks L (N := n) (rfl : ([] : List Byte).length % 16 = 0) P.env rfl hR₄
    P.dat hlen₄ (by omega_arith) P.tlen (by omega_arith) h184 hdw.ok hdw.ok.w X₄.ctxOk)
    fun s₅ ⟨⟨⟨he₅, _, rd₅, wr₅, _⟩, hK₅⟩, fT⟩ => ?_)
  have kT : ∀ d, 128 ≤ d → d + 8 ≤ 512 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fT.readW (Region.contains_self _ _) (dTP h₁ (by omega_arith) (.inl h₂)) (by decide)
  have htl₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [kT 224 (by decide) (by decide), kB 224 (.inr ⟨by decide, by decide⟩), kA 224 (by decide) (by decide), htl]
  have b24 : Region.Sub (below SP 8) (below SP 24) := below_sub (by decide) (by decide)
  have hTa₅ : s₅.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by
    rw [oAr fT (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · rw [add_ofNat_assoc]; exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))),
      oAr P.frame (fun r hr => by
        simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · rw [add_ofNat_assoc]; exact .inl (Lay.wSub (by decide))
        · rw [add_ofNat_assoc]; exact .inl (Lay.wSub (by decide))
        · exact .inr (.inl (Region.sub_prefix (by omega_arith)))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr (.inr fun _ h => h)),
      oAr fA (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl (Lay.wSub (by decide))),
      oAr E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl (Lay.wSub (by decide))), hTa]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, P.rd, Mi.rd]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, P.wr, Mi.wr]
  -- The tag length and the received tag's address.
  have q₁ := he₅.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [rd₅', wr₅']; exact hTar
  obtain ⟨s₆, run₆, hbx₆, hsi₆, hg₆, hm₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s₅ = some s₆ ∧ s₆.gpr .rbx = BitVec.ofNat 64 t ∧ s₆.gpr .rsi = T ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by xrun [he₅.r15, he₅.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₅]
    · simp [gpr_setReg, he₅.rsp, hTa₅]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₆ _ (by decide) (by decide)) hrd₆ hwr₆
  -- The received tag, padded, and the comparison.
  refine WP.seq (WP.mono (WP.with_rdwr (recv_ok he₆ hbx₆ hb.1 hb.2 hsi₆
    (by rw [hrd₆, hwr₆, rd₅', wr₅']; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₇ ⟨⟨he₇, hr₇, f₇, hbx₇⟩, hrd₇, hwr₇⟩ => ?_)
  rw [hbx₆] at hbx₇
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L (by decide) (o := 112) (.inr rfl) he₇ hbx₇ hb.1 hb.2
    (length_bytesAt _ _ _) hr₇)) fun s₈ ⟨⟨he₈, hax₈, f₈⟩, hrd₈, hwr₈⟩ => ?_)
  obtain ⟨k, hk2, hax₈'⟩ : ∃ k, k < 2 ∧ s₈.gpr .rax = BitVec.ofNat 64 k := by
    rw [hax₈]; split
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
  -- The result kept at `W + 216`.
  have w₉ := he₈.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₉, run₉, hz₉, hg₉, hm₉, hrd₉, hwr₉⟩ : ∃ s₉, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₈ = some s₉ ∧ s₉.zf = some (decide (k = 0)) ∧ (∀ r, s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine ⟨_, by xrun [he₈.r15, w₉], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₈', mem_setReg]
      exact congrArg some (and_self_beq (by omega_arith))
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₈']
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => hg₉ r) hrd₉ hwr₉
  have f₉ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩] s₈.mem s₉.mem := by
    rw [hm₉]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₉ : s₉.rd = s₀.rd := by rw [hrd₉, hrd₈, hrd₇, hrd₆, rd₅']
  have wr₉ : s₉.wr = s₀.wr := by rw [hwr₉, hwr₈, hwr₇, hwr₆, wr₅']
  have dW1 : ∀ {a k d : Nat}, a + k ≤ d → d + 8 ≤ 2560 → a + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 a, k⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun h h₂ h₃ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr h) h₂ h₃
  have dW2 : ∀ {a k d : Nat}, d + 8 ≤ a → a + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 a, k⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun h h₃ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega_arith) h₃
  have k9 : ∀ d, 128 ≤ d → d + 8 ≤ 216 →
      s₉.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [f₉.readW (Region.contains_self _ _) (dW2 h₂ (by decide)) (by decide),
      f₈.readW (Region.contains_self _ _) (dW2 (by omega_arith) (by decide)) (by decide),
      f₇.readW (Region.contains_self _ _) (dW2 (by omega_arith) (by decide)) (by decide), hm₆,
      kT d h₁ (by omega_arith)]
  have k9' : ∀ d, 224 ≤ d → d + 8 ≤ 240 →
      s₉.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [f₉.readW (Region.contains_self _ _) (dW1 (by omega_arith) (by omega_arith) (by decide)) (by decide),
      f₈.readW (Region.contains_self _ _) (dW2 (by omega_arith) (by decide)) (by decide),
      f₇.readW (Region.contains_self _ _) (dW2 (by omega_arith) (by decide)) (by decide), hm₆,
      kT d (by omega_arith) (by omega_arith)]
  have hR₉ : RoundsAt s₉.mem W R := ⟨by rw [k9 176 (by decide) (by decide)]; exact hR₄.1, hR₄.2⟩
  -- `K[1]` kept since the tag.
  have hK₉ : FastOpen.KOk Ctx W R s₉ := by
    have f₅₉ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩]
        s₅.mem s₉.mem :=
      (((by rw [← hm₆]; exact f₇ : Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s₅.mem s₇.mem).sub fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩).trans
        (f₈.sub fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩)).trans
        (f₉.sub fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩)
    exact FastOpen.pStable_kOk L hR₄.2 f₅₉ hK₅
  -- The rest decrypted, or the whole blocks encrypted again, and the result.
  have dRg : ∀ {a k : Nat}, a + k ≤ 272 →
      (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 a, k⟩ :=
    fun h => L.w_w (.inr h) (by decide) (by omega_arith)
  have FW : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 2560 → ∃ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, n⟩,
      below SP 24], Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r :=
    fun h₁ h₂ => ⟨_, List.mem_cons_self .., Offset.sub _ h₁ (by omega_arith)⟩
  have FD : ∀ {p : Addr} {k : Nat}, Region.Sub ⟨p, k⟩ ⟨D, n⟩ → ∃ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region),
      ⟨D, n⟩, below SP 24], Region.Sub ⟨p, k⟩ r := fun h => ⟨_, by simp, h⟩
  have FS : ∀ {k : Nat}, k ≤ 24 → ∃ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, n⟩,
      below SP 24], Region.Sub (below SP k) r := fun h => ⟨_, by simp, below_sub h (by decide)⟩
  have dS : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 240 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 16⟩ : Region),
      ⟨D, 16 * (n / 16)⟩, below SP 8], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by omega_arith))).symm
    · exact (L.stk_w (by omega_arith)).symm
  have dK : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hdw.ok.w.sub_right (Lay.wSub h)).symm
  refine WP.seq (WP.mono (Q := fun s₁₀ : State => (Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₀ ∧
      ∀ x, (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Contains x 1 → s₁₀.mem x = s₉.mem x) ∧
      Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, n⟩, below SP 24] s₉.mem s₁₀.mem ∧
      ∀ d, 96 ≤ d → d + 8 ≤ 240 → s₁₀.mem.readW (W + BitVec.ofNat 64 d) 64 = s₉.mem.readW (W + BitVec.ofNat 64 d) 64)
    (WP.ite (decide (k = 0)) (eval_e hz₉) (fun _ => ?_) (fun _ => ?_)) fun s₁₀ ⟨⟨he₁₀, hm₁₀⟩, F₁₀, K₁₀⟩ => ?_)
  · refine WP.mono (oneUndo_okF L v cf he₉ hR₉ (by rw [k9 192 (by decide) (by decide)]; exact P.tlen)
      (by rw [k9 200 (by decide) (by decide)]; exact P.dat) (C.data.of_eq rd₉ wr₉)) fun s' ⟨he', _, _, f'⟩ =>
      ⟨⟨he', fun x hx => frame_at f' (fun r hr => ?_) hx⟩, f'.sub fun r hr => ?_,
        fun d h₁ h₂ => f'.readW (Region.contains_self _ _) (dS h₁ h₂) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dRg (by decide)
      · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by decide))).symm
      · exact (L.stk_w (by decide)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact FW (by decide) (by decide)
      · exact FD (Region.sub_prefix hq)
      · exact FS (by decide)
  · refine WP.mono (FastOpen.tailK_okF (icb := 0) (P₀ := 0) rfl (by omega_arith) he₉
      (by rw [k9 200 (by decide) (by decide)]; exact P.dat) (by rw [k9 208 (by decide) (by decide)]; exact hlen₄)
      (hdw.of_eq (by rw [rd₉, P.rd, Mi.rd]) (by rw [wr₉, P.wr, Mi.wr])) hK₉)
      fun s' ⟨he', f', _, _, _⟩ =>
      ⟨⟨he', fun x hx => frame_at f' (dK (by decide)) hx⟩,
        f'.sub fun r hr => ?_,
        fun d h₁ h₂ => f'.readW (Region.contains_self _ _) (dK (by omega_arith)) (by decide)⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact FD (Offset.sub_base D (by omega_arith))
  · have q₁₁ := he₁₀.perm.wR (show 216 + 8 ≤ 2560 by decide)
    refine WP.run (Q := fun s₁₁ => s₁₁.mem = s₁₀.mem)
      ⟨_, by xrun [he₁₀.r15, q₁₁], by rfl⟩ fun s₁₁ hm₁₁ => ?_
    have k11 : ∀ d, 128 ≤ d → (d + 8 ≤ 216 ∨ (224 ≤ d ∧ d + 8 ≤ 240)) →
        s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [hm₁₁, K₁₀ d (by omega_arith) (by omega_arith)]
      rcases h₂ with h₂ | h₂
      · exact k9 d h₁ h₂
      · exact k9' d h₂.1 h₂.2
    refine ⟨fun {d k} hk x hx => ?_, ?_, fun d h => ?_, by rw [k11 192 (by decide) (.inl (by decide))]; exact P.tlen,
      by rw [k11 200 (by decide) (.inl (by decide))]; exact P.dat,
      by rw [k11 208 (by decide) (.inl (by decide))]; exact hlen₄⟩
    · have hx' := hk.sub x hx
      have e₈ : s₉.mem x = s₄.mem x := by
        rw [frame_at f₉ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRg (by decide)) hx',
          frame_at f₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRg (by decide)) hx',
          frame_at f₇ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dRg (by decide)) hx', hm₆,
          frame_at fT (dTP (by have := hk.1; omega_arith) hk.2.1 hk.2.2) hx]
      rw [hm₁₁, hm₁₀ x hx', e₈]
      simp only [openLW]
      rcases rg_split hx' with ⟨hs, h448⟩ | ⟨hs, h448⟩
      · rw [hB x hs, frame_at fA (dA (d := 448) (k := 2112) (by decide) (by decide)) hs]
        by_cases hz : n / 16 = 0
        · simp only [hz, true_or, ↓reduceIte]
        · simp only [hz, h448, or_self, ↓reduceIte, false_or]
      · rw [frame_at P.frame (disj_obF L hD C.t_w (d := 272) (k := 176) (.inr ⟨by decide, by decide⟩)) hs,
          frame_at fA (dA (d := 272) (k := 176) (by decide) (by decide)) hs]
        simp only [h448, or_true, ↓reduceIte, Option.getD_none]
    · -- What is written.
      rw [hm₁₁]
      refine ((((((fA.sub fun r hr => ?_).trans (P.frame.sub fun r hr => ?_)).trans (fT.sub fun r hr => ?_)).trans
        (hm₆ ▸ f₇.sub fun r hr => ?_)).trans (f₈.sub fun r hr => ?_)).trans (f₉.sub fun r hr => ?_)).trans F₁₀
      · simp only [List.mem_singleton] at hr; subst hr; exact FW (by decide) (by decide)
      · simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact FW (by decide) (by decide)
        · rw [add_ofNat_assoc]; exact FW (by decide) (by decide)
        · rw [add_ofNat_assoc]; exact FW (by decide) (by decide)
        · exact FD (Region.sub_prefix (by omega_arith))
        · exact FW (by decide) (by decide)
        · exact FS (by decide)
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact FW (by decide) (by decide)
        · rw [add_ofNat_assoc]; exact FW (by decide) (by decide)
        · exact FW (by decide) (by decide)
        · exact FW (by decide) (by decide)
      all_goals (simp only [List.mem_singleton] at hr; subst hr; exact FW (by decide) (by decide))
    · -- The saved registers and the kept values.
      rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [k11 d h₁ (.inl (by omega_arith)), kB d (.inl ⟨by omega_arith, h₂⟩), kA d (by omega_arith) (by omega_arith)]
      · rw [k11 d (by omega_arith) (.inr ⟨h₁, h₂⟩), kB d (.inr ⟨by omega_arith, by omega_arith⟩),
          kA d (by omega_arith) (by omega_arith)]

/-! ## What `open` leaves -/

/-- `openEntry_ok`, and what the entry writes: `entryFrame` and the tag
length's slot. -/
theorem openEntry_okF {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s 5 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .r8 = A)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W) :
    WP isa (.block (oneEntry 40 ++ ([.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx] : List Instr))) s
      fun s₁ => OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = stackArg s 3 ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s 3 ∧
        Frame (entryFrame W ++ [⟨W + BitVec.ofNat 64 224, 8⟩]) s.mem s₁.mem := by
  have L := C.lay
  have a₄ := C.args 4 (by decide)
  refine WP.block_append (WP.mono (oneEntry_okL (by decide) C hCtx hSP hA hD hn hW a₄) fun s₁ ⟨E, fE⟩ => ?_)
  have a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [E.rd, E.wr]; exact C.args 3 (by omega_arith)
  have ht : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = stackArg s 3 := by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hs : Region.Sub ⟨SP + BitVec.ofNat 64 32, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 5⟩ := by
        rw [show (32 : Nat) = 8 + 24 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    rfl
  have w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 32)),
      .store (at_ .r15 tlO) .rbx] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 3 ∧ (∀ r, r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 3) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [E.rsp, E.env.r15, a₃, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, ht]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, ht]
    all_goals rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₂, run₂, E.keep L (fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hrd₂ hwr₂ f₂, hbx₂,
    by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  exact (fE.mono fun r hr => List.mem_append_left _ hr).trans (f₂.mono fun r hr => List.mem_append_right _ hr)

/-- `openSkel_ok`, with `E` of the memory for a tag length `tagLenOk` does
not allow too. -/
theorem openSkelL_ok {entry : List Instr} {mid : Prog isa} {s : State}
    {Ctx W SP Np A D : Addr} {nl al n t : Nat} (C : OneCtx s 5 Ctx W SP Np A D nl al n) (hSP : s.gpr .rsp = SP)
    (ht : t < 2 ^ 64) {E : Mem → Prop} {Res : State → Prop}
    (hRes : ∀ s₁ s₂ : State, Res s₁ → s₂.gpr .rax = s₁.gpr .rax → s₂.mem = s₁.mem → Res s₂)
    (hentry : WP isa (.block entry) s fun s₁ =>
      OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ E s₁.mem)
    (hbad : Spec.Gcm.tagLenOk t = false → ∀ s₅ : State, s₅.gpr .rax = 0 → E s₅.mem → Res s₅)
    (hmid : ∀ s₂, OneEntry s Ctx W SP A D n s₂ → E s₂.mem → Spec.Gcm.tagLenOk t = true →
      WP isa mid s₂ fun s₅ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ ∧ SavedAt s₅.mem W s ∧
        s₅.mem.readW SP 64 = s.mem.readW SP 64 ∧ Res s₅) :
    WP isa (.seq (.block entry) (.seq tagLenOk (.seq (.ite .e (.block [.mov32 .rax (imm 0)]) mid) (.block restore)))) s
      fun s' => Res s' := by
  have L := C.lay
  refine WP.seq (WP.mono hentry fun s₁ ⟨E₁, hbx₁, hE₁⟩ => ?_)
  refine WP.seq (WP.mono (tagLenOk_ok s₁ hbx₁ ht) fun s₂ ⟨hz₂, k₂⟩ => ?_)
  have E₂ : OneEntry s Ctx W SP A D n s₂ := E₁.keep L (fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k₂.rd k₂.wr (by rw [k₂.mem]; exact Frame.refl _ _)
  have hE₂ : E s₂.mem := by rw [k₂.mem]; exact hE₁
  have dR : ∀ r ∈ [oneR W], (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ ∧ SavedAt s₅.mem W s ∧
      s₅.mem.readW SP 64 = s.mem.readW SP 64 ∧ Res s₅)
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₂) (fun hbad' => ?_) (fun hok => ?_)) fun s₅ h₅ => ?_)
  · have hbad'' : Spec.Gcm.tagLenOk t = false := by simpa using hbad'
    refine WP.run (Q := fun s₅ => s₅.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₅.gpr r = s₂.gpr r) ∧ s₅.mem = s₂.mem ∧
        s₅.rd = s₂.rd ∧ s₅.wr = s₂.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₅ ⟨hax, hg₅, hm₅, hrd₅, hwr₅⟩ => ?_
    refine ⟨E₂.env.keep (fun r hr => hg₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅, by rw [hm₅]; exact E₂.saved, ?_,
      hbad hbad'' s₅ hax (by rw [hm₅]; exact hE₂)⟩
    rw [hm₅, ret_kept E₂.frame dR]
  · exact hmid s₂ E₂ hE₂ (by simpa using hok)
  obtain ⟨he₅, hsv₅, hret₅, hres⟩ := h₅
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret₅]))
    fun s' ⟨_, hm, hax⟩ => hRes _ _ hres hax hm

/-- What `open` leaves at `x` in `work` (`W = a 4`) from byte 272 on, of its
argument registers `g` and stack arguments `a`, with a
`vg_aes_gcm_decrypt_blocks` that leaves `Lb` in its `scratch`: for a tag
length it allows (`a 3`), what `openLW` says, and otherwise nothing
written. -/
def openL (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (x : Addr) : Option (BitVec 8) :=
  if Spec.Gcm.tagLenOk (a 3).toNat = true then openLW Lb (g .rdi) (g .rsi).toNat (a 4) (a 0) (a 1).toNat x
  else none

/-- The words of `work` (word `j` the 8 bytes from `8 j`) whose bytes
`OpenL` states, from 96 to 240: the lengths block (12, 13), the saved
registers and kept values (16 to 26), the tag length (28) and the
additional data's address (29). -/
def OpenJ (j : Nat) : Prop := j = 12 ∨ j = 13 ∨ (16 ≤ j ∧ j < 27) ∨ j = 28 ∨ j = 29

/-- Word `j` of `work` that `open` leaves (`OpenJ`), of its argument
registers `g` and stack arguments `a`, if it writes it: for a tag length it
allows (`a 3`) the lengths block (12, 13); the saved registers (16 to 21),
`rounds` (22), `aad_len` (23), and, for a tag length it allows, `len` (24)
and the address and length of the data after the whole blocks (25, 26), or
else the data's (25) and `len` (26); the tag length (28) and the additional
data's address (29). -/
def openWord (g : Reg → BitVec 64) (a : Nat → BitVec 64) (j : Nat) : Option (BitVec 64) :=
  match j with
  | 12 => if Spec.Gcm.tagLenOk (a 3).toNat = true then some (byteRev64 (BitVec.ofNat 64 (8 * (g .r9).toNat)))
      else none
  | 13 => if Spec.Gcm.tagLenOk (a 3).toNat = true then some (byteRev64 (BitVec.ofNat 64 (8 * (a 1).toNat)))
      else none
  | 16 => some (g .rbx)
  | 17 => some (g .rbp)
  | 18 => some (g .r12)
  | 19 => some (g .r13)
  | 20 => some (g .r14)
  | 21 => some (g .r15)
  | 22 => some (g .rsi)
  | 23 => some (g .r9)
  | 24 => if Spec.Gcm.tagLenOk (a 3).toNat = true then some (a 1) else none
  | 25 => if Spec.Gcm.tagLenOk (a 3).toNat = true then some (a 0 + BitVec.ofNat 64 (16 * ((a 1).toNat / 16)))
      else some (a 0)
  | 26 => if Spec.Gcm.tagLenOk (a 3).toNat = true then
      some (BitVec.ofNat 64 ((a 1).toNat - 16 * ((a 1).toNat / 16))) else some (a 1)
  | 28 => some (a 3)
  | 29 => some (g .r8)
  | _ => none

/-- What `open` leaves, from `s` to `s'`: in `work` from byte 272 on as
`openL` says, its first 16 bytes, its return address and its stack
arguments as they were, the words `openWord` gives (`OpenJ`), and elsewhere
among them what was there. -/
structure OpenL (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (s s' : State) : Prop where
  rg : ∀ x, (⟨stackArg s 4 + BitVec.ofNat 64 272, 2288⟩ : Region).Contains x 1 →
    s'.mem x = (openL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)
  w0 : ∀ x, (⟨stackArg s 4, 16⟩ : Region).Contains x 1 → s'.mem x = s.mem x
  args : ∀ x, (⟨s.gpr .rsp, 48⟩ : Region).Contains x 1 → s'.mem x = s.mem x
  words : ∀ j, OpenJ j → ∀ w, openWord s.gpr (fun i => stackArg s i) j = some w →
    s'.mem.readW (stackArg s 4 + BitVec.ofNat 64 (8 * j)) 64 = w
  rest : ∀ d, OpenJ (d / 8) → openWord s.gpr (fun i => stackArg s i) (d / 8) = none →
    s'.mem (stackArg s 4 + BitVec.ofNat 64 d) = s.mem (stackArg s 4 + BitVec.ofNat 64 d)

/-- The cases of `OpenJ`. -/
theorem OpenJ.cases {j : Nat} (h : OpenJ j) : j = 12 ∨ j = 13 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨
    j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 28 ∨ j = 29 := by
  unfold OpenJ at h; omega_arith

/-- The return address and the stack arguments: the first 8 bytes, or the
40 after them. -/
theorem retArgs_split {SP x : Addr} (hx : (⟨SP, 48⟩ : Region).Contains x 1) :
    (⟨SP, 8⟩ : Region).Contains x 1 ∨ (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Contains x 1 := by
  by_cases h8 : (x - SP).toNat < 8
  · exact .inl (by simp only [Region.Contains] at hx ⊢; omega_using [h8])
  · refine .inr ?_
    have := (Offset.lt_iff x SP (d := 8) (n := 40) (by decide)).2
      ⟨by omega_arith, by simp only [Region.Contains] at hx; omega_using [hx]⟩
    simp only [Region.Contains]; omega_using [this]

/-- `vg_aes_gcm_open`, for a key context of kind `M`, with implementations of
`vg_ghash` and `vg_aes_ctr32` that never touch their working space and a
`vg_aes_gcm_decrypt_blocks` that leaves `Lb` in its `scratch`: what it leaves
(`OpenL`). -/
theorem openM_leaves_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code M) (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    {s : State} (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa («open» (v.withBlk B)) s (OpenL Lb s) := by
  have X := CtxExt.ofOpen hp.1 hp.2
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp.1 M.ge
  have L := C.lay
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hTar := C.args 2 (by decide)
  have hst : stackArg s 3 = BitVec.ofNat 64 (stackArg s 3).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : stackArg s 1 = BitVec.ofNat 64 (stackArg s 1).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hsi : s.gpr .rsi = BitVec.ofNat 64 (s.gpr .rsi).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have oT : OutWDS (stackArg s 4) (stackArg s 0) (s.gpr .rsp) (stackArg s 1).toNat
      ⟨stackArg s 2, (stackArg s 3).toNat⟩ := fun r hr =>
    hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have oA : OutWDS (stackArg s 4) (stackArg s 0) (s.gpr .rsp) (stackArg s 1).toNat
      ⟨s.gpr .rsp + BitVec.ofNat 64 24, 8⟩ := fun r hr => arg24_disj (by decide) C.dA C.dAD hr
  -- What the entry writes.
  let EF : List Region := entryFrame (stackArg s 4) ++ [⟨stackArg s 4 + BitVec.ofNat 64 224, 8⟩]
  have eW : ∀ {d k : Nat}, ((d + k ≤ 128) ∨ (192 ≤ d ∧ d + k ≤ 200) ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) →
      ∀ r ∈ EF, (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [EF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl <;> exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  have sW : ∀ r ∈ EF, r.Sub ⟨stackArg s 4, 2560⟩ := fun r hr => by
    simp only [EF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide)
  have eA : ∀ r ∈ EF, (⟨s.gpr .rsp, 48⟩ : Region).Disjoint r := fun r hr x hx hr' => by
    rcases retArgs_split hx with h | h
    · exact C.rW x h (sW r hr x hr')
    · exact C.dA x h (sW r hr x hr')
  have w0E : ∀ m : Mem, Frame EF s.mem m → ∀ x, (⟨stackArg s 4, 16⟩ : Region).Contains x 1 → m x = s.mem x :=
    fun m f x hx => frame_at f (fun r hr => by
      have := eW (d := 0) (k := 16) (.inl (by decide)) r hr; simpa using this) hx
  -- The bytes of word `j` from those of `work`.
  have rdW : ∀ {m : Mem} {d : Nat} (hd : d < 2560), Frame EF s.mem m → (d + 1 ≤ 128) →
      m (stackArg s 4 + BitVec.ofNat 64 d) = s.mem (stackArg s 4 + BitVec.ofNat 64 d) := fun {m d} hd f h =>
    frame_at f (eW (d := d) (k := 1) (.inl h)) (Region.contains_self _ _)
  refine openSkelL_ok (t := (stackArg s 3).toNat)
    (E := fun m => m.readW (stackArg s 4 + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 (stackArg s 3).toNat ∧
      Frame EF s.mem m ∧ SavedAt m (stackArg s 4) s ∧ m.readW (stackArg s 4 + BitVec.ofNat 64 176) 64 = s.gpr .rsi ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 184) 64 = s.gpr .r9 ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 200) 64 = stackArg s 0 ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 208) 64 = stackArg s 1 ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 232) 64 = s.gpr .r8)
    (Res := OpenL Lb s) C rfl (stackArg s 3).isLt
    (fun s₁ s₂ h _ hm => ⟨fun x hx => by rw [hm]; exact h.rg x hx, fun x hx => by rw [hm]; exact h.w0 x hx,
      fun x hx => by rw [hm]; exact h.args x hx, fun j h₁ w hw => by rw [hm]; exact h.words j h₁ w hw,
      fun d h₁ hn => by rw [hm]; exact h.rest d h₁ hn⟩) ?_ ?_ ?_
  · exact WP.mono (openEntry_okF C rfl rfl rfl rfl rfl hW') fun s₁ ⟨E, hbx₁, htl₁, fE⟩ =>
      ⟨E, by rw [hbx₁, ← hst], by rw [htl₁, ← hst], fE, E.saved, by rw [E.rounds.1, ← hsi], E.alen, E.dat,
        by rw [E.len, ← hn1], E.aad⟩
  · -- A length `tagLenOk` does not allow: what the entry wrote.
    intro hbad s₅ _ ⟨htl, fE, hsv, h176, h184, h200, h208, h232⟩
    refine ⟨fun x hx => ?_, w0E _ fE, fun x hx => frame_at fE eA hx, fun j hj w hw => ?_, fun d hj hn => ?_⟩
    · simp only [openL, hbad, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
      exact frame_at fE (eW (d := 272) (k := 2288) (.inr (.inr (.inr ⟨by decide, by decide⟩)))) hx
    · rcases hj.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [openWord, hbad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, reduceCtorEq] at hw ⊢ <;>
        subst hw
      · exact hsv (.rbx, 128) (by simp [saved])
      · exact hsv (.rbp, 136) (by simp [saved])
      · exact hsv (.r12, 144) (by simp [saved])
      · exact hsv (.r13, 152) (by simp [saved])
      · exact hsv (.r14, 160) (by simp [saved])
      · exact hsv (.r15, 168) (by simp [saved])
      · exact h176
      · exact h184
      · exact h200
      · exact h208
      · rw [htl, ← hst]
      · exact h232
    · have hj' := hj.cases
      have h24 : d / 8 = 12 ∨ d / 8 = 13 ∨ d / 8 = 24 := by
        rcases hj' with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          rw [e] at hn <;> simp only [openWord, hbad, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hn <;>
          omega_arith
      rcases h24 with e | e | e
      · exact rdW (by omega_arith) fE (by omega_arith)
      · exact rdW (by omega_arith) fE (by omega_arith)
      · exact frame_at fE (eW (d := d) (k := 1) (.inr (.inl ⟨by omega_arith, by omega_arith⟩)))
          (Region.contains_self _ _)
  · intro s₂ E₂ ⟨htl₂, fE₂, _, h176, h184, _, _, _⟩ hok
    refine WP.mono (wp_both (openOk_ok v B C X E₂ rfl rfl rfl hTa hTar hTr oT oA htl₂ hok)
      (openRun_leaves v B hL gf cf C X E₂ rfl rfl rfl hTa hTar hTr oT oA htl₂ hok))
      fun s₅ ⟨⟨he₅, hsv₅, hret₅, _⟩, R⟩ => ⟨he₅, hsv₅, hret₅, ?_⟩
    have dR : ∀ {X : Region}, (∀ r : Region, r.Sub ⟨stackArg s 4, 2560⟩ ∨ r.Sub ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∨
        r.Sub (below (s.gpr .rsp) 24) → X.Disjoint r) →
        ∀ r ∈ [(⟨stackArg s 4 + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
          below (s.gpr .rsp) 24], X.Disjoint r := fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h _ (.inl (Lay.wSub (by decide)))
      · exact h _ (.inr (.inl fun _ h => h))
      · exact h _ (.inr (.inr fun _ h => h))
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun j hj w hw => ?_, fun d hj hn => ?_⟩
    · rw [R.rg x hx, frame_at fE₂ (eW (d := 272) (k := 2288) (.inr (.inr (.inr ⟨by decide, by decide⟩)))) hx]
      simp only [openL, hok, ↓reduceIte]
    · rw [frame_at R.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (Offset.disjoint_base (stackArg s 4) (d := 16) (n := 2544) (k := 16) (by decide)
            (by have := L.ww; omega_arith)).symm
        · exact (C.dE.sub_right (Region.sub_prefix (by decide))).symm
        · exact (C.t_w.sub_right (Region.sub_prefix (by decide))).symm) hx, w0E _ fE₂ x hx]
    · rw [frame_at R.frame (dR fun r hr y hy hr' => by
        rcases retArgs_split hy with h | h
        · rcases hr with hr | hr | hr
          · exact C.rW y h (hr y hr')
          · exact C.rD y h (hr y hr')
          · exact Offset.base_disjoint_below _ (n := 24) (k := 8) (by decide) y h (hr y hr')
        · rcases hr with hr | hr | hr
          · exact C.dA y h (hr y hr')
          · exact C.dAD y h (hr y hr')
          · exact Offset.disjoint_below _ (n := 24) (d := 8) (k := 40) (by decide) y h (hr y hr')) hx,
        frame_at fE₂ eA hx]
    · rcases hj.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [openWord, hok, ↓reduceIte, Option.some.injEq] at hw ⊢ <;> subst hw
      · rw [R.lens96, h184]
      · rw [R.lens104]
      · exact hsv₅ (.rbx, 128) (by simp [saved])
      · exact hsv₅ (.rbp, 136) (by simp [saved])
      · exact hsv₅ (.r12, 144) (by simp [saved])
      · exact hsv₅ (.r13, 152) (by simp [saved])
      · exact hsv₅ (.r14, 160) (by simp [saved])
      · exact hsv₅ (.r15, 168) (by simp [saved])
      · rw [R.kept 176 (.inl ⟨by decide, by decide⟩)]; exact h176
      · rw [R.kept 184 (.inl ⟨by decide, by decide⟩)]; exact h184
      · rw [R.tlen, ← hn1]
      · exact R.dat
      · exact R.len
      · rw [R.kept 224 (.inr ⟨by decide, by decide⟩), htl₂, ← hst]
      · rw [R.kept 232 (.inr ⟨by decide, by decide⟩)]; exact E₂.aad
    · exfalso
      rcases hj.cases with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
        rw [e] at hn <;> simp only [openWord, hok, ↓reduceIte, reduceCtorEq] at hn

/-- `vg_aes_gcm_open`, for a key context of kind `M`, with implementations of
`vg_ghash` and `vg_aes_ctr32` that never touch their working space and a
`vg_aes_gcm_decrypt_blocks` that leaves a function of its arguments in its
`scratch` (`BlkLeavesD`): what it leaves (`OpenL`), byte by byte a function
of its argument registers and stack arguments, or what was there. -/
theorem open_leaves (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (hB : BlkLeavesD B)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.openX86_64M M).pre s → Exec isa («open» (v.withBlk B)) s t s' → OpenL Lb s s' := by
  obtain ⟨Lb, hL⟩ := hB
  refine ⟨Lb, fun s t s' hp he => ?_⟩
  obtain ⟨_, s'', he', h⟩ := openM_leaves_wp v B hL gf cf hp
  obtain ⟨_, rfl⟩ := Exec.det he he'
  exact h

/-- The bytes `OpenL` says what `open` leaves in: the 48 bytes of its return
address and stack arguments at `A`, the first 16 bytes of `work` at `W`, its
words of `OpenJ` (from 96 to 112, 128 to 216 and 224 to 240), and `work`
from byte 272 on. -/
def openQ (A W x : Addr) : Prop :=
  (⟨A, 48⟩ : Region).Contains x 1 ∨ (⟨W, 16⟩ : Region).Contains x 1 ∨
    (⟨W + BitVec.ofNat 64 96, 16⟩ : Region).Contains x 1 ∨ (⟨W + BitVec.ofNat 64 128, 88⟩ : Region).Contains x 1 ∨
    (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains x 1 ∨ (⟨W + BitVec.ofNat 64 272, 2288⟩ : Region).Contains x 1

/-- What `open` leaves at `x` there: at `A` what `hdr` says, and in `work`
(`W`) nothing written in its first 96 bytes, the bytes of `openWord` up to
240, and from 272 on what `openL` says. -/
def openV (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (hdr : Addr → Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64)
    (A W x : Addr) : Option (BitVec 8) :=
  if (⟨A, 48⟩ : Region).Contains x 1 then hdr x
  else if (x - W).toNat < 96 then none
  else if (x - W).toNat < 240 then
    (openWord g a ((x - W).toNat / 8)).map fun w => w.extractLsb' (8 * ((x - W).toNat % 8)) 8
  else openL Lb g a x

/-- `OpenL`, byte by byte (`openV`), for a return address and stack
arguments apart from `work`. -/
theorem OpenL.all {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {s s' : State} (h : OpenL Lb s s')
    (hAW : (⟨s.gpr .rsp, 48⟩ : Region).Disjoint ⟨stackArg s 4, 2560⟩)
    (ww : (stackArg s 4).toNat + 2560 ≤ 2 ^ 64) :
    ∀ x, openQ (s.gpr .rsp) (stackArg s 4) x →
      s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) (stackArg s 4) x).getD
        (s.mem x) := by
  intro x hx
  -- A byte of `work` at offset `d`.
  have inW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
      ¬ (⟨s.gpr .rsp, 48⟩ : Region).Contains x 1 ∧
        d ≤ (x - stackArg s 4).toNat ∧ (x - stackArg s 4).toNat < d + k := fun {d k} hk hc => by
    have hlt : (x - (stackArg s 4 + BitVec.ofNat 64 d)).toNat < k := by
      simp only [Region.Contains] at hc; omega_using [hc]
    refine ⟨fun hA => hAW x hA (Offset.sub_base _ hk x hc), (Offset.lt_iff x _ (by omega_using [ww, hk])).1 hlt⟩
  -- A byte of a word of `OpenJ`.
  have word : ∀ {d k : Nat}, d + k ≤ 240 → 96 ≤ d →
      (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
      (∀ i, d ≤ i → i < d + k → OpenJ (i / 8)) →
      s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) (stackArg s 4) x).getD
        (s.mem x) := fun {d k} hk h96 hc hJ => by
    obtain ⟨hA, h₁, h₂⟩ := inW (d := d) (k := k) (by omega_arith) hc
    generalize hd : (x - stackArg s 4).toNat = i at h₁ h₂
    have ex : x = stackArg s 4 + BitVec.ofNat 64 i := by
      rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have hj := hJ i h₁ h₂
    simp only [openV, hA, ↓reduceIte, hd, show ¬ i < 96 by omega_arith, show i < 240 by omega_arith]
    cases hw : openWord s.gpr (fun i => stackArg s i) (i / 8) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      rw [ex]; exact h.rest i hj hw
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      rw [ex, ← Offset.add_add_eq (stackArg s 4) (show 8 * (i / 8) + i % 8 = i by omega_arith),
        Blocks.byte_readW64 s'.mem (stackArg s 4 + BitVec.ofNat 64 (8 * (i / 8))) (j := i % 8) (by omega_arith),
        h.words (i / 8) hj w hw]
  rcases hx with hx | hx | hx | hx | hx | hx
  · simp only [openV, hx, ↓reduceIte, Option.getD_none]; exact h.args x hx
  · obtain ⟨hA, -, h16⟩ := inW (d := 0) (k := 16) (by decide) (by simpa using hx)
    simp only [openV, hA, ↓reduceIte, show (x - stackArg s 4).toNat < 96 by omega_arith, Option.getD_none]
    exact h.w0 x hx
  · exact word (d := 96) (k := 16) (by decide) (by decide) hx fun i h₁ h₂ => by unfold OpenJ; omega_arith
  · exact word (d := 128) (k := 88) (by decide) (by decide) hx fun i h₁ h₂ => by unfold OpenJ; omega_arith
  · exact word (d := 224) (k := 16) (by decide) (by decide) hx fun i h₁ h₂ => by unfold OpenJ; omega_arith
  · obtain ⟨hA, h₁, -⟩ := inW (d := 272) (k := 2288) (by decide) hx
    simp only [openV, hA, ↓reduceIte, show ¬ (x - stackArg s 4).toNat < 96 by omega_arith,
      show ¬ (x - stackArg s 4).toNat < 240 by omega_arith]
    exact h.rg x hx

/-- `open_leaves`, byte by byte (`openV`). -/
theorem open_leavesQ (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (hB : BlkLeavesD B)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.openX86_64M M).pre s → Exec isa («open» (v.withBlk B)) s t s' →
        ∀ x, openQ (s.gpr .rsp) (stackArg s 4) x →
          s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp)
            (stackArg s 4) x).getD (s.mem x) := by
  obtain ⟨Lb, hL⟩ := open_leaves v B hB gf cf
  refine ⟨Lb, fun s t s' hp he => ?_⟩
  obtain ⟨C, -⟩ := OneCtx.ofOpen hp.1 M.ge
  refine (hL s t s' hp he).all (fun y hy hW => ?_) C.ww
  rcases retArgs_split hy with h | h
  · exact C.rW y h hW
  · exact C.dA y (by simpa using h) hW

/-! ## What `open` leaves with the path for TLS records -/

/-- The words of `work` whose bytes `OpenLF` states, from 128 to 240: those
of `OpenJ` but the lengths block. -/
def OpenJF (j : Nat) : Prop := (16 ≤ j ∧ j < 27) ∨ j = 28 ∨ j = 29

theorem OpenJF.cases {j : Nat} (h : OpenJF j) : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨
    j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 28 ∨ j = 29 := by
  unfold OpenJF at h; omega_arith

/-- What `open` with the path for TLS records leaves, from `s` to `s'`: what
`OpenL` says, but in `work` from byte 272 on only where `RunOk` says, and
without the lengths block. -/
structure OpenLF (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (s s' : State) : Prop where
  rg : ∀ {d k : Nat}, RunOk d k → ∀ x, (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
    s'.mem x = (openL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)
  w0 : ∀ x, (⟨stackArg s 4, 16⟩ : Region).Contains x 1 → s'.mem x = s.mem x
  args : ∀ x, (⟨s.gpr .rsp, 48⟩ : Region).Contains x 1 → s'.mem x = s.mem x
  words : ∀ j, OpenJF j → ∀ w, openWord s.gpr (fun i => stackArg s i) j = some w →
    s'.mem.readW (stackArg s 4 + BitVec.ofNat 64 (8 * j)) 64 = w
  rest : ∀ d, OpenJF (d / 8) → openWord s.gpr (fun i => stackArg s i) (d / 8) = none →
    s'.mem (stackArg s 4 + BitVec.ofNat 64 d) = s.mem (stackArg s 4 + BitVec.ofNat 64 d)

theorem OpenJF.toJ {j : Nat} (h : OpenJF j) : OpenJ j := by unfold OpenJF at h; unfold OpenJ; omega_arith

theorem OpenL.toF {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {s s' : State} (h : OpenL Lb s s') : OpenLF Lb s s' :=
  ⟨fun hk x hx => h.rg x (hk.sub x hx), h.w0, h.args, fun j hj => h.words j hj.toJ, fun d hj => h.rest d hj.toJ⟩

theorem OpenRunLF.of_mem {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {Ctx W SP D : Addr} {R n : Nat} {s₂ s₃ s' : State} (hm : s₃.mem = s₂.mem)
    (h : OpenRunLF Lb Ctx W SP D R n s₃ s') : OpenRunLF Lb Ctx W SP D R n s₂ s' :=
  ⟨fun hk x hx => by rw [← hm]; exact h.rg hk x hx, by rw [← hm]; exact h.frame,
    fun d hd => by rw [← hm]; exact h.kept d hd, h.tlen, h.dat, h.len⟩

open Short (ShortFacts) in
/-- `vg_aes_gcm_open` with the path for TLS records (`FastOpen.openFin` of
`FastOpen.sel`, the code of `vg_aes_gcm_open_prepared` without the short
path), for a prepared key context, with implementations of `vg_ghash` and
`vg_aes_ctr32` that never touch their working space and a
`vg_aes_gcm_decrypt_blocks` that leaves `Lb` in its `scratch`: what it leaves
(`OpenLF`). -/
theorem openFinM_leaves_wp (hF : ShortFacts) (v : GcmImpl) {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}
    (B : BlkFn (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn))
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.dec.code (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn)) (gf : GhashFree v.gh.fn.code)
    (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) {s : State}
    (hp : (Proof.AesGcm.openX86_64M (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn)).pre s) :
    WP isa (FastOpen.openFin (FastOpen.sel (v.withBlk B) (Short.openLong (v.withBlk B)) Short.finKsA true)) s
      (OpenLF Lb s) := by
  have X := CtxExt.ofOpen hp.1 hp.2
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp.1 (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn).ge
  have L := C.lay
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hTar := C.args 2 (by decide)
  have hst : stackArg s 3 = BitVec.ofNat 64 (stackArg s 3).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn1 : stackArg s 1 = BitVec.ofNat 64 (stackArg s 1).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hsi : s.gpr .rsi = BitVec.ofNat 64 (s.gpr .rsi).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have oT : OutWDS (stackArg s 4) (stackArg s 0) (s.gpr .rsp) (stackArg s 1).toNat
      ⟨stackArg s 2, (stackArg s 3).toNat⟩ := fun r hr =>
    hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have oA : OutWDS (stackArg s 4) (stackArg s 0) (s.gpr .rsp) (stackArg s 1).toNat
      ⟨s.gpr .rsp + BitVec.ofNat 64 24, 8⟩ := fun r hr => arg24_disj (by decide) C.dA C.dAD hr
  -- What the entry writes.
  let EF : List Region := entryFrame (stackArg s 4) ++ [⟨stackArg s 4 + BitVec.ofNat 64 224, 8⟩]
  have eW : ∀ {d k : Nat}, ((d + k ≤ 128) ∨ (192 ≤ d ∧ d + k ≤ 200) ∨ (216 ≤ d ∧ d + k ≤ 224) ∨ (240 ≤ d ∧ d + k ≤ 2560)) →
      ∀ r ∈ EF, (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [EF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl <;> exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  have sW : ∀ r ∈ EF, r.Sub ⟨stackArg s 4, 2560⟩ := fun r hr => by
    simp only [EF, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide)
  have eA : ∀ r ∈ EF, (⟨s.gpr .rsp, 48⟩ : Region).Disjoint r := fun r hr x hx hr' => by
    rcases retArgs_split hx with h | h
    · exact C.rW x h (sW r hr x hr')
    · exact C.dA x h (sW r hr x hr')
  have w0E : ∀ m : Mem, Frame EF s.mem m → ∀ x, (⟨stackArg s 4, 16⟩ : Region).Contains x 1 → m x = s.mem x :=
    fun m f x hx => frame_at f (fun r hr => by
      have := eW (d := 0) (k := 16) (.inl (by decide)) r hr; simpa using this) hx
  refine openSkelL_ok (t := (stackArg s 3).toNat)
    (E := fun m => m.readW (stackArg s 4 + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 (stackArg s 3).toNat ∧
      Frame EF s.mem m ∧ SavedAt m (stackArg s 4) s ∧ m.readW (stackArg s 4 + BitVec.ofNat 64 176) 64 = s.gpr .rsi ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 184) 64 = s.gpr .r9 ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 200) 64 = stackArg s 0 ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 208) 64 = stackArg s 1 ∧
      m.readW (stackArg s 4 + BitVec.ofNat 64 232) 64 = s.gpr .r8)
    (Res := OpenLF Lb s) C rfl (stackArg s 3).isLt
    (fun s₁ s₂ h _ hm => ⟨fun hk x hx => by rw [hm]; exact h.rg hk x hx, fun x hx => by rw [hm]; exact h.w0 x hx,
      fun x hx => by rw [hm]; exact h.args x hx, fun j h₁ w hw => by rw [hm]; exact h.words j h₁ w hw,
      fun d h₁ hn => by rw [hm]; exact h.rest d h₁ hn⟩) ?_ ?_ ?_
  · exact WP.mono (openEntry_okF C rfl rfl rfl rfl rfl hW') fun s₁ ⟨E, hbx₁, htl₁, fE⟩ =>
      ⟨E, by rw [hbx₁, ← hst], by rw [htl₁, ← hst], fE, E.saved, by rw [E.rounds.1, ← hsi], E.alen, E.dat,
        by rw [E.len, ← hn1], E.aad⟩
  · -- A length `tagLenOk` does not allow: what the entry wrote.
    intro hbad s₅ _ ⟨htl, fE, hsv, h176, h184, h200, h208, h232⟩
    refine ⟨fun {d k} hk x hx => ?_, w0E _ fE, fun x hx => frame_at fE eA hx, fun j hj w hw => ?_, fun d hj hn => ?_⟩
    · simp only [openL, hbad, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
      exact frame_at fE (eW (d := d) (k := k) (.inr (.inr (.inr ⟨by have := hk.1; omega_arith, hk.2.1⟩)))) hx
    · rcases hj.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [openWord, hbad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, reduceCtorEq] at hw ⊢ <;>
        subst hw
      · exact hsv (.rbx, 128) (by simp [saved])
      · exact hsv (.rbp, 136) (by simp [saved])
      · exact hsv (.r12, 144) (by simp [saved])
      · exact hsv (.r13, 152) (by simp [saved])
      · exact hsv (.r14, 160) (by simp [saved])
      · exact hsv (.r15, 168) (by simp [saved])
      · exact h176
      · exact h184
      · exact h200
      · exact h208
      · rw [htl, ← hst]
      · exact h232
    · have h24 : d / 8 = 24 := by
        rcases hj.cases with e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          rw [e] at hn <;> simp only [openWord, hbad, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hn <;>
          omega_arith
      exact frame_at fE (eW (d := d) (k := 1) (.inr (.inl ⟨by omega_arith, by omega_arith⟩)))
        (Region.contains_self _ _)
  · intro s₂ E₂ ⟨htl₂, fE₂, _, h176, h184, _, _, _⟩ hok
    -- The path for TLS records, or the other instances' body.
    unfold FastOpen.sel
    refine WP.seq (WP.mono (Fast.condE_ok (any := true) C E₂ rfl rfl) fun s₃ ⟨hz, E₃, K⟩ => ?_)
    have htl₃ : s₃.mem.readW (stackArg s 4 + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 (stackArg s 3).toNat := by
      rw [K.mem]; exact htl₂
    refine WP.mono (Q := fun s₅ : State => (Env (s.gpr .rdi) (stackArg s 4 + BitVec.ofNat 64 16) (stackArg s 4) (s.gpr .rsp) s₅ ∧
        SavedAt s₅.mem (stackArg s 4) s ∧ s₅.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64) ∧
        OpenRunLF Lb (s.gpr .rdi) (stackArg s 4) (s.gpr .rsp) (stackArg s 0) (s.gpr .rsi).toNat (stackArg s 1).toNat s₂ s₅)
      (WP.ite (decide ¬Fast.IsFast (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat true) (eval_e hz)
        (fun _ => WP.mono (wp_both (openOk_ok v B C X E₃ rfl rfl rfl hTa hTar hTr oT oA htl₃ hok)
          (openRun_leaves v B hL gf cf C X E₃ rfl rfl rfl hTa hTar hTr oT oA htl₃ hok))
          fun s₅ ⟨⟨he₅, hsv₅, hret₅, _⟩, R⟩ => ⟨⟨he₅, hsv₅, hret₅⟩, R.toF.of_mem K.mem⟩)
        fun h => ?_) fun s₅ ⟨⟨he₅, hsv₅, hret₅⟩, R⟩ => ⟨he₅, hsv₅, hret₅, ?_⟩
    · obtain ⟨h12, h17, -⟩ : Fast.IsFast (s.gpr .rcx).toNat (s.gpr .r9).toNat (stackArg s 1).toNat true :=
        Decidable.not_not.mp (of_decide_eq_false h)
      have C' : OneCtx s 5 (s.gpr .rdi) (stackArg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0) 12
          (s.gpr .r9).toNat (stackArg s 1).toNat := h12 ▸ C
      exact WP.mono (wp_both (openOkW_ok v B (FastOpen.tagP_okP hF Short.finKsA_ksOk) FastOpen.pStable_kOk
          FastOpen.crOk_tailK C' X rfl hTa hTar hTr oT oA htl₃ hok
          (Fast.aad_mid hF C' X E₃ rfl h12 rfl (by omega_arith)))
        (fastRun_leaves hF v B hL cf Short.finKsA_ksOk C' X E₃ rfl h12 rfl (by omega_arith) hTa hTar hTr oT oA htl₃
          hok))
        fun s₅ ⟨⟨he₅, hsv₅, hret₅, _⟩, R⟩ => ⟨⟨he₅, hsv₅, hret₅⟩, R.of_mem K.mem⟩
    refine ⟨fun {d k} hk x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun j hj w hw => ?_, fun d hj hn => ?_⟩
    · rw [R.rg hk x hx, frame_at fE₂ (eW (d := d) (k := k) (.inr (.inr (.inr ⟨by have := hk.1; omega_arith, hk.2.1⟩)))) hx]
      simp only [openL, hok, ↓reduceIte]
    · rw [frame_at R.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (Offset.disjoint_base (stackArg s 4) (d := 16) (n := 2544) (k := 16) (by decide)
            (by have := L.ww; omega_arith)).symm
        · exact (C.dE.sub_right (Region.sub_prefix (by decide))).symm
        · exact (C.t_w.sub_right (Region.sub_prefix (by decide))).symm) hx, w0E _ fE₂ x hx]
    · have dR : ∀ {X : Region}, (∀ r : Region, r.Sub ⟨stackArg s 4, 2560⟩ ∨ r.Sub ⟨stackArg s 0, (stackArg s 1).toNat⟩ ∨
          r.Sub (below (s.gpr .rsp) 24) → X.Disjoint r) →
          ∀ r ∈ [(⟨stackArg s 4 + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
            below (s.gpr .rsp) 24], X.Disjoint r := fun h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h _ (.inl (Lay.wSub (by decide)))
        · exact h _ (.inr (.inl fun _ h => h))
        · exact h _ (.inr (.inr fun _ h => h))
      rw [frame_at R.frame (dR fun r hr y hy hr' => by
        rcases retArgs_split hy with h | h
        · rcases hr with hr | hr | hr
          · exact C.rW y h (hr y hr')
          · exact C.rD y h (hr y hr')
          · exact Offset.base_disjoint_below _ (n := 24) (k := 8) (by decide) y h (hr y hr')
        · rcases hr with hr | hr | hr
          · exact C.dA y h (hr y hr')
          · exact C.dAD y h (hr y hr')
          · exact Offset.disjoint_below _ (n := 24) (d := 8) (k := 40) (by decide) y h (hr y hr')) hx,
        frame_at fE₂ eA hx]
    · rcases hj.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [openWord, hok, ↓reduceIte, Option.some.injEq] at hw ⊢ <;> subst hw
      · exact hsv₅ (.rbx, 128) (by simp [saved])
      · exact hsv₅ (.rbp, 136) (by simp [saved])
      · exact hsv₅ (.r12, 144) (by simp [saved])
      · exact hsv₅ (.r13, 152) (by simp [saved])
      · exact hsv₅ (.r14, 160) (by simp [saved])
      · exact hsv₅ (.r15, 168) (by simp [saved])
      · rw [R.kept 176 (.inl ⟨by decide, by decide⟩)]; exact h176
      · rw [R.kept 184 (.inl ⟨by decide, by decide⟩)]; exact h184
      · rw [R.tlen, ← hn1]
      · exact R.dat
      · exact R.len
      · rw [R.kept 224 (.inr ⟨by decide, by decide⟩), htl₂, ← hst]
      · rw [R.kept 232 (.inr ⟨by decide, by decide⟩)]; exact E₂.aad
    · exfalso
      rcases hj.cases with e | e | e | e | e | e | e | e | e | e | e | e | e <;>
        rw [e] at hn <;> simp only [openWord, hok, ↓reduceIte, reduceCtorEq] at hn

/-- The bytes `OpenLF` says what `open` leaves in: those of `openQ` but the
lengths block and, in `work` from byte 272 on, where `RunOk` says. -/
def openQF (A W x : Addr) : Prop :=
  (⟨A, 48⟩ : Region).Contains x 1 ∨ (⟨W, 16⟩ : Region).Contains x 1 ∨
    (⟨W + BitVec.ofNat 64 128, 88⟩ : Region).Contains x 1 ∨ (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains x 1 ∨
    (⟨W + BitVec.ofNat 64 272, 240⟩ : Region).Contains x 1 ∨ (⟨W + BitVec.ofNat 64 544, 480⟩ : Region).Contains x 1 ∨
    (⟨W + BitVec.ofNat 64 1088, 1472⟩ : Region).Contains x 1

theorem openQF_openQ {A W x : Addr} (h : openQF A W x) : openQ A W x := by
  unfold openQF at h
  unfold openQ
  rcases h with h | h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (RunOk.sub (d := 272) (k := 240) ⟨by decide, by decide, .inl (by decide)⟩ x h)))))
  · exact .inr (.inr (.inr (.inr (.inr (RunOk.sub (d := 544) (k := 480) ⟨by decide, by decide, .inr (.inl ⟨by decide, by decide⟩)⟩ x h)))))
  · exact .inr (.inr (.inr (.inr (.inr (RunOk.sub (d := 1088) (k := 1472) ⟨by decide, by decide, .inr (.inr (by decide))⟩ x h)))))

/-- `OpenLF`, byte by byte (`openV`), for a return address and stack
arguments apart from `work`. -/
theorem OpenLF.all {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {s s' : State} (h : OpenLF Lb s s')
    (hAW : (⟨s.gpr .rsp, 48⟩ : Region).Disjoint ⟨stackArg s 4, 2560⟩)
    (ww : (stackArg s 4).toNat + 2560 ≤ 2 ^ 64) :
    ∀ x, openQF (s.gpr .rsp) (stackArg s 4) x →
      s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) (stackArg s 4) x).getD
        (s.mem x) := by
  intro x hx
  -- A byte of `work` at offset `d`.
  have inW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
      ¬ (⟨s.gpr .rsp, 48⟩ : Region).Contains x 1 ∧
        d ≤ (x - stackArg s 4).toNat ∧ (x - stackArg s 4).toNat < d + k := fun {d k} hk hc => by
    have hlt : (x - (stackArg s 4 + BitVec.ofNat 64 d)).toNat < k := by
      simp only [Region.Contains] at hc; omega_using [hc]
    refine ⟨fun hA => hAW x hA (Offset.sub_base _ hk x hc), (Offset.lt_iff x _ (by omega_using [ww, hk])).1 hlt⟩
  -- A byte of a word of `OpenJF`.
  have word : ∀ {d k : Nat}, d + k ≤ 240 → 128 ≤ d →
      (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
      (∀ i, d ≤ i → i < d + k → OpenJF (i / 8)) →
      s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) (stackArg s 4) x).getD
        (s.mem x) := fun {d k} hk h96 hc hJ => by
    obtain ⟨hA, h₁, h₂⟩ := inW (d := d) (k := k) (by omega_arith) hc
    generalize hd : (x - stackArg s 4).toNat = i at h₁ h₂
    have ex : x = stackArg s 4 + BitVec.ofNat 64 i := by
      rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have hj := hJ i h₁ h₂
    simp only [openV, hA, ↓reduceIte, hd, show ¬ i < 96 by omega_arith, show i < 240 by omega_arith]
    cases hw : openWord s.gpr (fun i => stackArg s i) (i / 8) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      rw [ex]; exact h.rest i hj hw
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      rw [ex, ← Offset.add_add_eq (stackArg s 4) (show 8 * (i / 8) + i % 8 = i by omega_arith),
        Blocks.byte_readW64 s'.mem (stackArg s 4 + BitVec.ofNat 64 (8 * (i / 8))) (j := i % 8) (by omega_arith),
        h.words (i / 8) hj w hw]
  -- A byte from 272 on.
  have high : ∀ {d k : Nat}, RunOk d k → (⟨stackArg s 4 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1 →
      s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp) (stackArg s 4) x).getD
        (s.mem x) := fun {d k} hk hc => by
    obtain ⟨hA, h₁, -⟩ := inW (d := d) (k := k) hk.2.1 hc
    have := hk.1
    simp only [openV, hA, ↓reduceIte, show ¬ (x - stackArg s 4).toNat < 96 by omega_arith,
      show ¬ (x - stackArg s 4).toNat < 240 by omega_arith]
    exact h.rg hk x hc
  rcases hx with hx | hx | hx | hx | hx | hx | hx
  · simp only [openV, hx, ↓reduceIte, Option.getD_none]; exact h.args x hx
  · obtain ⟨hA, -, h16⟩ := inW (d := 0) (k := 16) (by decide) (by simpa using hx)
    simp only [openV, hA, ↓reduceIte, show (x - stackArg s 4).toNat < 96 by omega_arith, Option.getD_none]
    exact h.w0 x hx
  · exact word (d := 128) (k := 88) (by decide) (by decide) hx fun i h₁ h₂ => by unfold OpenJF; omega_arith
  · exact word (d := 224) (k := 16) (by decide) (by decide) hx fun i h₁ h₂ => by unfold OpenJF; omega_arith
  · exact high ⟨by decide, by decide, .inl (by decide)⟩ hx
  · exact high ⟨by decide, by decide, .inr (.inl ⟨by decide, by decide⟩)⟩ hx
  · exact high ⟨by decide, by decide, .inr (.inr (by decide))⟩ hx

open Short (ShortFacts) in
/-- `openFinM_leaves_wp`, byte by byte (`openV`), for a decrypting function
that leaves a function of its arguments in its `scratch`. -/
theorem openFin_leavesQ (hF : ShortFacts) (v : GcmImpl) {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}
    (B : BlkFn (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn)) (hB : BlkLeavesD B)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.openX86_64M (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn)).pre s →
        Exec isa (FastOpen.openFin (FastOpen.sel (v.withBlk B) (Short.openLong (v.withBlk B)) Short.finKsA true))
          s t s' →
        ∀ x, openQF (s.gpr .rsp) (stackArg s 4) x →
          s'.mem x = (openV Lb (fun _ => none) s.gpr (fun i => stackArg s i) (s.gpr .rsp)
            (stackArg s 4) x).getD (s.mem x) := by
  obtain ⟨Lb, hL⟩ := hB
  refine ⟨Lb, fun s t s' hp he => ?_⟩
  obtain ⟨_, s'', he', h⟩ := openFinM_leaves_wp hF v B hL gf cf hp
  obtain ⟨_, rfl⟩ := Exec.det he he'
  obtain ⟨C, -⟩ := OneCtx.ofOpen hp.1 (Gcm.X86_64.Stitch.CtxMode.preparedN np hpn).ge
  refine h.all (fun y hy hW => ?_) C.ww
  rcases retArgs_split hy with h | h
  · exact C.rW y h hW
  · exact C.dA y (by simpa using h) hW

/-- `openL` reads neither `rax` nor `rsp`, and no stack argument after the
fifth. -/
theorem openL_congr (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : ∀ i < 5, a i = a' i) :
    openL Lb g a = openL Lb g' a' := by
  funext x
  unfold openL
  rw [hg .rdi (by decide) (by decide), hg .rsi (by decide) (by decide), ha 0 (by decide), ha 1 (by decide),
    ha 3 (by decide), ha 4 (by decide)]

end VG.Proof.AesGcm.X86_64
