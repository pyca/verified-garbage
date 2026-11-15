module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
public import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
public import VerifiedGarbage.Proof.AesGcm.X86_64.J0
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on x86-64: what `vg_aes_gcm_seal` leaves in `work`

Untrusted: everything here is checked by Lean. With implementations of
`vg_aes_ctr32` and `vg_ghash` that never touch their working space, and a
`vg_aes_gcm_encrypt_blocks` that leaves in its `scratch` a function of its
arguments (`BlkLeaves`), `seal` leaves in `work` from byte 96 on a function
of its argument registers and stack arguments (`seal_leaves`): the lengths
block at 96, the saved registers and the arguments it keeps from 128 to 240,
the blocks function's `scratch` at 448, and elsewhere what was there. Each
piece's frame: the entry (`oneEntry_okL`), `J₀` and the additional data
(`oneAad_okF`), the whole blocks (`oneBlocksE_okL`), the rest of the data
(`oneCrypt_okF`) and the tag (`oneTag_okF`).
-/

-- separate module: its one importer imports `Instances`, and with it every proof of AES-GCM on x86-64; these generic proofs need no re-checking when one of those changes

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem sub_empty {a : Addr} {r : Region} : Region.Sub ⟨a, 0⟩ r := fun _ h => by
  simp only [Region.Contains] at h; omega_using [h]

/-! ## `J₀` and the additional data -/

/-- What `oneAad` writes, with `vg_ghash` writing none of its working space:
the state and `T` (`[16, 112)`), the nonce's length at `216` unless the nonce
has 12 bytes, and the stack. -/
abbrev aadF (W SP : Addr) (nl : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 96⟩, ⟨W + BitVec.ofNat 64 216, if nl = 12 then 0 else 8⟩, below SP 8]

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The slots from 112 on but `216` are apart from what `j0` writes. -/
theorem slot_j0 {d : Nat} (h₁ : 112 ≤ d) (h₂ : d + 8 ≤ 216 ∨ (224 ≤ d ∧ d + 8 ≤ 2560)) :
    ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP 0, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.sb.sub_right (Lay.bSub (by omega_arith) (by omega_arith))).symm
  · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.disj_empty
  · exact (L.stk_w (by omega_arith)).symm

/-- `oneAad`, with an implementation of `vg_ghash` that never touches its
working space: what it writes (`aadF`), and the nonce's length it keeps at
`216` unless the nonce has 12 bytes. -/
theorem oneAad_okF (gf : GhashFree v.gh.fn.code) {Np A : Addr} {nl al : Nat} {H : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (h12 : s.gpr .r12 = Np) (hbp : s.gpr .rbp = BitVec.ofNat 64 nl)
    (hN : DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) (hAd : DataOk (W + BitVec.ofNat 64 16) W SP s A al)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) :
    WP isa (oneAad v.callees) s fun s' => Frame (aadF W SP nl) s.mem s'.mem ∧
      (nl ≠ 12 → s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 nl) := by
  refine WP.seq (WP.mono (WP.with_rdwr (j0_okL v (G := GhFits.free v gf 2560) L ⟨he, hH, h12, hbp, hN⟩))
    fun s₁ ⟨⟨jo, j12, jn⟩, hrd₁, hwr₁⟩ => ?_)
  have he₁ := jo.env
  have q₁ := he₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he₁.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have k232 : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
    rw [jo.frame.readW (Region.contains_self _ _) (slot_j0 L (by decide) (.inr ⟨by decide, by decide⟩)) (by decide),
      haad]
  have k184 : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [jo.frame.readW (Region.contains_self _ _) (slot_j0 L (by decide) (.inl (by decide))) (by decide), hal]
  obtain ⟨s₂, run₂, h12₂, hbp₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)] s₁ = some s₂ ∧
      s₂.gpr .r12 = A ∧ s₂.gpr .rbp = BitVec.ofNat 64 al ∧ s₂.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he₁.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, k232]
    · simp [gpr_setReg, k184]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hai : AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 H [] A al s₂ :=
    ⟨he₂, h12₂, hbp₂, hbx₂, hAd.of_eq (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]), by rw [hm₂]; exact jo.hH⟩
  refine WP.mono (absorbPad_ok v (G := GhFits.free v gf 2560) L (yo := 16) (.inr rfl) hai rfl) fun s₅ hf => ?_
  obtain ⟨m₃, fa, ft⟩ := hf.frame
  have hS : ∀ {a k : Nat}, a + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a, k⟩ ⟨W + BitVec.ofNat 64 16, 96⟩ :=
    fun h => Offset.sub_base _ (by omega_arith)
  have gA : Frame (aadF W SP nl) s₂.mem s₅.mem := by
    refine (fa.sub fun r hr => ?_).trans (ft.sub fun r hr => ?_) <;>
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
  have d216 : ∀ r ∈ absFrame (W + BitVec.ofNat 64 16) W SP 16 0 ++ tFrame (W + BitVec.ofNat 64 16) W SP 16 0,
      (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Lay.disj_empty
    · exact (L.stk_w (by decide)).symm
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.disj_empty
    · exact (L.stk_w (by decide)).symm
  rw [hm₂] at gA
  refine ⟨Frame.trans ?_ gA, fun hn => ?_⟩
  · by_cases hn : nl = 12
    · refine (j12 hn).sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · refine jo.frame.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 216, if nl = 12 then 0 else 8⟩, by simp, by rw [ite_eq_right hn]; exact fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., sub_empty⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · rw [ft.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _)
      (fun r hr => d216 r (List.mem_append_right _ hr)) (by decide),
      fa.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _)
      (fun r hr => d216 r (List.mem_append_left _ hr)) (by decide), hm₂, jn hn]

end

/-- A byte of a region apart from a frame's regions is unchanged. -/
theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    {x : Addr} (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

/-! ## The whole blocks -/

/-- What a function `L` of the arguments of `vg_aes_gcm_encrypt_blocks` and of
its `scratch` says it leaves there (as `BlkLeaves`). -/
abbrev BlkLeft (L : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
    Option (BitVec 8)) (c : Prog isa) (M : Gcm.X86_64.Stitch.CtxMode) : Prop :=
  ∀ s t s', (Proof.AesGcm.encryptBlocksX86_64M M).pre s → Exec isa c s t s' →
    ∀ x, (⟨stackArg s 0, 2112⟩ : Region).Contains x 1 →
      s'.mem x = (L (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9)
        (stackArg s 0) x).getD (s.mem x)

/-- A call of `vg_aes_gcm_encrypt_blocks` that leaves `Lb` in its `scratch`. -/
theorem blkE_callL {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Lb : BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb B.enc.code M)
    {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall M s K C Y D S R q) :
    WP isa (.call B.enc.name B.enc.code) s fun s' => BlkPost s C Y D S q s' ∧
      ∀ x, (⟨S, 2112⟩ : Region).Contains x 1 →
        s'.mem x = (Lb K (BitVec.ofNat 64 R) C Y D (BitVec.ofNat 64 q) S x).getD (s.mem x) := by
  let k : Contract isa := ⟨(Proof.AesGcm.encryptBlocksX86_64M M).pre, fun s s' => ∀ x,
    (⟨stackArg s 0, 2112⟩ : Region).Contains x 1 → s'.mem x = (Lb (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx)
      (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) x).getD (s.mem x), Proof.AesGcm.blocksPub⟩
  refine WP.call (k := k) (fun s' hs => ?_) B.encNosp (by rw [B.encDepth]; decide)
    (rd := BlkCall.rd M s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  · obtain ⟨t, s'', e, ha, -⟩ := B.encOk s' hs
    exact ⟨t, s'', e, ha, hL s' t s'' hs e⟩
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [B.encDepth] at hf
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

/-- The frame of the call of `vg_aes_gcm_encrypt_blocks` that leaves `Lb` in
its `scratch`. -/
theorem obFrameE_okL {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Lb : BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb B.enc.code M)
    {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn M Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call B.enc.name B.enc.code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
        s₄.mem x = (Lb Ctx (BitVec.ofNat 64 R) (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 16) D
          (BitVec.ofNat 64 q) (W + BitVec.ofNat 64 448) x).getD (s.mem x) := by
  have hsp := h.env.rsp
  have hn8 : 8 * [Reg.rax].length ≤ (s.gpr .rsp).toNat := by rw [hsp]; have := h.sp24; simp; omega_arith
  obtain ⟨hfp, -⟩ := pushRegs_mem s [.rax] (by decide) hn8
  have hfp' : Frame [below SP 8] s.mem (pushed [.rax] s).mem := by rw [← hsp]; exact hfp
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (blkE_callL B hL (ObIn.call L h))
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

/-- `oneBlocks` of the encrypting function that leaves `Lb` in its
`scratch` at `W + 448`: there, if there was a whole block, what `Lb` says. -/
theorem oneBlocksE_okL {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Lb : BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)} (hL : BlkLeft Lb B.enc.code M)
    {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre M Ctx W SP R D n s) :
    WP isa (oneBlocks B.enc) s fun s' => ObPost Ctx W SP D n s s' ∧
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
        (BitVec.ofNat 64 (n / 16)) (W + BitVec.ofNat 64 448) x).getD (s.mem x)) (fun s₂ hz hi => WP.mono (obFrameE_okL L B hL hi) fun s₄ ⟨a, b, c, d, e⟩ =>
    ⟨a, b, c, d, fun x hx => by rw [ite_eq_right hz]; exact e x hx⟩) (fun hz s₁ m₁ x hx => ?_)
    (fun s₂ s₄ s₅ m₂ o f x hx => ?_)
  · rw [ite_eq_left hz, Option.getD_none, m₁, frame_at (f192 _) d192 hx]
  · rw [frame_at f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)) hx,
      o x hx, m₂, frame_at (f192 _) d192 hx]

end

/-! ## The rest of the data, and the tag -/

/-- A layout with `W` of 2560 bytes, with only its first 512. -/
theorem Lay.to512 {Ctx St W SP : Addr} (L : Lay Ctx St W SP) : Lay Ctx St W SP 512 :=
  ⟨L.cw, L.sw, by have := L.ww; omega_arith, L.cs, L.cw'.sub_right (Region.sub_prefix (by decide)), L.sa,
    L.sb.sub_right (Region.sub_prefix (by decide)), L.kc, L.ks, L.kw.sub_right (Region.sub_prefix (by decide)),
    by decide, by decide⟩

theorem Env.to512 {Ctx St W SP : Addr} {s : State} (h : Env Ctx St W SP s) : Env Ctx St W SP s 512 :=
  ⟨h.r13, h.r14, h.r15, h.rsp, ⟨h.perm.ctx, h.perm.st, covers_prefix h.perm.w (by decide)⟩⟩

theorem DataOk.to512 {St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DataOk St W SP s D n) :
    DataOk St W SP s D n 512 :=
  ⟨h.rd, h.lt, h.wrap, h.st, h.w.sub_right (Region.sub_prefix (by decide)), h.stk⟩

/-- What `oneTag 0` writes, with implementations of `vg_ghash` and
`vg_aes_ctr32` that write none of their working space: the first 112 bytes
of `W` and the stack. -/
abbrev tagF (W SP : Addr) : List Region := [⟨W, 112⟩, below SP 8]

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The slots from 112 to 512 are apart from what `absorb 16`, `flush 16` and
`lens 16` write, with no working space for `vg_ghash`. -/
theorem slot_abs16 {d : Nat} (h₁ : 112 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ absFrame (W + BitVec.ofNat 64 16) W SP 16 0 ++ tFrame (W + BitVec.ofNat 64 16) W SP 16 0,
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w (by omega_arith)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact Lay.disj_empty
  · exact (L.stk_w (by omega_arith)).symm

/-- `oneCrypt`, with an implementation of `vg_aes_ctr32` that never touches
its working space: `oneCrypt_ok`, and what it writes. -/
theorem oneCrypt_okF (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) {R : Nat} {icb : Block} {P : Nat}
    (hP : P % 16 = 0) {D : Addr} {n : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneCrypt v.callees) s fun s' => (CrOut Ctx (W + BitVec.ofNat 64 16) W SP R icb P D n s.mem s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr) ∧ Frame (crFrameS (W + BitVec.ofNat 64 16) W SP D n 0) s.mem s'.mem := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  simp only [oneCrypt, oneCryptG, oneCryptBlk, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 (P % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hdat]
    · simp [gpr_setReg, hlen]
    · simp [gpr_setReg, hP]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have := WP.with_rdwr (cryptAl_okP v L (CrCallP.free v cf) (R := R) (icb := icb) (P := P)
    ⟨he₁, h12, hbp, hbx, hd.of_eq hrd₁ hwr₁, by rw [hm₁]; exact hR⟩ hP)
  rw [hm₁] at this
  exact WP.mono this fun s' ⟨⟨o, f⟩, a, b⟩ => ⟨⟨o, a.trans hrd₁, b.trans hwr₁⟩, f⟩

/-- `oneTag 0`, with implementations of `vg_ghash` and `vg_aes_ctr32` that
never touch their working space: what it writes (`tagF`), and the lengths
block it leaves in `T`, of the lengths at `184` and `192`. -/
theorem oneTag_okF (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) {R : Nat}
    {D : Addr} {n : Nat} {a t : BitVec 64} {H : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = t) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = a)
    (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneTag v.callees 0) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame (tagF W SP) s.mem s'.mem ∧
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
    (o := 0) (.inl rfl) he₅.to512 hH₅ hR₅ rfl)) fun s₆ ⟨⟨ht, h96, h104⟩, hrd₆, hwr₆⟩ => ?_
  rw [hbx₅] at h96
  rw [hbp₅] at h104
  have hS : ∀ {d k : Nat}, d + k ≤ 80 →
      Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W, 112⟩ := fun {d k} h => by
    rw [add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨⟨ht.env.r13, ht.env.r14, ht.env.r15, ht.env.rsp, he₅.perm.of_eq hrd₆ hwr₆⟩,
    by rw [hrd₆, hrd₅, hrd₄, hrd₁], by rw [hwr₆, hwr₅, hwr₄, hwr₁], ?_, h96, h104⟩
  refine ((fa.sub fun r hr => ?_).trans (ft.sub fun r hr => ?_)).trans (hm₅ ▸ ht.frame.sub fun r hr => ?_) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using hS (d := 0) (k := 32) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_empty⟩
    · exact ⟨_, by simp, fun _ h => h⟩

end

/-! ## After the entry -/

/-- What `oneAad`, `oneBlocks`, `oneCrypt` and `oneTag 0` write, with
implementations of `vg_ghash` and `vg_aes_ctr32` that write none of their
working space: the first 112 bytes of `W`, the slots of the data's length,
data and length left (`[192, 216)`), the nonce's length unless it has 12
bytes, the blocks function's `scratch`, the data and the stack. -/
abbrev leftF (W SP D : Addr) (n nl : Nat) : List Region :=
  [⟨W, 112⟩, ⟨W + BitVec.ofNat 64 192, 24⟩, ⟨W + BitVec.ofNat 64 216, if nl = 12 then 0 else 8⟩,
    ⟨W + BitVec.ofNat 64 448, 2112⟩, ⟨D, n⟩, below SP 24]

/-- What `seal` leaves after its entry (`s₁`), up to the tag (`sealRun_leaves`). -/
structure SealLeft (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (s₀ s₁ : State) (Ctx W SP D : Addr) (R n nl : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (leftF W SP D n nl) s₁.mem s.mem
  w96 : s.mem.readW (W + BitVec.ofNat 64 96) 64 = byteRev64 (BitVec.ofNat 64 (8 * (s₀.gpr .r9).toNat))
  w104 : s.mem.readW (W + BitVec.ofNat 64 104) 64 = byteRev64 (BitVec.ofNat 64 (8 * (BitVec.ofNat 64 n).toNat))
  w192 : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  w200 : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))
  w208 : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n % 16)
  w216 : nl ≠ 12 → s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 nl
  blk : ∀ x, (⟨W + BitVec.ofNat 64 448, 2112⟩ : Region).Contains x 1 →
    s.mem x = (if n / 16 = 0 then none else Lb Ctx (BitVec.ofNat 64 R)
      (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) D
      (BitVec.ofNat 64 (n / 16)) (W + BitVec.ofNat 64 448) x).getD (s₁.mem x)

/-- Two postconditions of the same code from the same state: its run is
deterministic. -/
theorem wp_both {c : Prog isa} {s : State} {Q R : State → Prop} (h₁ : WP isa c s Q) (h₂ : WP isa c s R) :
    WP isa c s fun s' => Q s' ∧ R s' := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨_, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem disj_aadF (nl : Nat) {d k : Nat} (h₁ : 112 ≤ d) (h₂ : d + k ≤ 2560) (h₃ : d + k ≤ 216 ∨ 224 ≤ d ∨ nl = 12) :
    ∀ r ∈ aadF W SP nl, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (.inr (by omega_arith)) h₂ (by decide)
  · by_cases hn : nl = 12
    · rw [ite_eq_left hn]; exact Lay.disj_empty
    · rw [ite_eq_right hn]; exact L.w_w (by omega_arith) h₂ (by decide)
  · exact (L.stk_w h₂).symm

theorem disj_obF {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) {d k : Nat}
    (h : (112 ≤ d ∧ d + k ≤ 192) ∨ (216 ≤ d ∧ d + k ≤ 448)) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)),
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · rw [add_ofNat_assoc]; exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by omega_arith))).symm
  · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega_arith))).symm

theorem disj_crF {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {d k : Nat} (h₁ : 96 ≤ d)
    (h₂ : d + k ≤ 2560) : ∀ r ∈ crFrameS (W + BitVec.ofNat 64 16) W SP D n 0,
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hD.sub_right (Lay.wSub h₂)).symm
  · exact (L.st_w (by decide) (.inr ⟨h₁, h₂⟩)).symm
  · exact Lay.disj_empty
  · exact (L.stk_w h₂).symm

theorem disj_tagF {d k : Nat} (h₁ : 112 ≤ d) (h₂ : d + k ≤ 2560) :
    ∀ r ∈ tagF W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base W h₁ (by have := L.ww; omega_arith)
  · exact (L.stk_w h₂).symm

end

/-- After the entry, `seal` up to the tag, with implementations of
`vg_ghash` and `vg_aes_ctr32` that write none of their working space and a
`vg_aes_gcm_encrypt_blocks` that leaves `Lb` in its `scratch`: what it
writes and leaves in `W` (`SealLeft`). -/
theorem sealRun_leaves (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.enc.code M) (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa (.seq (oneAad v.callees) (.seq (oneBlocks B.enc) (.seq (oneCrypt v.callees) (oneTag v.callees 0))))
      s₁ (SealLeft Lb s₀ s₁ Ctx W SP D (s₀.gpr .rsi).toNat n nl) := by
  have L := C.lay
  have hD := C.dE
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hbp : s₁.gpr .rbp = BitVec.ofNat 64 nl := by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `J₀` and the additional data.
  refine WP.seq (WP.mono (wp_both (oneMid_ok v C E hNp hnl hal) (oneAad_okF v L gf E.env rfl (E.r12.trans hNp) hbp
    (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr) E.aad hal')) fun s₂ ⟨Mi, fA, h216⟩ => ?_)
  have hRo : RoundsAt s₂.mem W R := hR ▸ Mi.rounds
  have hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq Mi.rd Mi.wr
  have X₂ := X.keep Mi.rd Mi.wr Mi.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  have hob : ObPre M Ctx W SP R D n s₂ := ⟨Mi.env, hRo, Mi.dat, Mi.len, hd₂, C.t_c, C.t_w, C.t_d, C.sp24, X₂⟩
  -- The whole blocks.
  refine WP.seq (WP.mono (oneBlocksE_okL L B hL hob) fun s₃ ⟨P, hB⟩ => ?_)
  have kB : ∀ d, (112 ≤ d ∧ d + 8 ≤ 192) ∨ (216 ≤ d ∧ d + 8 ≤ 448) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => P.frame.readW (Region.contains_self _ _) (disj_obF L hD C.t_w h) (by decide)
  have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₃ (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (hd₂.of_eq P.rd P.wr).drop (by omega_arith)
  have hD' := hdw.ok.w
  have hR₃ : RoundsAt s₃.mem W R := ⟨by rw [kB 176 (.inl ⟨by decide, by decide⟩)]; exact hRo.1, hRo.2⟩
  have hlen₃ : s₃.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [P.len]; congr 1; omega_arith
  -- The rest of the data.
  refine WP.seq (WP.mono (oneCrypt_okF v L cf (icb := 0) (P := 0) rfl P.env hR₃ P.dat hlen₃ hdw)
    fun s₄ ⟨⟨co, rd₄, wr₄⟩, fC⟩ => ?_)
  have kC : ∀ d, 96 ≤ d → d + 8 ≤ 2560 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fC.readW (Region.contains_self _ _) (disj_crF L hD' h₁ h₂) (by decide)
  have h184 : s₄.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r9 := by
    rw [kC 184 (by decide) (by decide), kB 184 (.inl ⟨by decide, by decide⟩), fA.readW (Region.contains_self _ _)
      (disj_aadF L nl (by decide) (by decide) (.inl (by decide))) (by decide), E.alen]
  -- The tag.
  refine WP.mono (oneTag_okF v L gf cf (t := BitVec.ofNat 64 n) co.env rfl co.rounds (by rw [kC 200 (by decide) (by decide), P.dat])
    (by rw [kC 208 (by decide) (by decide)]; exact hlen₃) (by rw [kC 192 (by decide) (by decide)]; exact P.tlen) h184
    (hdw.ok.of_eq rd₄ wr₄)) fun s₅ ⟨he₅, rd₅, wr₅, fT, h96, h104⟩ => ?_
  have kT : ∀ d, 112 ≤ d → d + 8 ≤ 2560 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fT.readW (Region.contains_self _ _) (disj_tagF L h₁ h₂) (by decide)
  have kCT : ∀ d, 112 ≤ d → d + 8 ≤ 2560 →
      s₅.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => by rw [kT d h₁ h₂, kC d (by omega_arith) h₂]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, rd₄, P.rd, Mi.rd]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, wr₄, P.wr, Mi.wr]
  refine ⟨he₅, hrd, hwr, ?_, h96, h104, by rw [kCT 192 (by decide) (by decide), P.tlen],
    by rw [kCT 200 (by decide) (by decide), P.dat], by rw [kCT 208 (by decide) (by decide), P.len], fun hn => ?_,
    fun x hx => ?_⟩
  · -- What is written.
    have b24 : Region.Sub (below SP 8) (below SP 24) := below_sub (by decide) (by decide)
    have hS : ∀ {d k : Nat}, d + k ≤ 80 →
        Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ ⟨W, 112⟩ := fun {d k} h => by
      rw [add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
    refine Frame.trans (Frame.trans (Frame.trans (fA.sub fun r hr => ?_) (P.frame.sub fun r hr => ?_))
      (fC.sub fun r hr => ?_)) (fT.sub fun r hr => ?_) <;> simp only [obFrame, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    · rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, b24⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
      · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_arith)⟩
      · exact ⟨_, List.mem_cons_self .., hS (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., sub_empty⟩
      · exact ⟨_, by simp, b24⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, by simp, b24⟩
  · -- The nonce's length.
    have d216 : ∀ r ∈ (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame (W + BitVec.ofNat 64 16) W SP D (n / 16)),
        (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
      intro r hr
      simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · rw [add_ofNat_assoc]; exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · rw [add_ofNat_assoc]; exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((hD.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (C.t_w.sub_right (Lay.wSub (by decide))).symm
    rw [kCT 216 (by decide) (by decide), P.frame.readW (Region.contains_self _ _) d216 (by decide), h216 hn]
  · -- The blocks function's `scratch`.
    rw [frame_at fT (disj_tagF L (d := 448) (k := 2112) (by decide) (by decide)) hx,
      frame_at fC (disj_crF L hD' (d := 448) (k := 2112) (by decide) (by decide)) hx, hB x hx,
      frame_at fA (disj_aadF L nl (d := 448) (k := 2112) (by decide) (by decide) (.inr (.inl (by decide)))) hx]

/-! ## What `seal` leaves -/

/-- Word `j` (the 8 bytes from `8 j`) of `work` that `seal` leaves from 96 to
240, of its argument registers `g` and stack arguments `a`, if it writes it:
the lengths block (12, 13), the saved registers (16 to 21), `rounds` (22),
`aad_len` (23), `len` (24), the address and length of the data after the
whole blocks (25, 26), the nonce's length unless it is 12 (27), and `aad`
(29). -/
def sealWord (g : Reg → BitVec 64) (a : Nat → BitVec 64) (j : Nat) : Option (BitVec 64) :=
  match j with
  | 12 => some (byteRev64 (BitVec.ofNat 64 (8 * (g .r9).toNat)))
  | 13 => some (byteRev64 (BitVec.ofNat 64 (8 * (a 1).toNat)))
  | 16 => some (g .rbx)
  | 17 => some (g .rbp)
  | 18 => some (g .r12)
  | 19 => some (g .r13)
  | 20 => some (g .r14)
  | 21 => some (g .r15)
  | 22 => some (g .rsi)
  | 23 => some (g .r9)
  | 24 => some (a 1)
  | 25 => some (a 0 + BitVec.ofNat 64 (16 * ((a 1).toNat / 16)))
  | 26 => some (BitVec.ofNat 64 ((a 1).toNat % 16))
  | 27 => if (g .rcx).toNat = 12 then none else some (g .rcx)
  | 29 => some (g .r8)
  | _ => none

/-- What `seal` leaves at `x` in `work` (`W = a 3`) from byte 96 on, of its
argument registers `g` and stack arguments `a`, with a
`vg_aes_gcm_encrypt_blocks` that leaves `Lb` in its `scratch`: up to byte
240 the bytes of `sealWord`, from 448 those `Lb` says if there was a whole
block, and elsewhere nothing written (`none`). -/
def sealL (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) (g : Reg → BitVec 64) (a : Nat → BitVec 64) (x : Addr) : Option (BitVec 8) :=
  if (x - a 3).toNat < 240 then
    (sealWord g a ((x - a 3).toNat / 8)).map fun w => w.extractLsb' (8 * ((x - a 3).toNat % 8)) 8
  else if (x - a 3).toNat < 448 ∨ (a 1).toNat / 16 = 0 then none
  else Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat) (a 3 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
    (a 3 + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (a 0) (BitVec.ofNat 64 ((a 1).toNat / 16))
    (a 3 + BitVec.ofNat 64 448) x

/-- Byte `j` of a 64-bit little-endian read. -/
theorem byte_readW64' (m : Mem) (p : Addr) {j : Nat} (hj : j < 8) :
    m (p + BitVec.ofNat 64 j) = (m.readW p 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m p hj]; rfl

/-- `sealL`, from what is left: the words `sealWord` gives, the bytes where
it gives none and up to 448 as they were, and the blocks function's `scratch`. -/
theorem sealL_of {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {g : Reg → BitVec 64} {a : Nat → BitVec 64} {m m' : Mem} {W : Addr} (hW : a 3 = W)
    (hw : ∀ j, 12 ≤ j → j < 30 → ∀ w, sealWord g a j = some w → m'.readW (W + BitVec.ofNat 64 (8 * j)) 64 = w)
    (hn : ∀ d, 96 ≤ d → d < 2560 → (d < 240 → sealWord g a (d / 8) = none) →
      (240 ≤ d → d < 448 ∨ (a 1).toNat / 16 = 0) → m' (W + BitVec.ofNat 64 d) = m (W + BitVec.ofNat 64 d))
    (hb : ∀ d, 448 ≤ d → d < 2560 → (a 1).toNat / 16 ≠ 0 →
      m' (W + BitVec.ofNat 64 d) = (Lb (g .rdi) (BitVec.ofNat 64 (g .rsi).toNat)
        (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (a 0)
        (BitVec.ofNat 64 ((a 1).toNat / 16)) (W + BitVec.ofNat 64 448) (W + BitVec.ofNat 64 d)).getD
        (m (W + BitVec.ofNat 64 d))) :
    ∀ x, (⟨W + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 → m' x = (sealL Lb g a x).getD (m x) := by
  intro x hx
  have hx' : (x - (W + BitVec.ofNat 64 96)).toNat < 2464 := by simp only [Region.Contains] at hx; omega_using [hx]
  have hlt := (Offset.lt_iff x W (d := 96) (n := 2464) (by decide)).1 hx'
  generalize hd : (x - W).toNat = d at hlt
  have ex : x = W + BitVec.ofNat 64 d := by
    rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  subst ex
  simp only [sealL, hW, hd]
  by_cases h240 : d < 240
  · simp only [h240, ↓reduceIte]
    cases hj : sealWord g a (d / 8) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      exact hn d hlt.1 (by omega_arith) (fun _ => hj) fun h => absurd h (by omega_arith)
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      rw [← Offset.add_add_eq W (show 8 * (d / 8) + d % 8 = d by omega_arith),
        byte_readW64' m' (W + BitVec.ofNat 64 (8 * (d / 8))) (j := d % 8) (by omega_arith),
        hw (d / 8) (by omega_arith) (by omega_arith) w hj]
  · simp only [h240, ↓reduceIte]
    by_cases h448 : d < 448 ∨ (a 1).toNat / 16 = 0
    · simp only [h448, ↓reduceIte, Option.getD_none]
      exact hn d hlt.1 (by omega_arith) (fun h' => absurd h' h240) fun _ => h448
    · simp only [h448, ↓reduceIte]
      rw [not_or] at h448
      exact hb d (by omega_arith) (by omega_arith) h448.2

/-- Each region of `leftF` is in `W`, the data or the stack below `SP`. -/
theorem leftF_sub {W SP D : Addr} {n nl : Nat} :
    ∀ r ∈ leftF W SP D n nl, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 24) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (Region.sub_prefix (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by split <;> decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr (.inl fun _ h => h)
  · exact .inr (.inr fun _ h => h)

/-- What `seal` leaves in `work` from byte 96 on (`sealL`), from what its
entry (`E`, `fE`) and the pieces after it (`SL`) leave and the copy of the
tag to `tag` (`f₅`) writes. -/
theorem seal_final {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)} {s s₁ s₄ s₅ : State} {Ctx W SP Np A D T : Addr} {nl al n : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hW : stackArg s 3 = W)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hnl : (s.gpr .rcx).toNat = nl) (hA : s.gpr .r8 = A)
    (E : OneEntry s Ctx W SP A D n s₁) (fE : Frame (entryFrame W) s.mem s₁.mem)
    (SL : SealLeft Lb s s₁ Ctx W SP D (s.gpr .rsi).toNat n nl s₄) (f₅ : Frame [⟨T, 16⟩] s₄.mem s₅.mem)
    (d_tw : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ x, (⟨W + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
      s₅.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x) := by
  subst hCtx hW hD hn hnl hA
  have L := C.lay
  have ww := L.ww
  have dT : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨T, 16⟩ : Region)],
      (⟨stackArg s 3 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (d_tw.sub_right (Lay.wSub h)).symm
  have dL : ∀ {d k : Nat}, (112 ≤ d ∧ d + k ≤ 192) ∨ (216 ≤ d ∧ d + k ≤ 448 ∧ ((s.gpr .rcx).toNat = 12 ∨ 224 ≤ d)) →
      ∀ r ∈ leftF (stackArg s 3) SP (stackArg s 0) (stackArg s 1).toNat (s.gpr .rcx).toNat,
        (⟨stackArg s 3 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun {d k} h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · by_cases h12 : (s.gpr .rcx).toNat = 12
      · rw [ite_eq_left h12]; exact Lay.disj_empty
      · rw [ite_eq_right h12]; exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact (C.dE.sub_right (Lay.wSub (by omega_arith))).symm
    · exact (C.t_w.sub_right (Lay.wSub (by omega_arith))).symm
  have dE : ∀ {d k : Nat}, d + k ≤ 128 ∨ (192 ≤ d ∧ d + k ≤ 200) ∨ (216 ≤ d ∧ d + k ≤ 232) ∨ (240 ≤ d ∧ d + k ≤ 2560) →
      ∀ r ∈ entryFrame (stackArg s 3), (⟨stackArg s 3 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  -- The words kept from the entry, from the pieces after it, and from `tag`.
  have k5 : ∀ d, d + 8 ≤ 2560 → s₅.mem.readW (stackArg s 3 + BitVec.ofNat 64 d) 64 =
      s₄.mem.readW (stackArg s 3 + BitVec.ofNat 64 d) 64 :=
    fun d h => f₅.readW (r := ⟨stackArg s 3 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dT h) (by decide)
  have k1 : ∀ d, (112 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 448) →
      s₅.mem.readW (stackArg s 3 + BitVec.ofNat 64 d) 64 = s₁.mem.readW (stackArg s 3 + BitVec.ofNat 64 d) 64 :=
    fun d h => by
      rw [k5 d (by omega_arith), SL.frame.readW (r := ⟨stackArg s 3 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (dL (d := d) (k := 8) (by omega_arith)) (by decide)]
  have hsv : ∀ p ∈ saved, s₅.mem.readW (stackArg s 3 + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := fun p hp => by
    have hp' : (112 ≤ p.2 ∧ p.2 + 8 ≤ 192) ∨ (224 ≤ p.2 ∧ p.2 + 8 ≤ 448) := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k1 p.2 hp', E.saved p hp]
  have hlt := C.data.ok.lt
  refine sealL_of rfl (fun j h₁ h₂ w hj => ?_) (fun d h₁ h₂ hw hb => ?_) (fun d h₁ h₂ hz => ?_)
  · rcases (by omega_arith : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨
      j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sealWord, Option.some.injEq, reduceCtorEq, Nat.reduceMul] at hj ⊢
    · subst hj; rw [k5 96 (by decide)]; exact SL.w96
    · subst hj; rw [k5 104 (by decide), SL.w104, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · subst hj; exact hsv (.rbx, 128) (by simp [saved])
    · subst hj; exact hsv (.rbp, 136) (by simp [saved])
    · subst hj; exact hsv (.r12, 144) (by simp [saved])
    · subst hj; exact hsv (.r13, 152) (by simp [saved])
    · subst hj; exact hsv (.r14, 160) (by simp [saved])
    · subst hj; exact hsv (.r15, 168) (by simp [saved])
    · subst hj; rw [k1 176 (.inl ⟨by decide, by decide⟩), E.rounds.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · subst hj; rw [k1 184 (.inl ⟨by decide, by decide⟩), E.alen]
    · subst hj; rw [k5 192 (by decide), SL.w192, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · subst hj; rw [k5 200 (by decide), SL.w200]
    · subst hj; rw [k5 208 (by decide), SL.w208]
    · split at hj
      · exact absurd hj (by simp)
      · rename_i h12
        simp only [Option.some.injEq] at hj
        subst hj; rw [k5 216 (by decide), SL.w216 h12, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · subst hj; rw [k1 232 (.inr ⟨by decide, by decide⟩), E.aad]
  · -- The bytes left as they were.
    have hr : (112 ≤ d ∧ d < 128) ∨ (216 ≤ d ∧ d < 224 ∧ (s.gpr .rcx).toNat = 12) ∨ (224 ≤ d ∧ d < 232) ∨
        (240 ≤ d ∧ d < 448) ∨ (448 ≤ d ∧ (stackArg s 1).toNat / 16 = 0) := by
      by_cases h240 : d < 240
      · have hw := hw h240
        rcases (by omega_arith : d / 8 = 12 ∨ d / 8 = 13 ∨ d / 8 = 14 ∨ d / 8 = 15 ∨ d / 8 = 16 ∨ d / 8 = 17 ∨
          d / 8 = 18 ∨ d / 8 = 19 ∨ d / 8 = 20 ∨ d / 8 = 21 ∨ d / 8 = 22 ∨ d / 8 = 23 ∨ d / 8 = 24 ∨ d / 8 = 25 ∨
          d / 8 = 26 ∨ d / 8 = 27 ∨ d / 8 = 28 ∨ d / 8 = 29) with
          e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          rw [e] at hw <;> simp only [sealWord, reduceCtorEq] at hw
        · exact .inl ⟨by omega_arith, by omega_arith⟩
        · exact .inl ⟨by omega_arith, by omega_arith⟩
        · split at hw
          · rename_i h12; exact .inr (.inl ⟨by omega_arith, by omega_arith, h12⟩)
          · exact absurd hw (by simp)
        · exact .inr (.inr (.inl ⟨by omega_arith, by omega_arith⟩))
      · rcases hb (by omega_arith) with h | h
        · exact .inr (.inr (.inr (.inl ⟨by omega_arith, h⟩)))
        · by_cases h448 : d < 448
          · exact .inr (.inr (.inr (.inl ⟨by omega_arith, h448⟩)))
          · exact .inr (.inr (.inr (.inr ⟨by omega_arith, h⟩)))
    have e₁ : s₁.mem (stackArg s 3 + BitVec.ofNat 64 d) = s.mem (stackArg s 3 + BitVec.ofNat 64 d) :=
      frame_at fE (dE (by omega_arith)) (Region.contains_self _ _)
    rw [frame_at f₅ (dT (by omega_arith)) (Region.contains_self _ _), ← e₁]
    rcases hr with h | h | h | h | h
    · exact frame_at SL.frame (dL (.inl ⟨h.1, by omega_arith⟩)) (Region.contains_self _ _)
    · exact frame_at SL.frame (dL (.inr ⟨h.1, by omega_arith, .inl h.2.2⟩)) (Region.contains_self _ _)
    · exact frame_at SL.frame (dL (.inr ⟨by omega_arith, by omega_arith, .inr h.1⟩)) (Region.contains_self _ _)
    · exact frame_at SL.frame (dL (.inr ⟨by omega_arith, by omega_arith, .inr (by omega_arith)⟩)) (Region.contains_self _ _)
    · rw [SL.blk _ (Offset.contains _ h.1 (by omega_arith) (by omega_arith)), ite_eq_left h.2, Option.getD_none]
  · -- The blocks function's `scratch`.
    rw [frame_at f₅ (dT (by omega_arith)) (Region.contains_self _ _),
      SL.blk _ (Offset.contains _ h₁ (by omega_arith) (by omega_arith)), ite_eq_right hz,
      frame_at fE (dE (by omega_arith)) (Region.contains_self _ _)]

/-- `vg_aes_gcm_seal`, for a key context of kind `M`, with implementations of
`vg_ghash` and `vg_aes_ctr32` that never touch their working space and a
`vg_aes_gcm_encrypt_blocks` that leaves `Lb` in its `scratch`: what it leaves
in `work` from byte 96 on (`sealL`). -/
theorem sealM_leaves_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr → Option (BitVec 8)}
    (hL : BlkLeft Lb B.enc.code M) (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee)
    {s : State} (hp : (Proof.AesGcm.sealX86_64M M).pre s) :
    WP isa («seal» (v.withBlk B)) s fun s' => (∀ x,
      (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
        s'.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
      Frame [⟨stackArg s 3, 2560⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, 16⟩, below (s.gpr .rsp) 24]
        s.mem s'.mem := by
  refine WP.reassoc_seal' ?_
  have X := CtxExt.ofSeal hp.1 hp.2
  obtain ⟨C, hTw, d_td, d_tw, r_t⟩ := OneCtx.ofSeal hp.1 M.ge
  have L := C.lay
  have hwa := C.args 3 (by decide)
  have hta := C.args 2 (by decide)
  have hnlt : (stackArg s 1).toNat < 2 ^ 64 := (stackArg s 1).isLt
  refine WP.seq (WP.mono (oneEntry_okL (by decide) C rfl rfl rfl rfl rfl (wo := 32) rfl hwa) fun s₁ ⟨E, fE⟩ => ?_)
  refine WP.seq (WP.mono (sealRun_leaves v B hL gf cf C X E rfl rfl rfl) fun s₄ SL => WP.seq ?_)
  -- The tag copied to `tag`.
  have dA := C.arg24 (by decide)
  have hT₄' : s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := by
    rw [SL.env.rsp, SL.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
      (fun r hr => dA r (leftF_sub r hr)) (by decide),
      fE.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => dA r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact .inl (Lay.wSub (by decide)))) (by decide)]
    rfl
  obtain ⟨s₅, run₅, -, f₅, hg₅, hrd₅, hwr₅⟩ := tagOut_ok (b := .rsp) (d := 24) SL.env.r15 hT₄'
    (by rw [SL.env.rsp, SL.rd, SL.wr]; exact hta) SL.env.perm.w (by rw [SL.wr]; exact hTw)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have he₅ : Env (s.gpr .rdi) (stackArg s 3 + BitVec.ofNat 64 16) (stackArg s 3) (s.gpr .rsp) s₅ :=
    SL.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  -- `W`'s bytes apart from `tag` and from what the pieces after the entry write.
  have dT : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨stackArg s 2, 16⟩ : Region)],
      (⟨stackArg s 3 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (d_tw.sub_right (Lay.wSub h)).symm
  have hsv₄ : SavedAt s₄.mem (stackArg s 3) s := E.saved.frame SL.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by decide) (by have := L.ww; omega_arith)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by split <;> decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (C.dE.sub_right (Lay.wSub (by decide))).symm
    · exact (C.t_w.sub_right (Lay.wSub (by decide))).symm
  have hsv₅ : SavedAt s₅.mem (stackArg s 3) s := hsv₄.frame f₅ (dT (by decide))
  have r₅ : ∀ r ∈ [(⟨stackArg s 2, 16⟩ : Region)], (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact r_t
  have r₄ : ∀ r ∈ leftF (stackArg s 3) (s.gpr .rsp) (stackArg s 0) (stackArg s 1).toNat (s.gpr .rcx).toNat,
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r := fun r hr => by
    rcases leftF_sub r hr with h | h | h
    · exact C.rW.sub_right h
    · exact C.rD.sub_right h
    · exact (Offset.base_disjoint_below _ (n := 24) (k := 8) (by decide)).sub_right h
  have r₁ : ∀ r ∈ entryFrame (stackArg s 3), (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact C.rW.sub_right (Lay.wSub (by decide))
  have hret : s₅.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    rw [ret_kept f₅ r₅, ret_kept SL.frame r₄, ret_kept fE r₁]
  refine WP.mono (exit_ok (s₀ := s) he₅.r15 he₅.rsp (covers_left he₅.perm.w) hsv₅ hret) fun s' ⟨_, hm, _⟩ => ?_
  rw [hm]
  refine ⟨seal_final C rfl rfl rfl rfl rfl rfl E fE SL f₅ d_tw, ?_⟩
  refine ((fE.sub fun r hr => ?_).trans (SL.frame.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · rcases leftF_sub r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩


/-- `sealWord` reads no register but those it names, and no stack argument
but the first two. -/
theorem sealWord_congr {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : ∀ i < 4, a i = a' i) (j : Nat) :
    sealWord g a j = sealWord g' a' j := by
  unfold sealWord
  rw [hg .r9 (by decide) (by decide), hg .rbx (by decide) (by decide), hg .rbp (by decide) (by decide),
    hg .r12 (by decide) (by decide), hg .r13 (by decide) (by decide), hg .r14 (by decide) (by decide),
    hg .r15 (by decide) (by decide), hg .rsi (by decide) (by decide), hg .rcx (by decide) (by decide),
    hg .r8 (by decide) (by decide), ha 0 (by decide), ha 1 (by decide)]

/-- `sealL` reads neither `rax` nor `rsp`, and no stack argument after the
fourth. -/
theorem sealL_congr (Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
      Option (BitVec 8)) {g g' : Reg → BitVec 64} {a a' : Nat → BitVec 64}
    (hg : ∀ r, r ≠ .rax → r ≠ .rsp → g r = g' r) (ha : ∀ i < 4, a i = a' i) :
    sealL Lb g a = sealL Lb g' a' := by
  funext x
  unfold sealL
  rw [funext (sealWord_congr hg ha), hg .rdi (by decide) (by decide), hg .rsi (by decide) (by decide),
    ha 0 (by decide), ha 1 (by decide), ha 3 (by decide)]

/-- `vg_aes_gcm_seal`, for a key context of kind `M`, with implementations of
`vg_ghash` and `vg_aes_ctr32` that never touch their working space and a
`vg_aes_gcm_encrypt_blocks` that leaves a function of its arguments in its
`scratch` (`BlkLeaves`): what it leaves in `work` (the fourth stack
argument) from byte 96 on is a function of its argument registers and its
stack arguments (`sealL`, which reads neither `rax` nor `rsp`, nor a stack
argument after `work`: `sealL_congr`), byte by byte either a value
(`some b`) or what was there (`none`). -/
theorem seal_leaves (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (hB : BlkLeaves B)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M M).pre s → Exec isa («seal» (v.withBlk B)) s t s' →
        ∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          s'.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x) := by
  obtain ⟨Lb, hL⟩ := hB
  refine ⟨Lb, fun s t s' hp he => ?_⟩
  obtain ⟨_, s'', he', h⟩ := sealM_leaves_wp v B hL gf cf hp
  obtain ⟨_, rfl⟩ := Exec.det he he'
  exact h.1

/-- `seal_leaves`, and what `seal` writes: `work`, the data, the tag and the
stack below `rsp`. -/
theorem seal_leavesF (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (hB : BlkLeaves B)
    (gf : GhashFree v.gh.fn.code) (cf : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    ∃ Lb : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Addr → Addr →
        Option (BitVec 8),
      ∀ s t s', (Proof.AesGcm.sealX86_64M M).pre s → Exec isa («seal» (v.withBlk B)) s t s' →
        (∀ x, (⟨stackArg s 3 + BitVec.ofNat 64 96, 2464⟩ : Region).Contains x 1 →
          s'.mem x = (sealL Lb s.gpr (fun i => stackArg s i) x).getD (s.mem x)) ∧
        Frame [⟨stackArg s 3, 2560⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, 16⟩,
          below (s.gpr .rsp) 24] s.mem s'.mem := by
  obtain ⟨Lb, hL⟩ := hB
  refine ⟨Lb, fun s t s' hp he => ?_⟩
  obtain ⟨_, s'', he', h⟩ := sealM_leaves_wp v B hL gf cf hp
  obtain ⟨_, rfl⟩ := Exec.det he he'
  exact h

end VG.Proof.AesGcm.X86_64
