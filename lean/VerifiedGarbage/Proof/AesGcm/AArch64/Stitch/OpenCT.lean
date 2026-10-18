module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on AArch64, interleaved: `vg_aes_gcm_open` is constant time

Untrusted: everything here is checked by Lean. As `Fast/OpenCT.lean` does
for `openRunWithP`: the code between the calls by the taint analysis, the
interleaved loop and its table by `stitched_rel`, the calls by a hypothesis
on the hash's call and `rel_ctr`, and the branch on the tag (`omBS_rel`),
which both runs take the same way, by the taint analysis and `cryptAl_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen ctxH ctxCiph inc32)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

section
variable {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- After `front` and keeping the first counter block: what the interleaved
loop needs. -/
theorem openSIn_of {H : Block} {s₀ t s₂ s₂c : State} {tb : List Instr}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem Np 12) (bytesAt t.mem A al) D n t s₂)
    (m₂c : s₂c.mem = s₂.mem.write (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) 16
      (s₂.mem.read (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16))
    (g₂c : s₂c.gpr = s₂.gpr) (sp₂c : s₂c.sp = s₂.sp) (rd₂c : s₂c.rd = s₂.rd) (wr₂c : s₂c.wr = s₂.wr)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t.rd → u.wr = t.wr →
      Frame [workR W, ⟨D, n⟩] t.mem u.mem → KeyAt H u.mem W → WP isa (.block tb) u (Stitch.TblPost W H u)) :
    Stitch.SIn Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length))
      (inc32 (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) R D n s₂c ∧
      Stitch.TbOk Ctx (W + BitVec.ofNat 64 16) W SP H tb s₂c ∧ Frame [workR W, ⟨D, n⟩] t.mem s₂c.mem ∧
      KeyAt H s₂c.mem W := by
  have L := o.lay
  have he₂c : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂c := h₂.env.keep (fun r _ => by rw [g₂c]) sp₂c rd₂c wr₂c
  have fcb : Frame [⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩] s₂.mem s₂c.mem := by
    rw [m₂c]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dcbR : ∀ {R' : Region}, (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint R' →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region)], R'.Disjoint r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.symm
  have F₂c : Frame [workR W, ⟨D, n⟩] t.mem s₂c.mem := by
    refine (h₂.frame.sub fun r hr => ⟨_, List.mem_cons_self .., frontFrame'_work W r hr⟩).trans
      (fcb.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have key₂c : KeyAt H s₂c.mem W := h₂.key.frame fcb (dcbR (L.w_w (.inr (by decide)) (by decide) (by decide)))
  refine ⟨⟨he₂c, by rw [g₂c, h₂.x22, o.x22], o.rounds, by rw [g₂c, h₂.x23], by rw [g₂c, h₂.x26],
    o.dat.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr]),
    by rw [blockAt_frame fcb (dcbR ((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right
      (Lay.wSub (by decide))).symm), h₂.hH],
    by rw [blockAt_frame fcb (dcbR (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm),
      h₂.cb],
    by rw [blockAt_frame fcb (dcbR (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm),
      h₂.y], ?_⟩, fun u heu hm hrd hwr _ => htb u heu (by rw [hrd, rd₂c, h₂.rd]) (by rw [hwr, wr₂c, h₂.wr])
      (by rw [hm]; exact F₂c) (by rw [hm]; exact key₂c), F₂c, key₂c⟩
  rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _

/-- The pointers of the rest and the arguments of the call on its whole
blocks, after the interleaved loop: `Mid`, and `Abs3`. -/
theorem openBlk_ok {H : Block} {s₀ t s₂ s₂c s₂' : State} {x : List Byte} {icb : Block} {c : Mem → List Byte}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem Np 12) (bytesAt t.mem A al) D n t s₂)
    (g₂c : s₂c.gpr = s₂.gpr) (rd₂c : s₂c.rd = s₂.rd) (wr₂c : s₂c.wr = s₂.wr)
    (F₂c : Frame [workR W, ⟨D, n⟩] t.mem s₂c.mem) (key₂c : KeyAt H s₂c.mem W)
    (hH₂c : blockAt s₂c.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hm : Stitch.SMid Ctx (W + BitVec.ofNat 64 16) W SP H x icb R D n c s₂c s₂') :
    WP isa (.block (Impl.AesGcm.AArch64.Stitch.whole ++ ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr) ++
        absSeg2 16)) s₂' fun s₆ => ∃ s₃ : State, ∃ X : Addr,
      Mid Ctx W SP H R n D (BitVec.ofNat 64 tl) X t s₃ ∧
      Abs3 Ctx (W + BitVec.ofNat 64 16) W SP s₃.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n)
        0 s₃.mem 0 s₆ ∧ s₆.rd = s₃.rd ∧ s₆.wr = s₃.wr := by
  have L := o.lay
  have hn := o.dat.ok.lt
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  have subP : Region.Sub ⟨D, Stitch.pre n⟩ ⟨D, n⟩ := Region.sub_prefix hpn
  have g₂' : ∀ r ∈ [Reg.x19, .x22, .x23, .x26, .x27, .x28], s₂'.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hm.gpr _ (by decide), g₂c]
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, x23₃, x24₃, x25₃, r₃⟩ := Stitch.afterD_ok (u := s₂') (D := D) (n := n)
    (by rw [g₂' _ (by simp), h₂.x23]) (by rw [g₂' _ (by simp), h₂.x26]) hn
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := hm.env.of_regs r₃
  have hd₃ : DataW Ctx (W + BitVec.ofNat 64 16) W s₃ D n :=
    o.dat.of_eq (by rw [r₃.rd, hm.rd, rd₂c, h₂.rd]) (by rw [r₃.wr, hm.wr, wr₂c, h₂.wr])
  have dS : ∀ {R' : Region}, R'.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ →
      R'.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ → R'.Disjoint ⟨D, Stitch.pre n⟩ →
      R'.Disjoint (Stitch.tblR W) → ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W D n, R'.Disjoint r :=
    fun h1 h2 h3 h4 r hr => by
      simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [r₃.mem, blockAt_frame hm.frame (dS ((L.cs.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.stSub (by decide)))
      ((L.cs.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.stSub (by decide)))
      ((o.dat.ctx.sub_left (Lay.ctxSub (by decide))).sub_right subP)
      ((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.wSub (by decide)))), hH₂c]
  have key₃ : KeyAt H s₃.mem W := by
    rw [r₃.mem]
    exact key₂c.frame hm.frame (dS (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      ((o.ddW.sub_left subP).sub_right (Lay.wSub (by decide))).symm
      (Offset.disjoint W (.inl (by decide)) (by decide) (by decide)))
  have F₃ : Frame [workR W, ⟨D, n⟩] t.mem s₃.mem := by
    rw [r₃.mem]
    refine F₂c.trans (hm.frame.sub fun r hr => ?_)
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), subP⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₃.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n))
      (n - Stitch.pre n) 0 s₃.mem 0 s₃ :=
    ⟨he₃, fun _ _ => rfl, Nat.zero_le _, by rw [x23₃]; simp, by rw [x24₃, Nat.sub_zero], x25₃,
      hd₃.ok.drop hpn, hH₃, fun ha => by simpa [bytesAt] using ha, .inr rfl, Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  have k : ∀ r ∈ [Reg.x22, .x26, .x28], s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [r₃.others _ (by decide), g₂' _ (by simp)]
  exact ⟨s₃, s₃.gpr .x27, ⟨he₃, by rw [k _ (by simp), h₂.x22, o.x22], o.rounds, by rw [k _ (by simp), h₂.x26], rfl,
    by rw [k _ (by simp), h₂.x28, o.x28], hH₃, key₃, hd₃, F₃, by rw [r₃.rd, hm.rd, rd₂c, h₂.rd],
    by rw [r₃.wr, hm.wr, wr₂c, h₂.wr]⟩, h₆, rd₆, wr₆⟩

/-- `openRunAS` in two runs from the same public arguments. -/
theorem openRunAS_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr}
    {s₀₁ s₀₂ t₁ t₂ : State}
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
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₁.rd → u.wr = t₁.wr →
      Frame [workR W, ⟨D, n⟩] t₁.mem u.mem → KeyAt (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u))
    (htb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₂.rd → u.wr = t₂.wr →
      Frame [workR W, ⟨D, n⟩] t₂.mem u.mem → KeyAt (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u))
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = t₁.rd → v₁.wr = t₁.wr → Frame [workR W, ⟨D, n⟩] t₁.mem v₁.mem →
      v₂.rd = t₂.rd → v₂.wr = t₂.wr → Frame [workR W, ⟨D, n⟩] t₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT) :
    RelCT isa (Eq2 t₁ t₂) (openRunAS v.callees cl tb) TT := by
  have L := o₁.lay
  have hn := o₁.dat.ok.lt
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  have hJ₁ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t₁.gpr (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t₁ :=
    ⟨o₁.env, fun _ _ => rfl, o₁.x23, o₁.x24, o₁.x26, o₁.x27, o₁.non, rfl⟩
  have hJ₂ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t₂.gpr (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t₂ :=
    ⟨o₂.env, fun _ _ => rfl, o₂.x23, o₂.x24, o₂.x26, o₂.x27, o₂.non, rfl⟩
  unfold openRunAS
  refine rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
      (by rw [o₁.env.sp, o₂.env.sp])
      (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, o₁.env.x19, o₂.env.x19, o₁.env.x20, o₂.env.x20,
        o₁.env.x21, o₂.env.x21, o₁.x23, o₂.x23]) ⟨_, by taint_decide⟩)
    (front_ok L hMK hJ₁ o₁.aad hal x4₁ x5₁ x6₁ x7₁) (front_ok L hMK hJ₂ o₂.aad hal x4₂ x5₂ x6₂ x7₂)
    fun s₂ u₂ h₂ k₂ => ?_
  obtain ⟨s₂c, run₂c, m₂c, g₂c, sp₂c, rd₂c, wr₂c⟩ := saveCb_ok h₂.env
  obtain ⟨u₂c, run₂c', m₂c', g₂c', sp₂c', rd₂c', wr₂c'⟩ := saveCb_ok k₂.env
  refine rel_seq (rel_taint [.x19, .x20] (by rw [h₂.env.sp, k₂.env.sp])
      (by agree_tac [h₂.env.x19, k₂.env.x19, h₂.env.x20, k₂.env.x20]) ⟨_, by taint_decide⟩)
    (F₁ := fun s => s = s₂c) (F₂ := fun s => s = u₂c)
    (WP.of_runBlock ⟨s₂c, run₂c, rfl⟩) (WP.of_runBlock ⟨u₂c, run₂c', rfl⟩) fun _ _ e₁ e₂ => ?_
  subst e₁ e₂
  obtain ⟨S₁, T₁, F₁, key₁⟩ := openSIn_of o₁ h₂ m₂c g₂c sp₂c rd₂c wr₂c htb₁
  obtain ⟨S₂, T₂, F₂, key₂⟩ := openSIn_of o₂ k₂ m₂c' g₂c' sp₂c' rd₂c' wr₂c' htb₂
  refine rel_seq (stitched_rel (n := n) (by rw [S₁.env.sp, S₂.env.sp]) (fun r hr h9 => ?_) S₁.x26 hn
      fun v₁ v₂ hsp hr g₁ m₁ r₁ w₁ sp₁ g₂ m₂ r₂ w₂ sp₂ => htbrel v₁ v₂ (by rw [sp₁, S₁.env.sp])
        (by rw [sp₂, S₂.env.sp]) hr (by rw [r₁, rd₂c, h₂.rd]) (by rw [w₁, wr₂c, h₂.wr]) (by rw [m₁]; exact F₁)
        (by rw [r₂, rd₂c', k₂.rd]) (by rw [w₂, wr₂c', k₂.wr]) (by rw [m₂]; exact F₂))
    (Stitch.stitchD_ok L gh T₁ S₁) (Stitch.stitchD_ok L gh T₂ S₂) fun s₃ u₃ m₁ m₂ => ?_
  · simp only [stRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h9
    · rw [S₁.env.x19, S₂.env.x19]
    · rw [S₁.env.x20, S₂.env.x20]
    · rw [S₁.env.x21, S₂.env.x21]
    · rw [S₁.x22, S₂.x22]
    · rw [S₁.x23, S₂.x23]
    · rw [S₁.x26, S₂.x26]
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x26] (by rw [m₁.env.sp, m₂.env.sp])
      (by agree_tac [m₁.env.x19, m₂.env.x19, m₁.env.x20, m₂.env.x20, m₁.env.x21, m₂.env.x21,
        m₁.gpr .x23 (by decide), m₂.gpr .x23 (by decide), m₁.gpr .x26 (by decide), m₂.gpr .x26 (by decide),
        S₁.x23, S₂.x23, S₁.x26, S₂.x26]) ⟨_, by taint_decide⟩)
    (openBlk_ok o₁ h₂ g₂c rd₂c wr₂c F₁ key₁ S₁.hH m₁) (openBlk_ok o₂ k₂ g₂c' rd₂c' wr₂c' F₂ key₂ S₂.hH m₂)
    fun u₁ u₂ ⟨q₁, X₁, M₁, a₁, rd₁, wr₁⟩ ⟨q₂, X₂, M₂, a₂, rd₂, wr₂⟩ => ?_
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
  have hDd : Region.Sub ⟨D + BitVec.ofNat 64 (Stitch.pre n) + BitVec.ofNat 64 0,
      16 * ((n - Stitch.pre n - 0) / 16)⟩ ⟨D, n⟩ :=
    fun x hx => (Offset.sub_base D (by omega) : Region.Sub ⟨D + BitVec.ofNat 64 (Stitch.pre n), n - Stitch.pre n⟩
      ⟨D, n⟩) x (Offset.sub_base _ (by omega) x hx)
  refine rel_seq (hrel a₁.call a₂.call sY sS a₁.env.sp a₂.env.sp r₁ w₁ fr₁ r₂ w₂ fr₂ hDd)
    (WP.with_rdwr (absCall2WithX_ok L (.inr rfl) (Q := fun _ => True) hexH hexB a₁
      (WP.mono (hgh₁ _ a₁.call sY sS r₁ w₁ a₁.env.sp fr₁ hDd) fun _ g => ⟨g, trivial⟩)))
    (WP.with_rdwr (absCall2WithX_ok L (.inr rfl) (Q := fun _ => True) hexH hexB a₂
      (WP.mono (hgh₂ _ a₂.call sY sS r₂ w₂ a₂.env.sp fr₂ hDd) fun _ g => ⟨g, trivial⟩)))
    fun s₇ t₇ ⟨⟨⟨b₁, l₁⟩, _⟩, rd₇, wr₇⟩ ⟨⟨⟨b₂, l₂⟩, _⟩, rd₇', wr₇'⟩ => ?_
  have N₁ := Mid.absorbXS L M₁ b₁ (by rw [rd₇, rd₁]) (by rw [wr₇, wr₁]) hexK
  have N₂ := Mid.absorbXS L M₂ b₂ (by rw [rd₇', rd₂]) (by rw [wr₇', wr₂]) hexK
  refine RelCT.seq_assoc3 (rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x26] (by rw [N₁.env.sp, N₂.env.sp])
      (by agree_tac [N₁.env.x19, N₂.env.x19, N₁.env.x20, N₂.env.x20, N₁.env.x21, N₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24, N₁.x26, N₂.x26]) ⟨_, by taint_decide⟩)
    (ctE'_ok L hMK (.inr rfl) N₁ b₁ l₁) (ctE'_ok L hMK (.inr rfl) N₂ b₂ l₂)
    fun s₁₆ t₁₆ ⟨_, _, _, _, T₁, k28₁⟩ ⟨_, _, _, _, T₂, k28₂⟩ => ?_)
  refine rel_seq (rel_ctr v.ctr T₁.call T₂.call (by rw [T₁.env.sp, T₂.env.sp]))
    (tagCall_ok L v (.inr rfl) T₁) (tagCall_ok L v (.inr rfl) T₂) fun s₁₇ t₁₇ O₁ O₂ => ?_
  exact rel_taint [.x19, .x28] (by rw [O₁.env.sp, O₂.env.sp])
    (by agree_tac [O₁.env.x19, O₂.env.x19, O₁.kept .x28 (by decide), O₂.kept .x28 (by decide), k28₁, k28₂])
    ⟨_, by taint_decide⟩

end

section
variable {Ctx W SP D Np A : Addr} {R nl al n tl P : Nat}

/-- The arguments of `failB`'s `cryptAl`: the first `P` bytes, from the kept
counter block. -/
theorem failCr_ok {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidS fr Ctx W SP D Np A R nl al n tl P s s₇) :
    ∃ s₈, runBlock isa (([.ldrq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO, .strq .v0 .x20 48,
      .ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      [mov .x24 .x9, imm .x25 0]) s₇ = some s₈ ∧
      CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D P s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 := by
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  obtain ⟨s₈, run₈, _, x23₈, x24₈, x25₈, og₈, sp₈, rd₈, wr₈⟩ := failArgs_ok mo
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := mo.env.keep (fun r hr => og₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  exact ⟨s₈, run₈, ⟨he₈, fun _ _ => rfl, by rw [og₈ _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
    (mo.data.take hPn).of_eq rd₈ wr₈⟩, og₈ _ (by decide)⟩

/-- The arguments of `okB`'s `cryptAl`: the rest. -/
theorem okCr_ok {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidS fr Ctx W SP D Np A R nl al n tl P s s₇) :
    ∃ s₈, runBlock isa (([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr)) s₇ = some s₈ ∧
      CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R P (D + BitVec.ofNat 64 P) (n - P) s₈ ∧
        s₈.gpr .x27 = s₇.gpr .x27 := by
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  obtain ⟨s₈, run₈, x23₈, x24₈, x25₈, r₈⟩ := okArgs_ok mo
  exact ⟨s₈, run₈, ⟨mo.env.of_regs r₈, fun _ _ => rfl, by rw [r₈.others _ (by decide), mo.x22], hR, x23₈, x24₈,
    x25₈, (mo.data.drop hPn).of_eq r₈.rd r₈.wr⟩, r₈.others _ (by decide)⟩

/-- `omBS` in two runs whose tags compare alike. -/
theorem omBS_rel (v : GcmImpl) (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr fr' : List Region}
    {s s' m₁ m₂ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo₁ : MidS fr Ctx W SP D Np A R nl al n tl P s m₁) (mo₂ : MidS fr' Ctx W SP D Np A R nl al n tl P s' m₂)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (omBS v.callees) TT := by
  have hP16 : P % 16 = 0 := by rw [mo₁.hP]; omega
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  have ite_ok : ∀ {fr : List Region} {s m : State}, MidS fr Ctx W SP D Np A R nl al n tl P s m →
      WP isa (.ite (.zero .x .x27) (failB v.callees) (okB v.callees)) m fun u => u.sp = SP ∧
        u.gpr .x27 = m.gpr .x27 := fun {fr s m} mo => by
    refine WP.ite _ (eval_zero mo.x27 (hlt _)) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨s₈, run₈, hc, k27⟩ := failCr_ok hR mo
      exact WP.seq (WP.of_runBlock ⟨s₈, run₈, WP.mono (cryptAl_ok L v (icb := 0) hc rfl) fun s₉ h₉ =>
        ⟨h₉.env.sp, by rw [h₉.kept .x27 (by decide), k27]⟩⟩)
    · obtain ⟨s₈, run₈, hc, k27⟩ := okCr_ok hR mo
      exact WP.seq (WP.of_runBlock ⟨s₈, run₈, WP.mono (cryptAl_ok L v (icb := 0) hc hP16) fun s₉ h₉ =>
        ⟨h₉.env.sp, by rw [h₉.kept .x27 (by decide), k27]⟩⟩)
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  unfold omBS
  refine rel_seq ?_ (ite_ok mo₁) (ite_ok mo₂) fun a b ⟨ea, xa⟩ ⟨eb, xb⟩ =>
    rel_taint [.x27] (by rw [ea, eb]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨s₈, run₈, hc₁, -⟩ := failCr_ok hR mo₁
    obtain ⟨t₈, run₈', hc₂, -⟩ := failCr_ok hR mo₂
    unfold failB
    refine rel_seq (rel_taint [.x19, .x20] (by rw [mo₁.env.sp, mo₂.env.sp])
        (by agree_tac [mo₁.env.x19, mo₂.env.x19, mo₁.env.x20, mo₂.env.x20]) ⟨_, by taint_decide⟩)
      (F₁ := fun u => u = s₈) (F₂ := fun u => u = t₈)
      (WP.of_runBlock ⟨s₈, run₈, rfl⟩) (WP.of_runBlock ⟨t₈, run₈', rfl⟩) fun _ _ e₁ e₂ => ?_
    subst e₁ e₂
    exact cryptAl_rel L v hc₁ hc₂ rfl
  · obtain ⟨s₈, run₈, hc₁, -⟩ := okCr_ok hR mo₁
    obtain ⟨t₈, run₈', hc₂, -⟩ := okCr_ok hR mo₂
    unfold okB
    refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp])
        (by agree_tac [mo₁.env.x19, mo₂.env.x19]) ⟨_, by taint_decide⟩)
      (F₁ := fun u => u = s₈) (F₂ := fun u => u = t₈)
      (WP.of_runBlock ⟨s₈, run₈, rfl⟩) (WP.of_runBlock ⟨t₈, run₈', rfl⟩) fun _ _ e₁ e₂ => ?_
    subst e₁ e₂
    exact cryptAl_rel L v hc₁ hc₂ hP16

end

section
variable {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `openRunWithS` in two runs, after `tagIn`, whose tags compare alike. -/
theorem openRunWithS_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {nl : Nat}
    {s₀₁ s₀₂ t₁ t₂ : State}
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
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb₁ : TbForO tb Ctx W SP D n s₀₁) (htb₂ : TbForO tb Ctx W SP D n s₀₂)
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = s₀₁.rd → v₁.wr = s₀₁.wr → Frame [workR W, ⟨D, n⟩] s₀₁.mem v₁.mem →
      v₂.rd = s₀₂.rd → v₂.wr = s₀₂.wr → Frame [workR W, ⟨D, n⟩] s₀₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT) :
    RelCT isa (Eq2 t₁ t₂) (Impl.AesGcm.AArch64.Stitch.openRunWithS v.callees tb cl) TT := by
  subst h12
  have L := o₁.lay
  have F₁ : Frame [workR W, ⟨D, n⟩] s₀₁.mem t₁.mem :=
    o₁.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  have F₂ : Frame [workR W, ⟨D, n⟩] s₀₂.mem t₂.mem :=
    o₂.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  have hH₁ := o₁.vals.2.1
  have hH₂ := o₂.vals.2.1
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
  have tb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₁.rd → u.wr = t₁.wr →
      Frame [workR W, ⟨D, n⟩] t₁.mem u.mem → KeyAt (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u) :=
    fun u he hrd hwr hf key => by
      rw [hH₁] at key ⊢; exact htb₁ u he (hrd.trans o₁.rd₀) (hwr.trans o₁.wr₀) (F₁.trans hf) key
  have tb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₂.rd → u.wr = t₂.wr →
      Frame [workR W, ⟨D, n⟩] t₂.mem u.mem → KeyAt (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u) :=
    fun u he hrd hwr hf key => by
      rw [hH₂] at key ⊢; exact htb₂ u he (hrd.trans o₂.rd₀) (hwr.trans o₂.wr₀) (F₂.trans hf) key
  refine (openRunWithS_split v.callees cl tb).symm.rel (rel_seq
    (openRunAS_relX v cl hMK gh hexW hexC o₁ o₂ hx₁ hx₂ hal g₁ g₂
      (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd =>
        hrel c₁ c₂ sY sS sp₁ sp₂ (r₁.trans o₁.rd₀) (w₁.trans o₁.wr₀) (F₁.trans f₁) (r₂.trans o₂.rd₀)
          (w₂.trans o₂.wr₀) (F₂.trans f₂) hd) tb₁ tb₂
      (fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrel v₁ v₂ sp₁ sp₂ hr (r₁.trans o₁.rd₀) (w₁.trans o₁.wr₀)
        (F₁.trans f₁) (r₂.trans o₂.rd₀) (w₂.trans o₂.wr₀) (F₂.trans f₂)))
    (WP.mono (openRunASX_ok cl v hMK gh (I := fun _ => True) o₁ hx₁.1 hx₁.2.1 hx₁.2.2.1 hx₁.2.2.2 hal hok
      hexW hexD hexC (fun _ _ => trivial) (fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₁ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) tb₁) fun _ q => q.1)
    (WP.mono (openRunASX_ok cl v hMK gh (I := fun _ => True) o₂ hx₂.1 hx₂.2.1 hx₂.2.2.1 hx₂.2.2.2 hal hok
      hexW hexD hexC (fun _ _ => trivial) (fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₂ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) tb₂) fun _ q => q.1) fun m₁ m₂ mo₁ mo₂ => ?_)
  refine omBS_rel v L o₁.rounds mo₁ mo₂ ?_
  rw [mo₁.x27, mo₂.x27, tagBit o₁ rt₁ hok, tagBit o₂ rt₂ hok, hb]

end

/-- `open` with the interleaved path for TLS records, its whole blocks hashed
by `gh`, is constant time, for a `gh` that hashes as `vg_ghash` and leaks the
same in two runs, called with memory changed since the entry only in the
working space and the text, and a `tb` that writes the table and leaks the
same in two runs. -/
theorem openWithSX_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 2 ∨ w = 3)
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
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb : ∀ {σ : State}, pre σ → TbForO tb (σ.gpr .x0) (stackArg σ w) σ.sp (σ.gpr .x6) (σ.gpr .x7).toNat σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl) := by
  unfold Impl.AesGcm.AArch64.Stitch.openWithS
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
    have htb₂ := htb p₂
    rw [← q0, ← qa w (by omega), ← q6, ← q7, ← qsp] at htb₂
    have regs : ∀ {u t : State}, (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u.gpr r = σ₁.gpr r) →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = u.gpr r) →
        t.gpr .x4 = σ₁.gpr .x4 ∧ t.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat ∧ t.gpr .x6 = σ₁.gpr .x6 ∧
          t.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := fun ku kt =>
      ⟨by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat'],
        by rw [kt _ (by simp), ku _ (by simp)], by rw [kt _ (by simp), ku _ (by simp), ofNat_toNat']⟩
    unfold Impl.AesGcm.AArch64.Stitch.openFastS
    refine openRestWith_rel v₁ v₂ y12₁ y12₂
      (fun o' hT hok hx => have e := regs kk₁ hx
        WP.mono (openRunWithS_postX v cl hMK gh (I := fun _ => True) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok
          (hexW p₁) (hexD p₁) (hexC p₁) (fun _ _ => trivial)
          (fun s' _ _ _ _ c sY sS hr hw hsp hf hd =>
            WP.mono (hgh p₁ c sY sS hr hw hsp hf hd) fun _ g => ⟨g, trivial⟩) (htb p₁)) fun _ q => q.1)
      (fun o' hT hok hx => have e := regs kk₂ hx
        WP.mono (openRunWithS_postX v cl hMK gh (I := fun _ => True) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok
          (hexW p₁) (hexD p₁) (hexC p₁) (fun _ _ => trivial)
          (fun s' _ _ _ _ c sY sS hr hw hsp hf hd =>
            WP.mono (hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd) fun _ g => ⟨g, trivial⟩) htb₂) fun _ q => q.1)
      fun p₁' p₂' rt₁ rt₂ hok hx₁ hx₂ => openRunWithS_relX v cl hMK gh (hexW p₁) (hexD p₁) (hexC p₁) p₁' p₂' hc.2
        (regs kk₁ hx₁) (regs kk₂ hx₂) hc.1 rt₁ rt₂ hok hb
        (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh p₁ c sY sS hr hw hsp hf hd)
        (fun s' _ _ _ _ c sY sS hr hw hsp hf hd => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf hd)
        (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd)
        (htb p₁) htb₂ (fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrel p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂)
  · exact openRestWith_rel v₁ v₂ y12₁ y12₂ (fun o' hT hok _ => openMain_post v o' hT hok)
      (fun o' hT hok _ => openMain_post v o' hT hok) fun p₁' p₂' rt₁ rt₂ hok _ _ =>
        openMain_rel v p₁' p₂' rt₁ rt₂ hok hb

/-- `openWithSX_ct`, for a call that writes only what `vg_ghash` does. -/
theorem openWithS_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 2 ∨ w = 3)
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
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb : ∀ {σ : State}, pre σ → TbForO tb (σ.gpr .x0) (stackArg σ w) σ.sp (σ.gpr .x6) (σ.gpr .x7).toNat σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithS v.callees (8 * w) tb cl) :=
  openWithSX_ct v cl hMK gh hw hpre (ex := fun _ => []) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => rfl) (fun p c y z r w sp f _ => hgh p c y z r w sp f)
    (fun p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel p₁ p₂ hq c₁ c₂ y z sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
    htb htbrel

/-- `powTbl` then the decryption, in two runs that agree on the arguments. -/
theorem powTblDec_rel {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) (hr : ∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) :
    RelCT isa (Eq2 v₁ v₂) (.seq (.block Impl.AesGcm.AArch64.Stitch.powTbl) Impl.Gcm.AArch64.Stitch.dec) TT :=
  rel_taint stRegs hsp hr ⟨_, by taint_decide⟩

/-- `vg_aes_gcm_open` with the interleaved path for TLS records is constant time. -/
theorem openS_ct (v : GcmImpl) (hMK : MulKey) (hP : PrepPow) (gh : Gh8Ok) :
    ConstantTime isa openAArch64.pre openAArch64.pub (Impl.AesGcm.AArch64.Stitch.«open» v.callees) :=
  openWithS_ct (w := 2) v _ hMK gh (.inl rfl) (fun _ h => openPreX_W (extra := []) h)
    (fun _ hc _ _ _ _ _ _ => gh_call v.gh hc)
    (fun _ _ _ c₁ c₂ _ _ sp₁ sp₂ _ _ _ _ _ _ => rel_gh v.gh c₁ c₂ (sp₁.trans sp₂.symm))
    (fun {σ} _ => powTbl_forO hP _ _ _ _ _ σ)
    fun _ _ _ _ _ sp₁ sp₂ hr _ _ _ _ _ _ => powTblDec_rel (sp₁.trans sp₂.symm) hr

end VG.Proof.AesGcm.AArch64.Fast
