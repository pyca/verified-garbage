module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenB
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.PadT
import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.PadT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenB
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64, interleaved: `openWithS` is constant time

Untrusted: everything here is checked by Lean. As `Fast/OpenCT.lean` does
for `openRunWithPG`: the code between the calls by the taint analysis, the
interleaved loop and its table by `stitched_rel`, the calls by a hypothesis
on the hash's call and `rel_ctr`, and the branch on the tag (`omBS_rel`),
which both runs take the same way, by the taint analysis, the counter mode
(`cryptAlT_rel`, out of place `cryptAlG_rel`) and out of place `wipeTo_rel`;
in place or out of place (`to`).
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

/-- After `front` and `decPre`: what the interleaved loop needs, from the
text at `D` to the output at `O`. -/
theorem openDec_ok {H : Block} {to : Bool} {O : Addr} {s₀ t s₂ s₂c : State} {tb : List Instr}
    (o : OpenInG to Ctx W SP Np A D O Tg R 12 al n tl s₀ t)
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem Np 12) (bytesAt t.mem A al) D n t s₂)
    (fcb : Frame (cbF to W) s₂.mem s₂c.mem) (g₂c : ∀ r, r ≠ .x15 → s₂c.gpr r = s₂.gpr r)
    (x15₂c : cond to (s₂c.gpr .x15 = O) True) (sp₂c : s₂c.sp = s₂.sp) (rd₂c : s₂c.rd = s₂.rd)
    (wr₂c : s₂c.wr = s₂.wr)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t.rd → u.wr = t.wr →
      Frame [workR W, ⟨O, n⟩] t.mem u.mem → KeyAt H u.mem W → WP isa (.block tb) u (Stitch.TblPost W H u)) :
    Stitch.SInM Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length))
        (inc32 (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) R D O n to s₂c ∧
      Stitch.TbOk Ctx (W + BitVec.ofNat 64 16) W SP H tb s₂c ∧
      Frame [workR W, ⟨O, n⟩] t.mem s₂c.mem ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂c := by
  have L := o.lay
  have he₂c : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂c := h₂.env.keep (fun r hr => g₂c r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂c rd₂c wr₂c
  have F₂c : Frame [workR W, ⟨O, n⟩] t.mem s₂c.mem :=
    (h₂.frame.sub fun r hr => ⟨_, List.mem_cons_self .., frontFrame'_work W r hr⟩).trans
      (fcb.sub fun r hr => have ⟨r', h, hs⟩ := cbF_sub r hr
        ⟨_, List.mem_cons_self .., fun x hx => sfr_work to W r' h x (hs x hx)⟩)
  have key₂c : KeyAt H s₂c.mem W := h₂.key.frame fcb (cbF_disj (L.w_w (.inl (by decide)) (by decide) (by decide)))
  have hH₂c : blockAt s₂c.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fcb (cbF_disj (((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right
      (Lay.wSub (by decide))))), h₂.hH]
  have hmode : cond to (s₂c.gpr .x15 = O ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (O = D) := by
    cases to
    · exact o.out
    · exact ⟨x15₂c, (o.out : OutIn Ctx W D O n t).dd⟩
  refine ⟨⟨he₂c, by rw [g₂c _ (by decide), h₂.x22, o.x22], o.rounds, by rw [g₂c _ (by decide), h₂.x23],
    by rw [g₂c _ (by decide), h₂.x26], (dataOk_of o.dat).of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr]),
    o.outW.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr]), hmode, hH₂c,
    by rw [blockAt_frame fcb (cbF_disj (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩))),
      h₂.cb],
    by rw [blockAt_frame fcb (cbF_disj (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩))),
      h₂.y], ?_⟩, fun u heu hm' hrd hwr _ => htb u heu (by rw [hrd, rd₂c, h₂.rd]) (by rw [hwr, wr₂c, h₂.wr])
      (by rw [hm']; exact F₂c) (by rw [hm']; exact key₂c), F₂c, he₂c⟩
  rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _

/-- The pointers of the rest and the arguments of the call on its whole
blocks, after the interleaved loop: `MidG`, and `Abs3`. -/
theorem openBlk_ok {H : Block} {to : Bool} {O : Addr} {s₀ t s₂ s₂c s₂' : State} {x : List Byte} {icb : Block}
    (o : OpenInG to Ctx W SP Np A D O Tg R 12 al n tl s₀ t)
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem Np 12) (bytesAt t.mem A al) D n t s₂)
    (g₂c : ∀ r, r ≠ .x15 → s₂c.gpr r = s₂.gpr r) (rd₂c : s₂c.rd = s₂.rd) (wr₂c : s₂c.wr = s₂.wr)
    (F₂c : Frame [workR W, ⟨O, n⟩] t.mem s₂c.mem)
    (hm : Stitch.SMid Ctx (W + BitVec.ofNat 64 16) W SP H x icb R D O n (fun _ => bytesAt s₂c.mem D (Stitch.pre n))
      s₂c s₂') (hin : Stitch.SInM Ctx (W + BitVec.ofNat 64 16) W SP H x icb R D O n to s₂c)
    (key₂c : KeyAt H s₂c.mem W) :
    WP isa (.block (Impl.AesGcm.AArch64.Stitch.whole ++ ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr) ++
        absSeg2 16)) s₂' fun s₆ => ∃ s₃ : State, ∃ X : Addr,
      MidG to Ctx W SP H R n D (BitVec.ofNat 64 tl) X s₃ s₃ ∧ Frame [workR W, ⟨O, n⟩] t.mem s₃.mem ∧
      s₃.rd = t.rd ∧ s₃.wr = t.wr ∧
      Abs3 Ctx (W + BitVec.ofNat 64 16) W SP s₃.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n)
        0 s₃.mem 0 s₆ ∧ s₆.rd = s₃.rd ∧ s₆.wr = s₃.wr := by
  have L := o.lay
  have hdk := dataOk_of o.dat
  have hn := hdk.lt
  have ow := o.outW
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  have g₂' : ∀ r ∈ [Reg.x19, .x22, .x23, .x26, .x27, .x28], s₂'.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hm.gpr _ (by decide), g₂c _ (by decide)]
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, x23₃, x24₃, x25₃, r₃⟩ := Stitch.afterD_ok (u := s₂') (D := D) (n := n)
    (by rw [g₂' _ (by simp), h₂.x23]) (by rw [g₂' _ (by simp), h₂.x26]) hn
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := hm.env.of_regs r₃
  have hd₃ : cond to (DataOk (W + BitVec.ofNat 64 16) W s₃ D n) (DataW Ctx (W + BitVec.ofNat 64 16) W s₃ D n) :=
    data_of_eq o.dat (by rw [r₃.rd, hm.rd, rd₂c, h₂.rd]) (by rw [r₃.wr, hm.wr, wr₂c, h₂.wr])
  have dOP : (⟨O, Stitch.pre n⟩ : Region).Disjoint (workR W) := ow.ok.w.sub_left (Region.sub_prefix hpn)
  have dS : ∀ {R' : Region}, R'.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ →
      R'.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ → R'.Disjoint ⟨O, Stitch.pre n⟩ →
      R'.Disjoint (Stitch.tblR W) → ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W O n, R'.Disjoint r :=
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
      ((ow.ctx.sub_left (Lay.ctxSub (by decide))).sub_right (Region.sub_prefix hpn))
      ((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.wSub (by decide)))), hin.hH]
  have key₃ : KeyAt H s₃.mem W := by
    rw [r₃.mem]
    exact key₂c.frame hm.frame (dS (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      (dOP.sub_right (Lay.wSub (by decide))).symm
      (Offset.disjoint W (.inl (by decide)) (by decide) (by decide)))
  have F₃ : Frame [workR W, ⟨O, n⟩] t.mem s₃.mem := by
    rw [r₃.mem]
    refine F₂c.trans (hm.frame.sub fun r hr => ?_)
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix hpn⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₃.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n))
      (n - Stitch.pre n) 0 s₃.mem 0 s₃ :=
    ⟨he₃, fun _ _ => rfl, Nat.zero_le _, by rw [x23₃]; simp, by rw [x24₃, Nat.sub_zero], x25₃,
      (dataOk_of hd₃).drop hpn, hH₃, fun ha => by simpa [bytesAt] using ha, .inr rfl, Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  have k : ∀ r ∈ [Reg.x22, .x26, .x28], s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [r₃.others _ (by decide), g₂' _ (by simp)]
  exact ⟨s₃, s₃.gpr .x27, ⟨he₃, by rw [k _ (by simp), h₂.x22, o.x22], o.rounds, by rw [k _ (by simp), h₂.x26], rfl,
    by rw [k _ (by simp), h₂.x28, o.x28], hH₃, key₃, hd₃, Frame.refl _ _, rfl, rfl⟩, F₃,
    by rw [r₃.rd, hm.rd, rd₂c, h₂.rd], by rw [r₃.wr, hm.wr, wr₂c, h₂.wr], h₆, rd₆, wr₆⟩

/-- `openRunAS` in two runs from the same public arguments: in place, or out
of place (`to`) from the text at `D` to the output at `O`. -/
theorem openRunAS_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr}
    {to : Bool} {O : Addr} {s₀₁ s₀₂ t₁ t₂ : State}
    {ex : List Region} (hexW : ∀ r ∈ ex, (workR W).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (o₁ : OpenInG to Ctx W SP Np A D O Tg R 12 al n tl s₀₁ t₁) (o₂ : OpenInG to Ctx W SP Np A D O Tg R 12 al n tl s₀₂ t₂)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = D ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = D ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (hal : al ≤ 16)
    (hgh₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₁.rd → s'.wr = t₁.wr → s'.sp = SP → Frame [workR W, ⟨O, n⟩] t₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hgh₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₂.rd → s'.wr = t₂.wr → s'.sp = SP → Frame [workR W, ⟨O, n⟩] t₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hrel : ∀ {s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) → s₁.sp = SP → s₂.sp = SP →
      s₁.rd = t₁.rd → s₁.wr = t₁.wr → Frame [workR W, ⟨O, n⟩] t₁.mem s₁.mem →
      s₂.rd = t₂.rd → s₂.wr = t₂.wr → Frame [workR W, ⟨O, n⟩] t₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₁.rd → u.wr = t₁.wr →
      Frame [workR W, ⟨O, n⟩] t₁.mem u.mem → KeyAt (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u))
    (htb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₂.rd → u.wr = t₂.wr →
      Frame [workR W, ⟨O, n⟩] t₂.mem u.mem → KeyAt (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u))
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      (to = true → v₁.gpr .x15 = v₂.gpr .x15) →
      v₁.rd = t₁.rd → v₁.wr = t₁.wr → Frame [workR W, ⟨O, n⟩] t₁.mem v₁.mem →
      v₂.rd = t₂.rd → v₂.wr = t₂.wr → Frame [workR W, ⟨O, n⟩] t₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec to)) TT) :
    RelCT isa (Eq2 t₁ t₂) (openRunAS v.callees cl tb to) TT := by
  have L := o₁.lay
  have hn := (dataOk_of o₁.dat).lt
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
    (front_ok (D := D) L hMK hJ₁ o₁.aad hal x4₁ x5₁ x6₁ x7₁) (front_ok (D := D) L hMK hJ₂ o₂.aad hal x4₂ x5₂ x6₂ x7₂)
    fun s₂ u₂ h₂ k₂ => ?_
  -- `decPre`, in each run.
  have sOf : ∀ {s₀ t s : State}, OpenInG to Ctx W SP Np A D O Tg R 12 al n tl s₀ t →
      Frame (frontFrame' (W + BitVec.ofNat 64 16) W) t.mem s.mem →
      cond to (s.mem.readW (W + BitVec.ofNat 64 320) 64 = O) True := fun {s₀ t s} o f => by
    cases to with
    | false => trivial
    | true =>
      show _ = _
      rw [f.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with (rfl | rfl | rfl) | rfl
          · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
          · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
          · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
          · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)) (by decide)]
      exact (o.out : OutIn Ctx W D O n t).sO
  obtain ⟨s₂c, run₂c, fcb, g₂c, x15₂c, sp₂c, rd₂c, wr₂c, -⟩ := decPre_ok (to := to) (O := O) h₂.env h₂.cb
    (sOf o₁ h₂.frame)
  obtain ⟨u₂c, run₂c', fcb', g₂c', x15₂c', sp₂c', rd₂c', wr₂c', -⟩ := decPre_ok (to := to) (O := O) k₂.env k₂.cb
    (sOf o₂ k₂.frame)
  have tdp : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block (Impl.AesGcm.AArch64.Stitch.decPre to)) h).isSome =
      true := by
    cases to <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.x19, .x20] (by rw [h₂.env.sp, k₂.env.sp])
      (by agree_tac [h₂.env.x19, k₂.env.x19, h₂.env.x20, k₂.env.x20]) tdp)
    (F₁ := fun s => s = s₂c) (F₂ := fun s => s = u₂c)
    (WP.of_runBlock ⟨s₂c, run₂c, rfl⟩) (WP.of_runBlock ⟨u₂c, run₂c', rfl⟩) fun a₁ a₂ e₁ e₂ => ?_
  subst a₁ a₂
  obtain ⟨I₁, T₁, F₁, he₁⟩ := openDec_ok o₁ h₂ fcb g₂c x15₂c sp₂c rd₂c wr₂c htb₁
  obtain ⟨I₂, T₂, F₂, he₂⟩ := openDec_ok o₂ k₂ fcb' g₂c' x15₂c' sp₂c' rd₂c' wr₂c' htb₂
  have key₁ := h₂.key.frame fcb (cbF_disj (L.w_w (.inl (by decide)) (by decide) (by decide)))
  have key₂ := k₂.key.frame fcb' (cbF_disj (L.w_w (.inl (by decide)) (by decide) (by decide)))
  -- The interleaved loop.
  have regs : ∀ r ∈ stRegs, r ≠ .x9 → s₂c.gpr r = u₂c.gpr r := by
    intro r hr h9
    simp only [stRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h9
    · rw [I₁.env.x19, I₂.env.x19]
    · rw [I₁.env.x20, I₂.env.x20]
    · rw [I₁.env.x21, I₂.env.x21]
    · rw [I₁.x22, I₂.x22]
    · rw [I₁.x23, I₂.x23]
    · rw [I₁.x26, I₂.x26]
  refine rel_seq (stitched_rel (by rw [he₁.sp, he₂.sp]) regs I₁.x26 hn
      fun v₁ v₂ hsp' hr' g₁ m₁ r₁ w₁ sp₁ g₂ m₂ r₂ w₂ sp₂ => htbrel v₁ v₂ (by rw [sp₁, he₁.sp])
        (by rw [sp₂, he₂.sp]) hr' (fun hto => by
          subst hto
          rw [g₁ .x15 (by decide), g₂ .x15 (by decide), (I₁.mode : _ ∧ _).1, (I₂.mode : _ ∧ _).1])
        (by rw [r₁, rd₂c, h₂.rd]) (by rw [w₁, wr₂c, h₂.wr]) (by rw [m₁]; exact F₁)
        (by rw [r₂, rd₂c', k₂.rd]) (by rw [w₂, wr₂c', k₂.wr]) (by rw [m₂]; exact F₂))
    (Stitch.stitchDM_ok L gh T₁ I₁) (Stitch.stitchDM_ok L gh T₂ I₂) fun s₃ u₃ m₁ m₂ => ?_
  have x23₁ : s₃.gpr .x23 = D := by rw [m₁.gpr _ (by decide), I₁.x23]
  have x23₂ : u₃.gpr .x23 = D := by rw [m₂.gpr _ (by decide), I₂.x23]
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x26] (by rw [m₁.env.sp, m₂.env.sp])
      (by agree_tac [m₁.env.x19, m₂.env.x19, m₁.env.x20, m₂.env.x20, m₁.env.x21, m₂.env.x21,
        x23₁, x23₂, m₁.gpr .x26 (by decide), m₂.gpr .x26 (by decide), I₁.x26, I₂.x26]) ⟨_, by taint_decide⟩)
    (openBlk_ok o₁ h₂ g₂c rd₂c wr₂c F₁ m₁ I₁ key₁) (openBlk_ok o₂ k₂ g₂c' rd₂c' wr₂c' F₂ m₂ I₂ key₂)
    fun u₁ u₂ ⟨q₁, X₁, M₁, fr₁', rd₁', wr₁', a₁, rd₁, wr₁⟩ ⟨q₂, X₂, M₂, fr₂', rd₂', wr₂', a₂, rd₂, wr₂⟩ => ?_
  have fr₁ : Frame [workR W, ⟨O, n⟩] t₁.mem u₁.mem := fr₁'.trans (absFrame_wd a₁.frame)
  have fr₂ : Frame [workR W, ⟨O, n⟩] t₂.mem u₂.mem := fr₂'.trans (absFrame_wd a₂.frame)
  have r₁ : u₁.rd = t₁.rd := rd₁.trans rd₁'
  have w₁ : u₁.wr = t₁.wr := wr₁.trans wr₁'
  have r₂ : u₂.rd = t₂.rd := rd₂.trans rd₂'
  have w₂ : u₂.wr = t₂.wr := wr₂.trans wr₂'
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
    (ctE'_ok L hMK (.inr rfl) N₁ b₁ l₁ (by rw [show n - (n - Stitch.pre n) = Stitch.pre n by omega]) (by omega))
    (ctE'_ok L hMK (.inr rfl) N₂ b₂ l₂ (by rw [show n - (n - Stitch.pre n) = Stitch.pre n by omega]) (by omega))
    fun s₁₆ t₁₆ ⟨_, _, _, _, T₁, k28₁⟩ ⟨_, _, _, _, T₂, k28₂⟩ => ?_)
  refine rel_seq (rel_ctr v.ctr T₁.call T₂.call (by rw [T₁.env.sp, T₂.env.sp]))
    (tagCall_ok L v (.inr rfl) T₁) (tagCall_ok L v (.inr rfl) T₂) fun s₁₇ t₁₇ O₁ O₂ => ?_
  exact rel_taint [.x19, .x28] (by rw [O₁.env.sp, O₂.env.sp])
    (by agree_tac [O₁.env.x19, O₂.env.x19, O₁.kept .x28 (by decide), O₂.kept .x28 (by decide), k28₁, k28₂])
    ⟨_, by taint_decide⟩

end

section
variable {Ctx W SP D O Np A : Addr} {R nl al n tl P : Nat} {C₁ C₂ C₁' C₂' : List Byte}

/-- The arguments of `failS`'s `cryptAl`, in place: the first `P` bytes, from
the kept counter block. -/
theorem failCr_ok {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidSG false fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    ∃ s₈, runBlock isa (([.ldrq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO, .strq .v0 .x20 48,
      .ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      [mov .x24 .x9, imm .x25 0]) s₇ = some s₈ ∧
      CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D P s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
        s₈.gpr .x26 = BitVec.ofNat 64 n := by
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W s₇ D n := mo.data
  obtain ⟨s₈, run₈, _, x23₈, x24₈, x25₈, x26₈, og₈, sp₈, rd₈, wr₈⟩ := failArgs_ok mo
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := mo.env.keep (fun r hr => og₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  exact ⟨s₈, run₈, ⟨he₈, fun _ _ => rfl, by rw [og₈ _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
    (hdw.take hPn).of_eq rd₈ wr₈, rfl⟩, og₈ _ (by decide), x26₈⟩

/-- The arguments of `okS`'s counter mode: the rest, from the text to the
output past the first `P` bytes. -/
theorem okCrG_ok (to : Bool) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidSG to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    ∃ s₈, runBlock isa (([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++
      Impl.AesGcm.AArch64.Stitch.whole ++ ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr) ++
      cond to ([.ldr .x .x26 .x19 dstO, .add .x .x26 .x26 .x9] : List Instr) []) s₇ = some s₈ ∧
      CrInG to Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R P (D + BitVec.ofNat 64 P) (O + BitVec.ofNat 64 P) (n - P)
        s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧ (to = false → s₈.gpr .x26 = BitVec.ofNat 64 n) ∧ s₈.wr = s₇.wr := by
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  have subR : ∀ E : Addr, Region.Sub ⟨E + BitVec.ofNat 64 P, n - P⟩ ⟨E, n⟩ := fun E => Offset.sub_base E (by
    have := mo.dataOk.wrap; omega)
  obtain ⟨s₈, run₈, x23₈, x24₈, x25₈, x26₈, r₈⟩ := okArgsG_ok to mo
  refine ⟨s₈, run₈, ⟨mo.env.of_regs r₈, ?_, by rw [r₈.others _ (by decide), mo.x22], hR, x23₈, x24₈,
    x25₈, data_of_eq ?_ r₈.rd r₈.wr, ?_⟩, r₈.others _ (by decide), ?_, r₈.wr⟩
  · cases to
    · exact fun _ _ => rfl
    · exact (fun _ _ => rfl : KeptTo s₈.gpr s₈)
  · cases to
    · exact (show DataW Ctx (W + BitVec.ofNat 64 16) W s₇ D n from mo.data).drop hPn
    · exact (show DataOk (W + BitVec.ofNat 64 16) W s₇ D n from mo.data).drop hPn
  · cases to
    · have e : O = D := mo.out
      subst e
      rfl
    · have ou : OutIn Ctx W D O n s₇ := mo.out
      exact OutAt.mkTo ((ou.dw.drop hPn).of_eq r₈.rd r₈.wr) ((ou.dd.sub_left (subR D)).sub_right (subR O))
        (by rw [show s₈.gpr .x26 = O + BitVec.ofNat 64 P from x26₈, BitVec.add_zero])
  · intro hto
    subst hto
    exact x26₈

/-- `omBS to` in two runs whose tags compare alike. -/
theorem omBS_rel (v : GcmImpl) (to : Bool) (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr fr' : List Region}
    {s s' m₁ m₂ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo₁ : MidSG to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s m₁)
    (mo₂ : MidSG to fr' Ctx W SP D O Np A R nl al n tl P C₁' C₂' s' m₂)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (omBS v.callees to) TT := by
  have hP16 : P % 16 = 0 := by rw [mo₁.hP]; omega
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  have ite_ok : ∀ {fr : List Region} {C₁ C₂ : List Byte} {s m : State},
      MidSG to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s m →
      WP isa (.ite (.zero .x .x27) (Impl.AesGcm.AArch64.Stitch.failS v.callees to)
        (Impl.AesGcm.AArch64.Stitch.okS v.callees to)) m fun u => u.sp = SP ∧
        u.gpr .x27 = m.gpr .x27 := fun {fr C₁ C₂ s m} mo => by
    have hn := mo.dataOk.lt
    refine WP.ite _ (eval_zero mo.x27 (hlt _)) (fun _ => ?_) (fun _ => ?_)
    · cases to with
      | false =>
        have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W m D n := mo.data
        obtain ⟨s₈, run₈, hc, k27, k26⟩ := failCr_ok hR mo
        exact WP.seq (WP.of_runBlock ⟨s₈, run₈, WP.mono (cryptAlT_ok L v (icb := 0) hc rfl k26 hn
          fun _ h => absurd hP16 h) fun s₉ h₉ =>
          ⟨h₉.env.sp, by rw [h₉.kept .x27 (by decide), k27]⟩⟩)
      | true =>
        have ou : OutIn Ctx W D O n m := mo.out
        exact WP.mono (wipeTo_ok mo.env ou.sO mo.sN ou.dw) fun s₉ ⟨_, _, g, sp, _, _⟩ =>
          ⟨sp.trans mo.env.sp, g _ (by decide) (by decide) (by decide)⟩
    · obtain ⟨s₈, run₈, hc, k27, k26, kw⟩ := okCrG_ok to hR mo
      unfold Impl.AesGcm.AArch64.Stitch.okS
      refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
      cases to with
      | false =>
        have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W m D n := mo.data
        have eO : O = D := mo.out
        subst eO
        exact WP.mono (cryptAlT_ok L v (icb := 0) hc hP16 (k26 rfl) hn
          (tail_big (by rw [kw]; exact hdw.wr) hn rfl (by have := mo.hP; omega))) fun s₉ h₉ =>
          ⟨h₉.env.sp, by rw [h₉.kept .x27 (by decide), k27]⟩
      | true =>
        exact WP.mono (cryptAlG_ok L v true (icb := 0) hc hP16) fun s₉ h₉ =>
          ⟨h₉.env.sp, by rw [keptG_x27 h₉.kept, k27]⟩
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  unfold omBS
  refine rel_seq ?_ (ite_ok mo₁) (ite_ok mo₂) fun a b ⟨ea, xa⟩ ⟨eb, xb⟩ =>
    rel_taint [.x27] (by rw [ea, eb]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · cases to with
    | false =>
      obtain ⟨s₈, run₈, hc₁, -, k₁⟩ := failCr_ok hR mo₁
      obtain ⟨t₈, run₈', hc₂, -, k₂⟩ := failCr_ok hR mo₂
      simp only [Impl.AesGcm.AArch64.Stitch.failS, Bool.cond_false]
      refine rel_seq (rel_taint [.x19, .x20] (by rw [mo₁.env.sp, mo₂.env.sp])
          (by agree_tac [mo₁.env.x19, mo₂.env.x19, mo₁.env.x20, mo₂.env.x20]) ⟨_, by taint_decide⟩)
        (F₁ := fun u => u = s₈) (F₂ := fun u => u = t₈)
        (WP.of_runBlock ⟨s₈, run₈, rfl⟩) (WP.of_runBlock ⟨t₈, run₈', rfl⟩) fun _ _ e₁ e₂ => ?_
      subst e₁ e₂
      exact cryptAlT_rel L v hc₁ hc₂ rfl (by rw [k₁, k₂])
    | true =>
      have ou₁ : OutIn Ctx W D O n m₁ := mo₁.out
      have ou₂ : OutIn Ctx W D O n m₂ := mo₂.out
      exact wipeTo_rel mo₁.env mo₂.env ou₁.sO ou₂.sO mo₁.sN mo₂.sN
  · obtain ⟨s₈, run₈, hc₁, -, k₁, -⟩ := okCrG_ok to hR mo₁
    obtain ⟨t₈, run₈', hc₂, -, k₂, -⟩ := okCrG_ok to hR mo₂
    unfold Impl.AesGcm.AArch64.Stitch.okS
    have tok : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block (([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] :
        List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
        ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr) ++
        cond to ([.ldr .x .x26 .x19 dstO, .add .x .x26 .x26 .x9] : List Instr) [])) h).isSome = true := by
      cases to <;> exact ⟨_, by taint_decide⟩
    refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp])
        (by agree_tac [mo₁.env.x19, mo₂.env.x19]) tok)
      (F₁ := fun u => u = s₈) (F₂ := fun u => u = t₈)
      (WP.of_runBlock ⟨s₈, run₈, rfl⟩) (WP.of_runBlock ⟨t₈, run₈', rfl⟩) fun _ _ e₁ e₂ => ?_
    subst e₁ e₂
    cases to with
    | false =>
      have e₁ : O = D := mo₁.out
      subst e₁
      exact cryptAlT_rel L v hc₁ hc₂ hP16 (by rw [k₁ rfl, k₂ rfl])
    | true => exact cryptAlG_rel L v true hc₁ hc₂ hP16

end

section
variable {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `openRunWithSG` in two runs, after `tagIn`, whose tags compare alike: in
place, or out of place (`to`) from the text at `D` to the output at `O`. -/
theorem openRunWithS_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {nl : Nat}
    {to : Bool} {O : Addr} {s₀₁ s₀₂ t₁ t₂ : State}
    {ex : List Region} (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexO : ∀ r ∈ ex, (⟨O, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (o₁ : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀₁ t₁)
    (o₂ : OpenInG to Ctx W SP Np A D O Tg R nl al n tl s₀₂ t₂)
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
      s'.rd = s₀₁.rd → s'.wr = s₀₁.wr → s'.sp = SP → Frame [workR W, ⟨O, n⟩] s₀₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hgh₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀₂.rd → s'.wr = s₀₂.wr → s'.sp = SP → Frame [workR W, ⟨O, n⟩] s₀₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex)
    (hrel : ∀ {s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, GhCall s₁ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) → s₁.sp = SP → s₂.sp = SP →
      s₁.rd = s₀₁.rd → s₁.wr = s₀₁.wr → Frame [workR W, ⟨O, n⟩] s₀₁.mem s₁.mem →
      s₂.rd = s₀₂.rd → s₂.wr = s₀₂.wr → Frame [workR W, ⟨O, n⟩] s₀₂.mem s₂.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb₁ : TbForO tb Ctx W SP O n s₀₁) (htb₂ : TbForO tb Ctx W SP O n s₀₂)
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      (to = true → v₁.gpr .x15 = v₂.gpr .x15) →
      v₁.rd = s₀₁.rd → v₁.wr = s₀₁.wr → Frame [workR W, ⟨O, n⟩] s₀₁.mem v₁.mem →
      v₂.rd = s₀₂.rd → v₂.wr = s₀₂.wr → Frame [workR W, ⟨O, n⟩] s₀₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec to)) TT) :
    RelCT isa (Eq2 t₁ t₂) (Impl.AesGcm.AArch64.Stitch.openRunWithSG v.callees to tb cl) TT := by
  subst h12
  have L := o₁.lay
  have F₁ : Frame [workR W, ⟨O, n⟩] s₀₁.mem t₁.mem :=
    o₁.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entryFr_work to W r hr⟩
  have F₂ : Frame [workR W, ⟨O, n⟩] s₀₂.mem t₂.mem :=
    o₂.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entryFr_work to W r hr⟩
  have hH₁ := o₁.vals.2.1
  have hH₂ := o₂.vals.2.1
  have g₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₁.rd → s'.wr = t₁.wr → s'.sp = SP → Frame [workR W, ⟨O, n⟩] t₁.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex :=
    fun s' _ _ _ _ hc sY sS hr hw hsp hf hd =>
      hgh₁ s' hc sY sS (hr.trans o₁.rd₀) (hw.trans o₁.wr₀) hsp (F₁.trans hf) hd
  have g₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t₂.rd → s'.wr = t₂.wr → s'.sp = SP → Frame [workR W, ⟨O, n⟩] t₂.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex :=
    fun s' _ _ _ _ hc sY sS hr hw hsp hf hd =>
      hgh₂ s' hc sY sS (hr.trans o₂.rd₀) (hw.trans o₂.wr₀) hsp (F₂.trans hf) hd
  have tb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₁.rd → u.wr = t₁.wr →
      Frame [workR W, ⟨O, n⟩] t₁.mem u.mem → KeyAt (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₁.mem (Ctx + BitVec.ofNat 64 240)) u) :=
    fun u he hrd hwr hf key => by
      rw [hH₁] at key ⊢; exact htb₁ u he (hrd.trans o₁.rd₀) (hwr.trans o₁.wr₀) (F₁.trans hf) key
  have tb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t₂.rd → u.wr = t₂.wr →
      Frame [workR W, ⟨O, n⟩] t₂.mem u.mem → KeyAt (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u (Stitch.TblPost W (blockAt t₂.mem (Ctx + BitVec.ofNat 64 240)) u) :=
    fun u he hrd hwr hf key => by
      rw [hH₂] at key ⊢; exact htb₂ u he (hrd.trans o₂.rd₀) (hwr.trans o₂.wr₀) (F₂.trans hf) key
  refine (openRunWithS_split v.callees cl tb to).symm.rel (rel_seq
    (openRunAS_relX v cl hMK gh hexW hexC o₁ o₂ hx₁ hx₂ hal g₁ g₂
      (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd =>
        hrel c₁ c₂ sY sS sp₁ sp₂ (r₁.trans o₁.rd₀) (w₁.trans o₁.wr₀) (F₁.trans f₁) (r₂.trans o₂.rd₀)
          (w₂.trans o₂.wr₀) (F₂.trans f₂) hd) tb₁ tb₂
      (fun v₁ v₂ sp₁ sp₂ hr h15 r₁ w₁ f₁ r₂ w₂ f₂ => htbrel v₁ v₂ sp₁ sp₂ hr h15 (r₁.trans o₁.rd₀)
        (w₁.trans o₁.wr₀) (F₁.trans f₁) (r₂.trans o₂.rd₀) (w₂.trans o₂.wr₀) (F₂.trans f₂)))
    (WP.mono (openRunASX_ok cl v hMK gh (I := fun _ => True) o₁ hx₁.1 hx₁.2.1 hx₁.2.2.1 hx₁.2.2.2 hal hok
      hexW hexD hexO hexC (fun _ _ => trivial) (fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₁ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) tb₁) fun _ q => q.1)
    (WP.mono (openRunASX_ok cl v hMK gh (I := fun _ => True) o₂ hx₂.1 hx₂.2.1 hx₂.2.2.1 hx₂.2.2.2 hal hok
      hexW hexD hexO hexC (fun _ _ => trivial) (fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₂ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) tb₂) fun _ q => q.1) fun m₁ m₂ mo₁ mo₂ => ?_)
  refine omBS_rel v to L o₁.rounds mo₁ mo₂ ?_
  have hCs : ∀ m : Mem, bytesAt m D (Stitch.pre n) ++
      bytesAt m (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n) = bytesAt m D n := fun m => by
    rw [← bytesAt_add, Nat.add_sub_cancel' (Nat.mul_div_le n 128)]
  rw [mo₁.x27, mo₂.x27, hCs, hCs, tagBit o₁ rt₁ hok, tagBit o₂ rt₂ hok, hb]

end

end VG.Proof.AesGcm.AArch64.Fast
