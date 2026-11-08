module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenB
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
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

/-- After `front` and keeping the first counter block: the first bytes of the
ciphertext at `S`, decrypted to the text at `D` (`decPart`). -/
theorem openDec_ok {H : Block} {s₀ t s₂ s₂c : State} {tb : List Instr} {to : Bool} {S : Addr}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem Np 12) (bytesAt t.mem A al) S n t s₂)
    (m₂c : s₂c.mem = s₂.mem.write (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) 16
      (s₂.mem.read (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16))
    (g₂c : s₂c.gpr = s₂.gpr) (sp₂c : s₂c.sp = s₂.sp) (rd₂c : s₂c.rd = s₂.rd) (wr₂c : s₂c.wr = s₂.wr)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t.rd → u.wr = t.wr →
      Frame [workR W, ⟨D, n⟩] t.mem u.mem → KeyAt H u.mem W → WP isa (.block tb) u (Stitch.TblPost W H u))
    (hsrc : DataOk (W + BitVec.ofNat 64 16) W t S n)
    (hm : cond to ((⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (S = D)) :
    Stitch.DecIn Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length))
        (inc32 (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) R S D n to tb s₂c ∧
      Frame [workR W, ⟨D, n⟩] t.mem s₂c.mem ∧ KeyAt H s₂c.mem W ∧
      blockAt s₂c.mem (Ctx + BitVec.ofNat 64 240) = H ∧ s₂c.mem.readW (W + BitVec.ofNat 64 232) 64 = D ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂c := by
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
  have hH₂c : blockAt s₂c.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fcb (dcbR ((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right
      (Lay.wSub (by decide))).symm), h₂.hH]
  have hsl₂c : s₂c.mem.readW (W + BitVec.ofNat 64 232) 64 = D := by
    rw [slot_kept fcb (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide) (by decide),
      slot_kept h₂.frame (slots_frontFrame' L) (by decide) (by decide), o.sD]
  have hTb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₂c.rd → u.wr = s₂c.wr →
      Frame [⟨D, n⟩] s₂c.mem u.mem → Stitch.TbOk Ctx (W + BitVec.ofNat 64 16) W SP H tb u :=
    fun u₀ _ hrd₀ hwr₀ hf₀ u heu hm' hrd hwr _ => htb u heu (by rw [hrd, hrd₀, rd₂c, h₂.rd])
      (by rw [hwr, hwr₀, wr₂c, h₂.wr]) (by rw [hm']; exact F₂c.trans (hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩))
      (by rw [hm']; exact key₂c.frame hf₀ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (o.ddW.sub_right (Lay.wSub (by decide))).symm))
  refine ⟨⟨hTb, he₂c, by rw [g₂c, h₂.x22, o.x22], o.rounds,
    by rw [g₂c, h₂.x23], by rw [g₂c, h₂.x26], hsrc.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr]),
    o.dat.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr]), hm, hsl₂c, hH₂c,
    by rw [blockAt_frame fcb (dcbR (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm),
      h₂.cb],
    by rw [blockAt_frame fcb (dcbR (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm),
      h₂.y], ?_⟩, F₂c, key₂c, hH₂c, hsl₂c, he₂c⟩
  rw [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _

/-- `decPart tb to` in two runs from states of `DecIn` with the same public
data: in place, `stitched_rel`; out of place, `tailTo`'s blocks by the taint
analysis, from the same arguments and the same text loaded from the slot,
then `stitched_rel`, and the text loaded again. -/
theorem decPart_rel (gh : Gh8Ok) {Ctx St W SP S D : Addr} {H₁ H₂ : Block} {x₁ x₂ : List Byte}
    {icb₁ icb₂ : Block} {R n : Nat} {to : Bool} {tb : List Instr} {u₁ u₂ : State} (L : Lay Ctx St W)
    (i₁ : Stitch.DecIn Ctx St W SP H₁ x₁ icb₁ R S D n to tb u₁)
    (i₂ : Stitch.DecIn Ctx St W SP H₂ x₂ icb₂ R S D n to tb u₂) (hsp : u₁.sp = u₂.sp)
    (hk : ∀ v₁ v₂ : State, v₁.sp = v₂.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      (to = true → v₁.gpr .x15 = v₂.gpr .x15) →
      v₁.rd = u₁.rd → v₁.wr = u₁.wr → Frame [⟨D, n⟩] u₁.mem v₁.mem → v₁.sp = u₁.sp →
      v₂.rd = u₂.rd → v₂.wr = u₂.wr → Frame [⟨D, n⟩] u₂.mem v₂.mem → v₂.sp = u₂.sp →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec to)) TT) :
    RelCT isa (Eq2 u₁ u₂) (Impl.AesGcm.AArch64.Stitch.decPart tb to) TT := by
  have hn := i₁.out.ok.lt
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  have regs : ∀ {a b : State}, Env Ctx St W SP a → Env Ctx St W SP b → a.gpr .x22 = BitVec.ofNat 64 R →
      b.gpr .x22 = BitVec.ofNat 64 R → a.gpr .x23 = S → b.gpr .x23 = S → a.gpr .x26 = BitVec.ofNat 64 n →
      b.gpr .x26 = BitVec.ofNat 64 n → ∀ r ∈ stRegs, r ≠ .x9 → a.gpr r = b.gpr r := by
    intro a b ea eb a22 b22 a23 b23 a26 b26 r hr h9
    simp only [stRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h9
    · rw [ea.x19, eb.x19]
    · rw [ea.x20, eb.x20]
    · rw [ea.x21, eb.x21]
    · rw [a22, b22]
    · rw [a23, b23]
    · rw [a26, b26]
  cases to with
  | false =>
    exact stitched_rel hsp (regs i₁.env i₂.env i₁.x22 i₂.x22 i₁.x23 i₂.x23 i₁.x26 i₂.x26) i₁.x26 hn
      fun v₁ v₂ hsp' hr' _ m₁ r₁ w₁ sp₁ _ m₂ r₂ w₂ sp₂ => hk v₁ v₂ hsp' hr' nofun r₁ w₁
        (by rw [m₁]; exact Frame.refl _ _) sp₁ r₂ w₂ (by rw [m₂]; exact Frame.refl _ _) sp₂
  | true =>
    have hSD : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩ := i₁.mode
    simp only [Impl.AesGcm.AArch64.Stitch.decPart, cond]
    have relA : RelCT isa (Eq2 u₁ u₂) Impl.AesGcm.AArch64.Stitch.tailTo TT := by
      unfold Impl.AesGcm.AArch64.Stitch.tailTo
      obtain ⟨a₁, run₁, x11₁, x12₁, x13₁, r₁⟩ := Stitch.tailArgs_run i₁.env i₁.x23 i₁.x26 hn i₁.slot
      obtain ⟨a₂, run₂, x11₂, x12₂, x13₂, r₂⟩ := Stitch.tailArgs_run i₂.env i₂.x23 i₂.x26 hn i₂.slot
      refine rel_seq (rel_taint [.x19, .x23, .x26] hsp
          (by agree_tac [i₁.env.x19, i₂.env.x19, i₁.x23, i₂.x23, i₁.x26, i₂.x26]) ⟨_, by taint_decide⟩)
        (F₁ := fun a => a = a₁) (F₂ := fun a => a = a₂) (WP.of_runBlock ⟨a₁, run₁, rfl⟩)
        (WP.of_runBlock ⟨a₂, run₂, rfl⟩) fun a₁' a₂' e₁ e₂ => ?_
      subst e₁ e₂
      have lp : ∀ {u a : State}, Stitch.DecIn Ctx St W SP H₁ x₁ icb₁ R S D n true tb u ∨
          Stitch.DecIn Ctx St W SP H₂ x₂ icb₂ R S D n true tb u → Regs [.x9, .x11, .x12, .x13] u a →
          LoopPre a (S + BitVec.ofNat 64 (Stitch.pre n)) (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n) := by
        intro u a hi r
        have hsrc : DataOk St W u S n := by rcases hi with hi | hi <;> exact hi.src
        have hout : DataW Ctx St W u D n := by rcases hi with hi | hi <;> exact hi.out
        exact ⟨by simp only [Stitch.pre]; omega, by rw [r.rd, r.wr]; exact (hsrc.drop hpn).rd,
          by rw [r.wr]; exact (hout.drop hpn).wr,
          (hSD.sub_left (Offset.sub_base S (by omega))).sub_right (Offset.sub_base D (by omega))⟩
      refine rel_seq (rel_taint [.x11, .x12, .x13] (by rw [r₁.sp, r₂.sp, hsp])
          (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩)
        (copy_ok a₁' x12₁ x11₁ x13₁ (lp (.inl i₁) r₁)) (copy_ok a₂' x12₂ x11₂ x13₂ (lp (.inr i₂) r₂))
        fun c₁ c₂ ⟨_, g₁, sp₁, _, _⟩ ⟨_, g₂, sp₂, _, _⟩ => ?_
      exact rel_taint [.x19] (by rw [sp₁, sp₂, r₁.sp, r₂.sp, hsp])
        (by agree_tac [g₁ .x19 (by decide), g₂ .x19 (by decide), r₁.others .x19 (by decide),
          r₂.others .x19 (by decide), i₁.env.x19, i₂.env.x19]) ⟨_, by taint_decide⟩
    refine rel_seq relA (Stitch.tailPre_ok i₁) (Stitch.tailPre_ok i₂) fun u₃ v₃ T₁ T₂ => ?_
    have m₁ := T₁.sin.mode
    have m₂ := T₂.sin.mode
    simp only [cond] at m₁ m₂
    refine rel_seq (stitched_rel (by rw [T₁.sp, T₂.sp, hsp])
        (regs T₁.sin.env T₂.sin.env T₁.sin.x22 T₂.sin.x22 T₁.sin.x23 T₂.sin.x23 T₁.sin.x26 T₂.sin.x26)
        T₁.sin.x26 hn fun w₁ w₂ hsp' hr' g₁ mm₁ rr₁ ww₁ sp₁ g₂ mm₂ rr₂ ww₂ sp₂ =>
          hk w₁ w₂ hsp' hr' (fun _ => by rw [g₁ .x15 (by decide), g₂ .x15 (by decide), m₁.1, m₂.1])
            (by rw [rr₁, T₁.rd]) (by rw [ww₁, T₁.wr]) (by rw [mm₁]; exact T₁.frame) (by rw [sp₁, T₁.sp])
            (by rw [rr₂, T₂.rd]) (by rw [ww₂, T₂.wr]) (by rw [mm₂]; exact T₂.frame) (by rw [sp₂, T₂.sp]))
      (Stitch.stitchDM_ok L gh T₁.tbOk T₁.sin) (Stitch.stitchDM_ok L gh T₂.tbOk T₂.sin) fun u₄ v₄ q₁ q₂ => ?_
    exact rel_taint [.x19] (by rw [q₁.sp, q₂.sp, T₁.sp, T₂.sp, hsp]) (by agree_tac [q₁.env.x19, q₂.env.x19])
      ⟨_, by taint_decide⟩

/-- The pointers of the rest and the arguments of the call on its whole
blocks, after the interleaved loop: `Mid`, and `Abs3`. -/
theorem openBlk_ok {H : Block} {s₀ t s₂ s₂c s₂' : State} {x : List Byte} {icb : Block} {S : Addr}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h₂ : FFront Ctx (W + BitVec.ofNat 64 16) W SP H (bytesAt t.mem Np 12) (bytesAt t.mem A al) S n t s₂)
    (g₂c : s₂c.gpr = s₂.gpr) (rd₂c : s₂c.rd = s₂.rd) (wr₂c : s₂c.wr = s₂.wr)
    (F₂c : Frame [workR W, ⟨D, n⟩] t.mem s₂c.mem) (key₂c : KeyAt H s₂c.mem W)
    (hH₂c : blockAt s₂c.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hm : Stitch.DecP Ctx (W + BitVec.ofNat 64 16) W SP H x icb R S D n s₂c s₂') :
    WP isa (.block (Impl.AesGcm.AArch64.Stitch.whole ++ ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr) ++
        absSeg2 16)) s₂' fun s₆ => ∃ s₃ : State, ∃ X : Addr,
      Mid Ctx W SP H R n D (BitVec.ofNat 64 tl) X t s₃ ∧
      Abs3 Ctx (W + BitVec.ofNat 64 16) W SP s₃.gpr 16 H [] (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n)
        0 s₃.mem 0 s₆ ∧ s₆.rd = s₃.rd ∧ s₆.wr = s₃.wr := by
  have L := o.lay
  have hn := o.dat.ok.lt
  have hpn : Stitch.pre n ≤ n := Nat.mul_div_le n 128
  have subP : Region.Sub ⟨D, Stitch.pre n⟩ ⟨D, n⟩ := Region.sub_prefix hpn
  have g₂' : ∀ r ∈ [Reg.x19, .x22, .x26, .x27, .x28], s₂'.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rw [hm.gpr _ (by decide), g₂c]
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, x23₃, x24₃, x25₃, r₃⟩ := Stitch.afterD_ok (u := s₂') (D := D) (n := n)
    hm.x23 (by rw [g₂' _ (by simp), h₂.x26]) hn
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := hm.env.of_regs r₃
  have hd₃ : DataW Ctx (W + BitVec.ofNat 64 16) W s₃ D n :=
    o.dat.of_eq (by rw [r₃.rd, hm.rd, rd₂c, h₂.rd]) (by rw [r₃.wr, hm.wr, wr₂c, h₂.wr])
  have dS : ∀ {R' : Region}, R'.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ →
      R'.Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ → R'.Disjoint ⟨D, n⟩ →
      R'.Disjoint (Stitch.tblR W) → ∀ r ∈ Stitch.sFrameN (W + BitVec.ofNat 64 16) W D n, R'.Disjoint r :=
    fun h1 h2 h3 h4 r hr => by
      simp only [Stitch.sFrameN, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [r₃.mem, blockAt_frame hm.frame (dS ((L.cs.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.stSub (by decide)))
      ((L.cs.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.stSub (by decide)))
      (o.dat.ctx.sub_left (Lay.ctxSub (by decide)))
      ((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (Lay.wSub (by decide)))), hH₂c]
  have key₃ : KeyAt H s₃.mem W := by
    rw [r₃.mem]
    exact key₂c.frame hm.frame (dS (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      (o.ddW.sub_right (Lay.wSub (by decide))).symm
      (Offset.disjoint W (.inl (by decide)) (by decide) (by decide)))
  have F₃ : Frame [workR W, ⟨D, n⟩] t.mem s₃.mem := by
    rw [r₃.mem]
    refine F₂c.trans (hm.frame.sub fun r hr => ?_)
    simp only [Stitch.sFrameN, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
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

/-- `openRunAS` in two runs from the same public arguments, of the ciphertext
at `S`: over it (`S = D`) or out of place (`to`). -/
theorem openRunAS_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr}
    {to : Bool} {S : Addr} {s₀₁ s₀₂ t₁ t₂ : State}
    {ex : List Region} (hexW : ∀ r ∈ ex, (workR W).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (o₁ : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀₂ t₂)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = S ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = S ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (hal : al ≤ 16)
    (hsrc₁ : DataOk (W + BitVec.ofNat 64 16) W t₁ S n) (hsrc₂ : DataOk (W + BitVec.ofNat 64 16) W t₂ S n)
    (hm : cond to ((⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (S = D))
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
      (to = true → v₁.gpr .x15 = v₂.gpr .x15) →
      v₁.rd = t₁.rd → v₁.wr = t₁.wr → Frame [workR W, ⟨D, n⟩] t₁.mem v₁.mem →
      v₂.rd = t₂.rd → v₂.wr = t₂.wr → Frame [workR W, ⟨D, n⟩] t₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec to)) TT) :
    RelCT isa (Eq2 t₁ t₂) (openRunAS v.callees cl tb to) TT := by
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
    (front_ok (D := S) L hMK hJ₁ o₁.aad hal x4₁ x5₁ x6₁ x7₁) (front_ok (D := S) L hMK hJ₂ o₂.aad hal x4₂ x5₂ x6₂ x7₂)
    fun s₂ u₂ h₂ k₂ => ?_
  obtain ⟨s₂c, run₂c, m₂c, g₂c, sp₂c, rd₂c, wr₂c⟩ := saveCb_ok h₂.env
  obtain ⟨u₂c, run₂c', m₂c', g₂c', sp₂c', rd₂c', wr₂c'⟩ := saveCb_ok k₂.env
  refine rel_seq (rel_taint [.x19, .x20] (by rw [h₂.env.sp, k₂.env.sp])
      (by agree_tac [h₂.env.x19, k₂.env.x19, h₂.env.x20, k₂.env.x20]) ⟨_, by taint_decide⟩)
    (F₁ := fun s => s = s₂c) (F₂ := fun s => s = u₂c)
    (WP.of_runBlock ⟨s₂c, run₂c, rfl⟩) (WP.of_runBlock ⟨u₂c, run₂c', rfl⟩) fun _ _ e₁ e₂ => ?_
  subst e₁ e₂
  obtain ⟨I₁, F₁, key₁, hH₁, -, he₁⟩ := openDec_ok o₁ h₂ m₂c g₂c sp₂c rd₂c wr₂c htb₁ hsrc₁ hm
  obtain ⟨I₂, F₂, key₂, hH₂, -, he₂⟩ := openDec_ok o₂ k₂ m₂c' g₂c' sp₂c' rd₂c' wr₂c' htb₂ hsrc₂ hm
  refine rel_seq (decPart_rel gh L I₁ I₂ (by rw [he₁.sp, he₂.sp])
      fun v₁ v₂ hsp hr h15 r₁ w₁ f₁ sp₁ r₂ w₂ f₂ sp₂ => htbrel v₁ v₂ (by rw [sp₁, he₁.sp])
        (by rw [sp₂, he₂.sp]) hr h15 (by rw [r₁, rd₂c, h₂.rd]) (by rw [w₁, wr₂c, h₂.wr])
        (F₁.trans (f₁.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩))
        (by rw [r₂, rd₂c', k₂.rd]) (by rw [w₂, wr₂c', k₂.wr])
        (F₂.trans (f₂.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)))
    (Stitch.decPart_ok L gh I₁) (Stitch.decPart_ok L gh I₂) fun s₃ u₃ m₁ m₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x26] (by rw [m₁.env.sp, m₂.env.sp])
      (by agree_tac [m₁.env.x19, m₂.env.x19, m₁.env.x20, m₂.env.x20, m₁.env.x21, m₂.env.x21,
        m₁.x23, m₂.x23, m₁.gpr .x26 (by decide), m₂.gpr .x26 (by decide), I₁.x26, I₂.x26]) ⟨_, by taint_decide⟩)
    (openBlk_ok o₁ h₂ g₂c rd₂c wr₂c F₁ key₁ hH₁ m₁) (openBlk_ok o₂ k₂ g₂c' rd₂c' wr₂c' F₂ key₂ hH₂ m₂)
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
variable {Ctx W SP D Np A : Addr} {R nl al n tl P : Nat} {C₁ C₂ C₁' C₂' : List Byte}

/-- The arguments of `failB`'s `cryptAl`: the first `P` bytes, from the kept
counter block. -/
theorem failCr_ok {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidS fr Ctx W SP D Np A R nl al n tl P C₁ C₂ s s₇) :
    ∃ s₈, runBlock isa (([.ldrq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO, .strq .v0 .x20 48,
      .ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      [mov .x24 .x9, imm .x25 0]) s₇ = some s₈ ∧
      CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D P s₈ ∧ s₈.gpr .x27 = s₇.gpr .x27 ∧
        s₈.gpr .x26 = BitVec.ofNat 64 n := by
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  obtain ⟨s₈, run₈, _, x23₈, x24₈, x25₈, x26₈, og₈, sp₈, rd₈, wr₈⟩ := failArgs_ok mo
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := mo.env.keep (fun r hr => og₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  exact ⟨s₈, run₈, ⟨he₈, fun _ _ => rfl, by rw [og₈ _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
    (mo.data.take hPn).of_eq rd₈ wr₈, rfl⟩, og₈ _ (by decide), x26₈⟩

/-- The arguments of `okB`'s `cryptAl`: the rest. -/
theorem okCr_ok {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidS fr Ctx W SP D Np A R nl al n tl P C₁ C₂ s s₇) :
    ∃ s₈, runBlock isa (([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr)) s₇ = some s₈ ∧
      CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R P (D + BitVec.ofNat 64 P) (n - P) s₈ ∧
        s₈.gpr .x27 = s₇.gpr .x27 ∧ s₈.gpr .x26 = BitVec.ofNat 64 n ∧ s₈.wr = s₇.wr := by
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  obtain ⟨s₈, run₈, x23₈, x24₈, x25₈, x26₈, r₈⟩ := okArgs_ok mo
  exact ⟨s₈, run₈, ⟨mo.env.of_regs r₈, fun _ _ => rfl, by rw [r₈.others _ (by decide), mo.x22], hR, x23₈, x24₈,
    x25₈, (mo.data.drop hPn).of_eq r₈.rd r₈.wr, rfl⟩, r₈.others _ (by decide), x26₈, r₈.wr⟩

/-- `omBS` in two runs whose tags compare alike. -/
theorem omBS_rel (v : GcmImpl) (L : Lay Ctx (W + BitVec.ofNat 64 16) W) {fr fr' : List Region}
    {s s' m₁ m₂ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo₁ : MidS fr Ctx W SP D Np A R nl al n tl P C₁ C₂ s m₁)
    (mo₂ : MidS fr' Ctx W SP D Np A R nl al n tl P C₁' C₂' s' m₂)
    (hx : m₁.gpr .x27 = m₂.gpr .x27) :
    RelCT isa (Eq2 m₁ m₂) (omBS v.callees) TT := by
  have hP16 : P % 16 = 0 := by rw [mo₁.hP]; omega
  have hlt : ∀ B : Bool, (if B then 1 else 0 : Nat) < 2 ^ 64 := fun B => by cases B <;> decide
  have ite_ok : ∀ {fr : List Region} {C₁ C₂ : List Byte} {s m : State}, MidS fr Ctx W SP D Np A R nl al n tl P C₁ C₂ s m →
      WP isa (.ite (.zero .x .x27) (failB v.callees) (okB v.callees)) m fun u => u.sp = SP ∧
        u.gpr .x27 = m.gpr .x27 := fun {fr C₁ C₂ s m} mo => by
    refine WP.ite _ (eval_zero mo.x27 (hlt _)) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨s₈, run₈, hc, k27, k26⟩ := failCr_ok hR mo
      exact WP.seq (WP.of_runBlock ⟨s₈, run₈, WP.mono (cryptAlT_ok L v (icb := 0) hc rfl k26 mo.data.ok.lt
        fun _ h => absurd hP16 h) fun s₉ h₉ =>
        ⟨h₉.env.sp, by rw [h₉.kept .x27 (by decide), k27]⟩⟩)
    · obtain ⟨s₈, run₈, hc, k27, k26, kw⟩ := okCr_ok hR mo
      exact WP.seq (WP.of_runBlock ⟨s₈, run₈, WP.mono (cryptAlT_ok L v (icb := 0) hc hP16 k26 mo.data.ok.lt
        (tail_big (by rw [kw]; exact mo.data.wr) mo.data.ok.lt rfl (by have := mo.hP; omega))) fun s₉ h₉ =>
        ⟨h₉.env.sp, by rw [h₉.kept .x27 (by decide), k27]⟩⟩)
  have tm : ∃ h, (taint.check (Taint.ofRegs [.x27]) (.block [mov .x0 .x27]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  unfold omBS
  refine rel_seq ?_ (ite_ok mo₁) (ite_ok mo₂) fun a b ⟨ea, xa⟩ ⟨eb, xb⟩ =>
    rel_taint [.x27] (by rw [ea, eb]) (by agree_tac [xa, xb, hx]) tm
  have x27₁ := mo₁.x27
  have x27₂ : m₂.gpr .x27 = _ := hx ▸ x27₁
  refine rel_ite (eval_zero x27₁ (hlt _)) (eval_zero x27₂ (hlt _)) (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨s₈, run₈, hc₁, -, k₁⟩ := failCr_ok hR mo₁
    obtain ⟨t₈, run₈', hc₂, -, k₂⟩ := failCr_ok hR mo₂
    unfold failB
    refine rel_seq (rel_taint [.x19, .x20] (by rw [mo₁.env.sp, mo₂.env.sp])
        (by agree_tac [mo₁.env.x19, mo₂.env.x19, mo₁.env.x20, mo₂.env.x20]) ⟨_, by taint_decide⟩)
      (F₁ := fun u => u = s₈) (F₂ := fun u => u = t₈)
      (WP.of_runBlock ⟨s₈, run₈, rfl⟩) (WP.of_runBlock ⟨t₈, run₈', rfl⟩) fun _ _ e₁ e₂ => ?_
    subst e₁ e₂
    exact cryptAlT_rel L v hc₁ hc₂ rfl (by rw [k₁, k₂])
  · obtain ⟨s₈, run₈, hc₁, -, k₁, -⟩ := okCr_ok hR mo₁
    obtain ⟨t₈, run₈', hc₂, -, k₂, -⟩ := okCr_ok hR mo₂
    unfold okB
    refine rel_seq (rel_taint [.x19] (by rw [mo₁.env.sp, mo₂.env.sp])
        (by agree_tac [mo₁.env.x19, mo₂.env.x19]) ⟨_, by taint_decide⟩)
      (F₁ := fun u => u = s₈) (F₂ := fun u => u = t₈)
      (WP.of_runBlock ⟨s₈, run₈, rfl⟩) (WP.of_runBlock ⟨t₈, run₈', rfl⟩) fun _ _ e₁ e₂ => ?_
    subst e₁ e₂
    exact cryptAlT_rel L v hc₁ hc₂ hP16 (by rw [k₁, k₂])

end

section
variable {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `tagBit`, of the ciphertext at `S`, as it was at the entry. -/
theorem tagBitS {Ctx W SP Np A D Tg S : Addr} {R nl al n tl : Nat} {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) (rt : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hS : bytesAt t.mem S n = bytesAt s₀.mem S n) (hok : Spec.Gcm.tagLenOk tl = true) :
    decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx R) (blockAt t.mem (Ctx + BitVec.ofNat 64 240))
      (bytesAt t.mem Np nl) (bytesAt t.mem A al) (bytesAt t.mem S n)).take tl = bytesAt t.mem W tl) =
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem S n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl)).isSome := by
  obtain ⟨hc₃, hH₃, hN₃, hA₃, -⟩ := o.vals
  rw [hc₃, hH₃, hN₃, hA₃, hS, rt, Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
  by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem A al) (bytesAt s₀.mem S n)).take tl = bytesAt s₀.mem Tg tl
  · rw [ite_eq_left hc]; simp [hc]
  · rw [ite_eq_right hc]; simp [hc]

/-- `openRunWithS` in two runs, after `tagIn`, whose tags compare alike, of
the ciphertext at `S`: over it (`S = D`) or out of place (`to`). -/
theorem openRunWithS_relX (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {nl : Nat}
    {to : Bool} {S : Addr} {s₀₁ s₀₂ t₁ t₂ : State}
    {ex : List Region} (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (o₁ : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀₁ t₁) (o₂ : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀₂ t₂)
    (h12 : nl = 12)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = S ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = S ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (hal : al ≤ 16) (rt₁ : bytesAt t₁.mem W tl = bytesAt s₀₁.mem Tg tl)
    (rt₂ : bytesAt t₂.mem W tl = bytesAt s₀₂.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true)
    (hsrc₁ : DataOk (W + BitVec.ofNat 64 16) W t₁ S n) (hsrc₂ : DataOk (W + BitVec.ofNat 64 16) W t₂ S n)
    (hsW : (⟨S, n⟩ : Region).Disjoint (workR W))
    (hm : cond to ((⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (S = D))
    (hS₁ : bytesAt t₁.mem S n = bytesAt s₀₁.mem S n) (hS₂ : bytesAt t₂.mem S n = bytesAt s₀₂.mem S n)
    (hb : (Spec.Gcm.openResult (ctxCiph s₀₁.mem Ctx R) (ctxH s₀₁.mem Ctx) tl (bytesAt s₀₁.mem Np nl)
        (bytesAt s₀₁.mem S n) (bytesAt s₀₁.mem A al) (bytesAt s₀₁.mem Tg tl)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀₂.mem Ctx R) (ctxH s₀₂.mem Ctx) tl (bytesAt s₀₂.mem Np nl)
        (bytesAt s₀₂.mem S n) (bytesAt s₀₂.mem A al) (bytesAt s₀₂.mem Tg tl)).isSome)
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
      (to = true → v₁.gpr .x15 = v₂.gpr .x15) →
      v₁.rd = s₀₁.rd → v₁.wr = s₀₁.wr → Frame [workR W, ⟨D, n⟩] s₀₁.mem v₁.mem →
      v₂.rd = s₀₂.rd → v₂.wr = s₀₂.wr → Frame [workR W, ⟨D, n⟩] s₀₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec to)) TT) :
    RelCT isa (Eq2 t₁ t₂) (Impl.AesGcm.AArch64.Stitch.openRunWithS v.callees tb cl to) TT := by
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
  refine (openRunWithS_split v.callees cl tb to).symm.rel (rel_seq
    (openRunAS_relX v cl hMK gh hexW hexC o₁ o₂ hx₁ hx₂ hal hsrc₁ hsrc₂ hm g₁ g₂
      (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ hd =>
        hrel c₁ c₂ sY sS sp₁ sp₂ (r₁.trans o₁.rd₀) (w₁.trans o₁.wr₀) (F₁.trans f₁) (r₂.trans o₂.rd₀)
          (w₂.trans o₂.wr₀) (F₂.trans f₂) hd) tb₁ tb₂
      (fun v₁ v₂ sp₁ sp₂ hr h15 r₁ w₁ f₁ r₂ w₂ f₂ => htbrel v₁ v₂ sp₁ sp₂ hr h15 (r₁.trans o₁.rd₀)
        (w₁.trans o₁.wr₀) (F₁.trans f₁) (r₂.trans o₂.rd₀) (w₂.trans o₂.wr₀) (F₂.trans f₂)))
    (WP.mono (openRunASX_ok cl v hMK gh (I := fun _ => True) o₁ hx₁.1 hx₁.2.1 hx₁.2.2.1 hx₁.2.2.2 hal hok
      hsrc₁ hsW hm hexW hexD hexC (fun _ _ => trivial) (fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₁ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) tb₁) fun _ q => q.1)
    (WP.mono (openRunASX_ok cl v hMK gh (I := fun _ => True) o₂ hx₂.1 hx₂.2.1 hx₂.2.2.1 hx₂.2.2.2 hal hok
      hsrc₂ hsW hm hexW hexD hexC (fun _ _ => trivial) (fun s' _ _ _ _ c y z r w sp f hd =>
        WP.mono (g₂ s' c y z r w sp f hd) fun _ g => ⟨g, trivial⟩) tb₂) fun _ q => q.1) fun m₁ m₂ mo₁ mo₂ => ?_)
  refine omBS_rel v L o₁.rounds mo₁ mo₂ ?_
  have hCs : ∀ m : Mem, bytesAt m S (Stitch.pre n) ++
      bytesAt m (S + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n) = bytesAt m S n := fun m => by
    rw [← bytesAt_add, Nat.add_sub_cancel' (Nat.mul_div_le n 128)]
  rw [mo₁.x27, mo₂.x27, hCs, hCs, tagBitS o₁ rt₁ hS₁ hok, tagBitS o₂ rt₂ hS₂ hok, hb]

end

end VG.Proof.AesGcm.AArch64.Fast
