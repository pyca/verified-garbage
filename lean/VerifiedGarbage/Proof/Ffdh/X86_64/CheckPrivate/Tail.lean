module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-! # FFDH private-key validation on x86-64: compare the generated public value -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr leave)

def PairReady (p : KpP) (xb : List Byte) (s : State) : Prop := ∃ mi,
  Base p xb s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi ∧
    wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb ∧
    wv s.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = Spec.Rsa.os2ip p.yb ∧
    word s.mem (off p.B (inner p.w)) (8 * sF) = bit (p.fl xb)

theorem checked_pair {p : KpP} {xb : List Byte} {s : State} (h : Checked p xb s) :
    WP isa (seqs (loadArr aXm sY sK)) s (StepPost p s (PairReady p xb)) := by
  obtain ⟨mi, hb, hc, hy, hF⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  have hn := hc.good.scr.nowrap
  have hYle := slot_le (w := p.w) (show aY < 8 by decide)
  have hFle := hdr_lt_slot p.w 8 (show sF < 32 by decide)
  refine WP.mono (primeLoad_ok hc (by omega) (Nat.le_refl _) (by omega) (show aXm < 8 by decide)
    (show sY < 32 by decide) (show sK < 32 by decide)
    (hb.hdr (sY, p.yp) (by simp [KpP.headers]))
    (by rw [hb.ylen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) hb.y
    (by rw [hb.ylen]; omega) (by rw [hb.ylen]; omega) (by rw [hb.ylen]))
    fun t ⟨hc', hxm, ho, k⟩ => ?_
  have hf : Frm (off p.B (inner p.w)) [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  have hXmle := slot_le (w := p.w) (show aXm < 8 by decide)
  obtain ⟨hb', hi, hs⟩ := hb.child hc hf (fun r hr => by rw [List.mem_singleton.mp hr]; omega) k
  refine ⟨⟨mi, hb', hc', ?_, hxm, ?_⟩, hi, hs, k.mono (by decide)⟩
  · apply Eq.trans _ hy
    apply hf.wv_eq
    · intro r hr
      rw [List.mem_singleton.mp hr]
      have := slot_sep (w := p.w) (show aXm ≠ aY by decide)
      omega
    · omega
  · apply Eq.trans _ hF
    apply hf.word_eq
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact Or.inl (hdr_lt_slot p.w aXm (show sF < 32 by decide))
    · omega

private theorem bit_and (P Q : Prop) [Decidable P] [Decidable Q] : bit Q &&& bit P = bit (P ∧ Q) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [bit, hp, hq]

/-- The final Boolean arithmetic and leaving the inner workspace. -/
def finish : List Instr := [.alu .and .rax (.mem (hdr sF)), leave]

theorem pair_finish {p : KpP} {xb : List Byte} {s : State} (h : PairReady p xb s) :
    WP isa (seqs (eqArr aY aXm ++ ([.block finish] : List (Prog isa)))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧
        t.gpr .rax = bit (p.fl xb ∧ p.z xb = Spec.Rsa.os2ip p.yb)) := by
  obtain ⟨mi, hb, hc, hy, hxm, hF⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  refine wp_seqs_append (a := eqArr aY aXm) (by simp [eqArr]) (by simp)
    (WP.mono (eqArr_ok hc.good (Nat.le_refl _) (by omega) (by omega)
      (show aY < 8 by decide) (show aXm < 8 by decide)) fun u ⟨ha, hm, k⟩ => ?_)
  rw [hy, hxm] at ha
  have hcu := (hc.toMem.congr hm k.2.2).ctx ((k.gpr (by decide)).trans hc.rdi)
  have hFu : word u.mem (off p.B (inner p.w)) (8 * sF) = bit (p.fl xb) := by rw [hm]; exact hF
  simp only [seqs]
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t =>
      t.gpr .rdi = p.B ∧ t.gpr .rax = bit (p.fl xb ∧ p.z xb = Spec.Rsa.os2ip p.yb) ∧ t.mem = u.mem) (by
        unfold finish leave
        xrun [State.ea, hdr, hdrOff, hcu.rdi, hcu.link, hFu, ha,
          hcu.good.scr.ld (hdr_lt_slot p.w 8 (show sF < 32 by decide)),
          hcu.good.scr.ld (hdr_lt_slot p.w 8 (show VG.Impl.Rsa.X86_64.Crt.sLink < 32 by decide))]
        exact bit_and (p.fl xb) (p.z xb = Spec.Rsa.os2ip p.yb)) rfl)
    fun t ⟨⟨hd, hf, hmem⟩, kk⟩ => ⟨⟨hd, hf⟩, by rw [hmem, hm]; exact InScr.refl _ _ _,
      (fun _ _ => by rw [hmem, hm]), keep_trans (k.mono (by decide)) (kk.mono (by decide))⟩

private theorem tail_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail M.mm E.code (.seq (.block r2Head) R.code) =
      .seq (.block r2Head) R.code :: (pow M.mm E.code sG sK sX sXl ++ (range aY ++
        (loadArr aXm sY sK ++ (eqArr aY aXm ++ ([.block finish] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail, finish, List.append_assoc, List.cons_append, List.nil_append]

theorem tail_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State}
    (h : Work p xb mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail M.mm E.code (.seq (.block r2Head) R.code))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit (p.fl xb ∧ p.z xb = Spec.Rsa.os2ip p.yb)) := by
  rw [tail_eq]
  refine wp_seqs_cons (by simp [pow]) (WP.mono (work_ready M R h hd hm) fun u₁ S₁ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sG sK sX sXl) (by simp [pow]) (by simp [range, gt1, ltArr, cmpArr])
    (WP.mono (ready_value M E S₁.1) fun u₂ S₂ => ?_)
  refine wp_seqs_append (a := range aY) (by simp [range, gt1, ltArr, cmpArr]) (by simp [loadArr])
    (WP.mono (value_checked S₂.1) fun u₃ S₃ => ?_)
  refine wp_seqs_append (a := loadArr aXm sY sK) (by simp [loadArr]) (by simp [eqArr])
    (WP.mono (checked_pair S₃.1) fun u₄ S₄ => ?_)
  exact WP.mono (pair_finish S₄.1) fun _ S₅ => (((S₁.trans S₂).trans S₃).trans S₄).trans S₅

end VG.Proof.Ffdh.X86_64.CheckPrivate
