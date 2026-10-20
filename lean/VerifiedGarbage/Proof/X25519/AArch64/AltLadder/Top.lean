module

import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Ends
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Top
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
import VerifiedGarbage.Proof.X25519.AArch64.Word.Output
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Lit
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# X25519 on AArch64: the `_alt` ladder's whole function

The four-word function's setup, the `_alt` ladder with its first and last
iterations, and the four-word function's inversion and output. No instruction writes a vector
register, so `v8`–`v15` are kept without being saved.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder

open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 (offset)
open VG.Proof.Ed25519.AArch64 (env F Outside ofs clob word off ofs_off' Saved Small)
open VG.Proof.X25519.AArch64.Word (LoopKeep Good bitOffset localContract Kp Sc saved_of_words
  preservedCases Scratch)

theorem correct [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s₀ : State} (hp : localContract.pre s₀) :
    WP isa VG.Impl.X25519.AArch64.AltLadder.x25519 s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ localContract.post s₀ t := by
  have pre := VG.Proof.X25519.AArch64.Pre.of s₀ hp.1
  let base := s₀.gpr .x3
  have hs : Sc base s₀ := ⟨rfl,by rw [pre.wr]; simp [base,VG.Proof.X25519.AArch64.scR]⟩
  rw [VG.Impl.X25519.AArch64.AltLadder.x25519]
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Word.setup_ok hs hp.2 rfl rfl
    (by rw [pre.rd]; simp) (by rw [pre.rd]; simp) pre.scalar_sc pre.point_sc)
    fun c ⟨hc, gc, wc, oc, bc, svc, kc, sc⟩ => ?_)
  have kl := length_bytesAt s₀.mem (s₀.gpr .x1) 32
  refine WP.seq (WP.mono (first_ok (k := decodeScalar25519 (bytesAt s₀.mem (s₀.gpr .x1) 32)) hc gc
    (by rw [scalar_bit kl (by decide)]; rfl) sc)
    fun c' ⟨kc', gc', wc', bc'⟩ => ?_)
  have hc' := kc'.scratch hc
  refine WP.seq (WP.mono (ladder_ok hc' gc' wc' (fun i hi => by rw [kc'.bit hi]; exact bc i hi) bc')
    fun d ⟨kd', gd, wd, bd⟩ => ?_)
  have kd := kc'.trans kd'
  have hd := kd.scratch hc
  refine WP.seq (WP.mono (tail_ok hd gd wd bd (by rw [scalar_bit kl (by decide)]; rfl)
    (by rw [scalar_bit kl (by decide)]; rfl) (by rw [scalar_bit kl (by decide)]; rfl))
    fun e ⟨ke, ex, ez⟩ => ?_)
  have he := ke.scratch hd
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.Divstep.invert_ok he) fun f ⟨fi, fk, f1, fm⟩ => ?_)
  have hf : Scratch f base := ⟨(fk.gpr _ (by decide)).trans he.x0, fk.wr ▸ he.wr, he.nowrap⟩
  have saved : Saved base s₀.gpr f.mem :=
    (((saved_of_words svc).outside kd.mem (by decide)).outside ke.mem (by decide)).outside fm (by decide)
  have out : f.gpr .x1 = s₀.gpr .x0 :=
    f1.trans ((ke.gpr _ (by decide) (by decide)).trans ((kd.gpr _ (by decide) (by decide)).trans oc))
  have dx : env f.mem base 1 = env e.mem base 1 :=
    congrArg toFe (VG.Proof.Ed25519.AArch64.Outside.fe fm (Or.inl (by decide : offset 1+32 ≤ 192))
      (by decide))
  have kf' : Kp (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ [.x2, .x20]) e f := ⟨fk.gpr, fk.rd, fk.wr⟩
  refine WP.mono (VG.Proof.X25519.AArch64.Word.finish_ok (g := s₀.gpr) hf out
    (by rw [fk.wr, ke.wr, kd.wr, kc.wr, pre.wr]; simp) pre.out_sc saved)
    fun t ⟨tg, kt, rt⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases preservedCases r hr with ⟨rd,hrd,er⟩ | hn
    · rw [← er]; exact tg rd hrd
    · have kk := (((kc.trans kd.kp).trans ke.kp).trans kf').trans kt
      exact kk.sub (by decide) |>.gpr r hn
  · change bytesAt t.mem (s₀.gpr .x0) 32 = Spec.X25519.x25519
      (bytesAt s₀.mem (s₀.gpr .x1) 32) (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [rt, dx, fi, ex, ez, x25519_eq]

theorem x25519_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (hs : localContract.pre s) :
    ∃ tr t, Exec isa VG.Impl.X25519.AArch64.AltLadder.x25519 s tr t ∧ abiPreserved s t ∧
      localContract.post s t := by
  obtain ⟨tr,t,he,⟨hg,hp⟩,hv⟩ := WP.preservedV (correct hs) (by lit_decide)
  exact ⟨tr,t,he,⟨hg,Exec.sp he,hv⟩,hp⟩

end VG.Proof.X25519.AArch64.AltLadder
