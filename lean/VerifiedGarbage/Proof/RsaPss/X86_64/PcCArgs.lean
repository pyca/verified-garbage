module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCall

import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedArgs
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Mathlib.Tactic.Set

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: the public-key operation's arguments

`pubArgsC_ok`: its output at the start of `scratch`, the signature, the
cache, and the rest of `scratch` after our part.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {G : Spec.Mgf1.Hash}

def pubA1 : List Instr :=
  ([.mov .rax (.mem (sp sSig)), .store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] : List Instr) ++
  scr .rax oRsa ++ ([.store (sp 16) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 24) .rax, .mov .rdi (.mem (sp sScr)), .mov .rsi (.mem (sp sK))] : List Instr)

theorem pubArgsC_eq : pubArgsC = pubA1 ++ ([.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))] : List Instr) ++
    ([.mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))] : List Instr) := rfl

theorem pubA1_ok {s : State} {u : State} (L : Lay u (fb s) (stackArg s 3))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 3) V W)
    (h17 : W 17 = s.gpr .rsi) (h22 : W 22 = stackArg s 4) (h38 : W 38 = s.gpr .r9) :
    WP isa (.block pubA1) u fun u' => Keep [.rax, .rdi, .rsi] u u' ∧
      Lay u' (fb s) (stackArg s 3) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 3) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧ (∀ i < nW, 4 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = stackArg s 3 ∧ u'.gpr .rsi = s.gpr .rsi := by
  have G' := L.geo
  have hs : u.mem.readW (off (fb s) sScr) 64 = stackArg s 3 := L.slot
  set S := stackArg s 3
  have Ra := R.wf G' (k := 0) (by decide) (s.gpr .r9)
  have Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rsi)
  have Rc := Rb.wf G' (k := 2) (by decide) (off S oRsa)
  have Rd := Rc.wf G' (k := 3) (by decide) (stackArg s 4 - BitVec.ofNat 64 1024)
  simp only [Nat.reduceMul, off_zero] at Ra Rb Rc Rd
  have hst0 : InRegions u.wr (fb s) 8 := by simpa only [off_zero] using L.st (d := 0) (by decide)
  have f0 : u.mem.readW (off (fb s) sSig) 64 = s.gpr .r9 := by
    rw [R.rd (d := sSig) 38 rfl (by decide), h38]
  have f1 : (u.mem.writeW (fb s) (s.gpr .r9)).readW (off (fb s) sK) 64 = s.gpr .rsi := by
    rw [Ra.rd (d := sK) 17 rfl (by decide)]; simp [upd, h17]
  have f2 : ((u.mem.writeW (fb s) (s.gpr .r9)).writeW (off (fb s) 8) (s.gpr .rsi)).readW
      (off (fb s) sScr) 64 = S := by
    rw [Rb.rd (d := sScr) 21 rfl (by decide)]; simp only [upd, Nat.reduceEqDiff, ite_false]
    exact (R.rd (d := sScr) 21 rfl (by decide)).symm.trans hs
  have f3 : (((u.mem.writeW (fb s) (s.gpr .r9)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off S oRsa)).readW (off (fb s) sScrLen) 64 = stackArg s 4 := by
    rw [Rc.rd (d := sScrLen) 22 rfl (by decide)]; simp [upd, h22]
  set m4 := ((((u.mem.writeW (fb s) (s.gpr .r9)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off S oRsa)).writeW (off (fb s) 24) (stackArg s 4 - BitVec.ofNat 64 1024)) with hm4
  have g : ∀ k, 4 ≤ k → k < nW → m4.readW (off (fb s) (8 * k)) 64 = W k := fun k hk hk' => by
    refine (Rd.fr k hk').trans ?_; simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  have g21 : m4.readW (off (fb s) sScr) 64 = S :=
    (g 21 (by decide) (by decide)).trans ((R.rd (d := sScr) 21 rfl (by decide)).symm.trans hs)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi] (Q := fun u' => u'.mem = m4 ∧
      u'.gpr .rdi = S ∧ u'.gpr .rsi = s.gpr .rsi) ?_ rfl) fun u2 ⟨⟨hm, h1, h2⟩, k2⟩ => ?_
  · xrun [pubA1, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sSig) (by decide), f0,
      L.ld (d := sScr) (by decide), hst0,
      L.st (d := 8) (by decide), L.st (d := 16) (by decide), L.st (d := 24) (by decide),
      L.ld (d := sK) (by decide), L.ld (d := sScrLen) (by decide), f1, f2, f3, g21,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 < 2 ^ 31 by decide),
      show m4.readW (off (fb s) sK) 64 = s.gpr .rsi from (g 17 (by decide) (by decide)).trans h17,
      show S + BitVec.ofNat 64 oRsa = off S oRsa from rfl]
    rw [show BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 by decide] at *
    rw [← hm4, g21]
    exact ⟨rfl, rfl, (g 17 (by decide) (by decide)).trans h17⟩
  have R2 : Rep u2.mem (fb s) S V _ := hm ▸ Rd
  refine ⟨k2, L.of_rep' R R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2,
    ⟨_, R2, fun i hi => ?_, fun i hi h4 => ?_⟩, h1, h2⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with h | h | h | h <;> subst h
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]; rfl
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]

theorem pubArgsC_ok {s u : State} (hp : Pre G s) (L : Lay u (fb s) (stackArg s 3))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 3) V W)
    (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem)
    (h17 : W 17 = s.gpr .rsi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h38 : W 38 = s.gpr .r9) :
    WP isa (.block pubArgsC) u fun u' =>
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧ Lay u' (fb s) (stackArg s 3) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 3) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧ (∀ i < nW, 4 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = stackArg s 3 ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 5 ∧
      u'.gpr .rcx = stackArg s 6 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx := by
  refine WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] ?_ (by decide) |>
    WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  rw [pubArgsC_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (pubA1_ok L R h17 h22 h38)) fun t ⟨⟨k, L1, ⟨W1, R1, ha, hb⟩, hdi, hsi⟩, f⟩ => ?_
  have hf := vframe_keep hp.toVPre hw L.rsp hM f
  refine WP.mono (load_pre hp L1.rsp (k.2.1.trans hrd) hf) fun v ⟨k2, hm, hdx, hcx⟩ => ?_
  have L2 : Lay v (fb s) (stackArg s 3) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm])
  have R2 : Rep v.mem (fb s) (stackArg s 3) V W1 := hm ▸ R1
  refine WP.mono (WP.keep [.r8, .r9] (Q := fun y => y.mem = v.mem ∧ y.gpr .r8 = s.gpr .rdx ∧
    y.gpr .r9 = s.gpr .rcx) ?_ rfl) fun y ⟨⟨hm3, h8, h9⟩, k3⟩ => ?_
  · xrun [ea_sp, L2.rsp, L2.ld (d := sE) (by decide), L2.ld (d := sEl) (by decide),
      R2.rd (d := sE) 19 rfl (by decide), R2.rd (d := sEl) 20 rfl (by decide),
      hb 19 (by decide) (by decide), hb 20 (by decide) (by decide), h19, h20]
  refine ⟨L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), ⟨W1, hm3 ▸ R2, ha, hb⟩,
    (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans hdi),
    (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans hsi), (k3.gpr (by decide)).trans hdx,
    (k3.gpr (by decide)).trans hcx, h8, h9⟩

end VG.Proof.RsaPss.X86_64.Pc
