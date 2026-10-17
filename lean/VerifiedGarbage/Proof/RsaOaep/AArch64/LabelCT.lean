module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# RSAES-OAEP on AArch64: the label's hash in constant time

`hashLabel` from two runs in the same frame and working space, with the
label at the same place and of the same length in both (`LabAt`): each block
by the taint analysis, each call the same call, dispatched on the same
number (`hashLabel_tr`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs initC updC finC)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

variable {hs : List Hash} {kH : Nat} {G : Hash} (hn : Num hs kH G) (hG : StreamOK G.stream)

/-- The label's registers for `update`. -/
def LabX (F S : Addr) (lab : Addr) (labLen : Nat) (W : Nat → BitVec 64) (t : State) : Prop :=
  LabAt t F S W lab labLen ∧ t.gpr .x0 = off S oSt ∧ t.gpr .x1 = BitVec.ofNat 64 0 ∧ t.gpr .x2 = lab ∧
    t.gpr .x3 = BitVec.ofNat 64 labLen ∧ t.gpr .x4 = off S oW

include hn hG in
theorem hashLabel_tr {F S : Addr} {lab : Addr} {labLen : Nat} (hlen : labLen < 2 ^ 64) {o : Nat}
    (ho : o = oDig ∨ o = oLh)
    {X : (Nat → BitVec 64) → State → Prop}
    (hX : ∀ W t, X W t → LabAt t F S W lab labLen ∧ W 2 = BitVec.ofNat 64 kH) :
    RelCT isa (LR F S X) (hashLabel hs o) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  unfold hashLabel seqs seqs seqs seqs seqs seqs
  refine (lr_wp (X' := fun W t => (LabAt t F S W lab labLen ∧ W 2 = BitVec.ofNat 64 kH) ∧ t.gpr .x0 = off S oSt)
    (lr_taint [] (by taint_decide) nopin) fun t V W L R hx => WP.mono (initArgs_ok L []) fun u ⟨Su, hm, x0⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, ⟨(hX W t hx).1.congr Su.rd Su.wr rfl rfl, (hX W t hx).2⟩,
        x0⟩).seq ?_
  refine (lr_wp (X' := fun W t => LabAt t F S W lab labLen ∧ W 2 = BitVec.ofNat 64 kH) (lr_hcall hn initC (j := 2)
      rfl (by decide) (by taint_decide) (fun _ _ h => h.1.2)
      (lr_init hG fun _ _ ⟨_, h, hs⟩ => (hs.gpr .x0 (by decide) (by decide)).trans h.2))
    fun t V W L R ⟨⟨A, hk⟩, x0⟩ => WP.mono (dinit_ok hn hG L R (SelAt.of_lay L R (j := 2) rfl (by decide) hk) x0 [])
      fun u ⟨Lu, Su, Ru, _⟩ => ⟨_, W, Lu, Ru, A.congr Su.rd Su.wr rfl rfl, hk⟩).seq ?_
  refine (lr_wp (X' := fun W t => LabX F S lab labLen W t ∧ W 2 = BitVec.ofNat 64 kH) (lr_taint [] (by taint_decide)
      nopin)
    fun t V W L R ⟨A, hk⟩ => WP.mono (labA_ok L R A []) fun u ⟨Su, hm, x0, x1, x2, x3, x4⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, ⟨A.congr Su.rd Su.wr rfl rfl, x0, x1, x2, x3, x4⟩, hk⟩).seq ?_
  refine (lr_wp (X' := fun W t => LabAt t F S W lab labLen ∧ W 2 = BitVec.ofNat 64 kH) (lr_hcall hn updC (j := 2)
      rfl (by decide) (by taint_decide) (fun _ _ h => h.2)
      (lr_updExt hG (BitVec.ofNat 64 0) (len := labLen) (d := lab) hlen
        fun _ u hu => by
          obtain ⟨_, ⟨⟨A, x0, x1, x2, x3, x4⟩, _⟩, hs⟩ := hu
          exact ⟨⟨by rw [hs.rd, hs.wr]; exact A.cov, A.dS, A.dK⟩, Same.regs5 hs ⟨x0, x1, x2, x3, x4⟩⟩))
    fun t V W L R ⟨⟨A, x0, x1, x2, x3, x4⟩, hk⟩ => WP.mono (dupdExt_ok hn hG L R
      (SelAt.of_lay L R (j := 2) rfl (by decide) hk) A.len A.cov A.dS A.dK x0 x2 x3 x4 [])
      fun u ⟨Lu, Su, Ru, _⟩ => ⟨_, W, Lu, Ru, A.congr Su.rd Su.wr rfl rfl, hk⟩).seq ?_
  refine (lr_wp (X' := fun W t => (t.gpr .x0 = off S oSt ∧ t.gpr .x1 = BitVec.ofNat 64 labLen ∧
      t.gpr .x2 = off S o ∧ t.gpr .x3 = off S oW) ∧ W 2 = BitVec.ofNat 64 kH)
      (lr_taint [] (check_of_zImm (τ := Taint.ofRegs [])
      (c := .block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 o ++ scr .x3 oW))
      (c' := .block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 0 ++ scr .x3 oW)) rfl
      (by taint_decide)) nopin)
    fun t V W L R ⟨A, hk⟩ => WP.mono (labF_ok L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide) [])
      fun u ⟨Su, hm, x0, x1, x2, x3⟩ => ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, ⟨x0, x1, x2, x3⟩, hk⟩).seq ?_
  exact lr_hcall hn finC (j := 2) rfl (by decide) (by taint_decide) (fun _ _ h => h.2)
    (lr_fin hG (BitVec.ofNat 64 labLen) (.inr hoo) fun _ _ ⟨_, h, hs⟩ => Same.regs4 hs h.1)

end VG.Proof.RsaOaep.AArch64
