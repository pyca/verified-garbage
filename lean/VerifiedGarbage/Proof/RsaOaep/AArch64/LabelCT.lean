import VerifiedGarbage.Proof.RsaOaep.AArch64.CtBase

/-!
# RSAES-OAEP on AArch64: the label's hash in constant time

`hashLabel` from two runs in the same frame and working space, with the
label at the same place and of the same length in both (`LabAt`): each block
by the taint analysis, each call the same call (`hashLabel_tr`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

variable {G : Hash} (hG : StreamOK G.stream)

/-- The label's registers for `update`. -/
def LabX (F S : Addr) (lab : Addr) (labLen : Nat) (W : Nat → BitVec 64) (t : State) : Prop :=
  LabAt t F S W lab labLen ∧ t.gpr .x0 = off S oSt ∧ t.gpr .x1 = BitVec.ofNat 64 0 ∧ t.gpr .x2 = lab ∧
    t.gpr .x3 = BitVec.ofNat 64 labLen ∧ t.gpr .x4 = off S oW

include hG in
theorem hashLabel_tr {F S : Addr} {lab : Addr} {labLen : Nat} (hlen : labLen < 2 ^ 64) {o : Nat}
    (ho : o = oDig ∨ o = oLh)
    {X : (Nat → BitVec 64) → State → Prop} (hX : ∀ W t, X W t → LabAt t F S W lab labLen) :
    RelCT isa (LR F S X) (hashLabel G o) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  unfold hashLabel seqs seqs seqs seqs seqs seqs
  refine (lr_wp (X' := fun W t => LabAt t F S W lab labLen ∧ t.gpr .x0 = off S oSt) (lr_taint [] (by taint_decide)
    nopin) fun t V W L R hx => WP.mono (initArgs_ok L []) fun u ⟨Su, hm, x0⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, (hX W t hx).congr Su.rd Su.wr rfl rfl, x0⟩).seq ?_
  refine (lr_wp (X' := fun W t => LabAt t F S W lab labLen) (lr_init hG fun _ _ h => h.2)
    fun t V W L R ⟨A, x0⟩ => WP.mono (init_ok hG L R x0 []) fun u ⟨Lu, Su, Ru, _⟩ =>
      ⟨_, W, Lu, Ru, A.congr Su.rd Su.wr rfl rfl⟩).seq ?_
  refine (lr_wp (X' := LabX F S lab labLen) (lr_taint [] (by taint_decide) nopin)
    fun t V W L R A => WP.mono (labA_ok L R A []) fun u ⟨Su, hm, x0, x1, x2, x3, x4⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, A.congr Su.rd Su.wr rfl rfl, x0, x1, x2, x3, x4⟩).seq ?_
  refine (lr_wp (X' := fun W t => LabAt t F S W lab labLen) (lr_updExt hG (BitVec.ofNat 64 0) (len := labLen)
      (d := lab) hlen fun _ _ ⟨A, x0, x1, x2, x3, x4⟩ => ⟨⟨A.cov, A.dS, A.dK⟩, x0, x1, x2, x3, x4⟩)
    fun t V W L R ⟨A, x0, x1, x2, x3, x4⟩ => WP.mono (updExt_ok hG L R A.len A.cov A.dS A.dK x0 x2 x3 x4 [])
      fun u ⟨Lu, Su, Ru, _⟩ => ⟨_, W, Lu, Ru, A.congr Su.rd Su.wr rfl rfl⟩).seq ?_
  refine (lr_wp (X' := fun _ t => t.gpr .x0 = off S oSt ∧ t.gpr .x1 = BitVec.ofNat 64 labLen ∧
      t.gpr .x2 = off S o ∧ t.gpr .x3 = off S oW) (lr_taint [] (check_of_zImm (τ := Taint.ofRegs [])
      (c := .block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 o ++ scr .x3 oW))
      (c' := .block (scr .x0 oSt ++ ([.ldrSp .x1 sLabLen] : List Instr) ++ scr .x2 0 ++ scr .x3 oW)) rfl
      (by taint_decide)) nopin)
    fun t V W L R A => WP.mono (labF_ok L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide) [])
      fun u ⟨Su, hm, x0, x1, x2, x3⟩ => ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, x0, x1, x2, x3⟩).seq ?_
  exact lr_fin hG (BitVec.ofNat 64 labLen) (.inr hoo) fun _ _ h => h

end VG.Proof.RsaOaep.AArch64
