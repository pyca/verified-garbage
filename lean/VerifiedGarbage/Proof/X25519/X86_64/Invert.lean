import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.X25519.Field64

/-!
# X25519 on x86-64: `vg_gf25519_r64_invert`, verified

The facts of `Spec.X25519.Field64.invertContract` on x86-64 (`inv64`: `ws` in
`rdi`), which `invertFn` meets: it keeps the callee-saved registers the
divsteps write in `xmm0`–`xmm5` (`invSaves_ok`, `invRestores_ok`), the
divsteps keep the vector registers and change only bytes 512 to 767 of `ws`,
and leave in slot 17 (byte 544) slot 4's (byte 128) power `p - 2`
(`invertDS_pow`). Constant time by taint tracking (only `rsp` and `ws` are
public), and a state satisfying the precondition.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519
open VG.Spec.X25519.Field64 (valAt zAt invAt InvKeeps)

/-- `vg_gf25519_r64_invert(ws = rdi)`. -/
def inv64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 4096⟩] ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 4096⟩ ∧ (s.gpr .rdi).toNat + 4096 ≤ 2 ^ 64
  post s s' :=
    valAt s'.mem (s.gpr .rdi) invAt % Spec.X25519.P =
        valAt s.mem (s.gpr .rdi) zAt ^ (Spec.X25519.P - 2) % Spec.X25519.P ∧
      InvKeeps (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

/-- The spec's element at `o` is the slot's four words. -/
theorem valAt_fe (m : Mem) (base : Addr) (o : BitVec 32) : valAt m base o = fe m base o.toNat := by
  show (m.read (off base o.toNat) (8 * 4)).toNat = _
  rw [Mont.read_eq_wordsVal]
  simp only [fe, val4, word, off, Mont.wordsVal, Mont.word, Mont.off, Nat.mul_zero, Nat.add_zero]
  rw [show o.toNat + 8 + 8 = o.toNat + 16 by omega, show o.toNat + 16 + 8 = o.toNat + 24 by omega]
  simp only [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
  omega

theorem setXmm_gpr' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem setXmm_mem' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem setXmm_rd' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem setXmm_wr' (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem setXmm_xmm' (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

/-- `invSaves`: the callee-saved registers in `xmm0`–`xmm5`. -/
theorem invSaves_ok (s : State) :
    WP isa (.block invSaves) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .rbx ∧ s'.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .rbp ∧
      s'.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r12 ∧ s'.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .r13 ∧
      s'.xmm .xmm4 = (0 : BitVec 64) ++ s.gpr .r14 ∧ s'.xmm .xmm5 = (0 : BitVec 64) ++ s.gpr .r15 := by
  apply WP.of_runBlock
  simp only [invSaves, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    Option.some.injEq, exists_eq_left', setXmm_gpr', setXmm_mem', setXmm_rd', setXmm_wr', setXmm_xmm',
    reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `invRestores`: the callee-saved registers out of `xmm0`–`xmm5`, nothing else changed but
them. -/
theorem invRestores_ok (s : State) :
    WP isa (.block invRestores) s fun s' =>
      s'.gpr .rbx = (s.xmm .xmm0).extractLsb' 0 64 ∧ s'.gpr .rbp = (s.xmm .xmm1).extractLsb' 0 64 ∧
      s'.gpr .r12 = (s.xmm .xmm2).extractLsb' 0 64 ∧ s'.gpr .r13 = (s.xmm .xmm3).extractLsb' 0 64 ∧
      s'.gpr .r14 = (s.xmm .xmm4).extractLsb' 0 64 ∧ s'.gpr .r15 = (s.xmm .xmm5).extractLsb' 0 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [invRestores, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setReg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, rfl, rfl, rfl⟩
  all_goals try (simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; done)
  simp only [RegUpd.gpr_setReg_of_ne _ _ a, RegUpd.gpr_setReg_of_ne _ _ b, RegUpd.gpr_setReg_of_ne _ _ c,
    RegUpd.gpr_setReg_of_ne _ _ d, RegUpd.gpr_setReg_of_ne _ _ e, RegUpd.gpr_setReg_of_ne _ _ f]

theorem lo_append (x : BitVec 64) : ((0 : BitVec 64) ++ x).extractLsb' 0 64 = x := by
  ext i h; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

theorem invert_x64 [DivstepInv] (s : State) (hs : inv64.pre s) :
    ∃ t s', Exec isa invertFn s t s' ∧ abiPreserved s s' ∧ inv64.post s s' := by
  obtain ⟨hrd, hwr, hret, hnw⟩ := hs
  let base := s.gpr .rdi
  have hscr : Scr s base := ⟨rfl, by rw [hwr]; simp [base], hnw⟩
  suffices hwp : WP isa invertFn s fun s' => gprPreserved s s' ∧ inv64.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he hg, hp⟩
  refine WP.seq (WP.mono (invSaves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, x0, x1, x2, x3, x4, x5⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨by rw [g₁], by rw [wr₁]; exact hscr.wr, hnw⟩
  refine WP.seq (WP.mono (WP.vecKeep (by lit_decide) (invertDS_pow baseline_ok hs₁))
    fun s₂ ⟨⟨g₂, rd₂, wr₂, o₂, e₂⟩, xm₂, _⟩ => ?_)
  refine WP.mono (invRestores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃, m₃, rd₃, wr₃⟩ => ?_
  have hx : ∀ r, s₂.xmm r = s₁.xmm r := fun r => by rw [xm₂]
  -- the registers the divsteps keep
  have keep : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 →
      s₃.gpr r = s.gpr r := fun r hc a b c d e f => by
    rw [k₃ r a b c d e f, g₂ r hc a, g₁]
  have hm : s₃.mem = s₂.mem := m₃
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b₃, hx, x0, lo_append]
    · rw [p₃, hx, x1, lo_append]
    · exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [r12₃, hx, x2, lo_append]
    · rw [r13₃, hx, x3, lo_append]
    · rw [r14₃, hx, x4, lo_append]
    · rw [r15₃, hx, x5, lo_append]
  · -- the return address, apart from `ws`
    refine Mem.readW_congr fun i hi => ?_
    have hx' := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx'
    rw [hm, o₂ _ (Or.inr ?_), m₁]
    simp only [ofs, base]; omega
  · rw [valAt_fe, valAt_fe, hm]
    have e := congrArg Fin.val e₂
    simp only [E, F, toFe, Fin.val_ofNat] at e
    show fe s₂.mem base 544 % Spec.X25519.P = fe s.mem base 128 ^ (Spec.X25519.P - 2) % Spec.X25519.P
    rw [show (32 * (17 : Fin 128).val) = 544 from rfl] at e
    rw [e, pow_pw]
    simp only [pw, Fin.val_ofNat]
    rw [show (32 * (4 : Fin 128).val) = 128 from rfl, m₁, ← Nat.pow_mod]
  · intro i hi hown
    simp only [Spec.X25519.Field64.wsBytes, Spec.X25519.Field64.invOwnAt,
      Spec.X25519.Field64.invOwnEnd] at hi hown
    rw [hm, o₂ _ (by rw [ofs_off' _ (by omega)]; omega), m₁]

theorem invert_ct : ConstantTime isa inv64.pre inv64.pub invertFn := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h0

/-- A state satisfying the precondition. -/
def invSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 4096⟩]

theorem invert_verified [DivstepInv] :
    Verified X86_64.target invertFn (Spec.X25519.Field64.invertContract X86_64.abi) :=
  Verified.of_correct invert_x64 invert_ct (by
    sig_implies [Spec.X25519.Field64.invertContract, Spec.X25519.Field64.invSig, X86_64.abi,
      X86_64.argRegs, inv64] [invSat] using invSat)

end VG.Proof.X25519.X86_64
