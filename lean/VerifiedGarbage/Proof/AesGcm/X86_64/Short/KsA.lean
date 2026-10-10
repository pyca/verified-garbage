import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin

/-!
# The keystream of the end of `seal` with AES-NI

Untrusted: everything here is checked by Lean. `finKsA` (`Short.finKsA`)
loads `J₀` and the counter block into `xmm5` and `xmm7`, encrypts them with
`AesNi.aes` and stores them at `K`: it meets what `finishWith` needs of its
keystream (`finKsA_ksOk`), in two runs too (`finKsA_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt aesWith)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64.AesNi (Keys XFrame aes_ok)

/-- `finCtrsA`: `J₀` and the counter block in `xmm5` and `xmm7`, and
`AesNi.aes`'s registers. -/
theorem finCtrsA_ok {Ctx St W SP : Addr} {nr : Nat} (s : State) (he : Env Ctx St W SP s)
    (hR : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 nr) :
    ∃ t, runBlock isa finCtrsA s = some t ∧
      t.xmm .xmm5 = s.mem.readW St 128 ∧ t.xmm .xmm7 = s.mem.readW (St + BitVec.ofNat 64 48) 128 ∧
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 nr ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * nr) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm7 → t.xmm r = s.xmm r) := by
  have r0 : InRegions (s.rd ++ s.wr) St 16 := by
    have := he.perm.stR (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  have r48 : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 48) 16 := he.perm.stR (by decide)
  obtain ⟨s₁, run₁, x5, x7, g₁, m₁, rd₁, wr₁, k₁⟩ : ∃ t, runBlock isa
      [.movdquLoad .xmm5 (at_ .r14 0), .movdquLoad .xmm7 (at_ .r14 48)] s = some t ∧
      t.xmm .xmm5 = s.mem.readW St 128 ∧ t.xmm .xmm7 = s.mem.readW (St + BitVec.ofNat 64 48) 128 ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm5 → r ≠ .xmm7 → t.xmm r = s.xmm r) := by
    have e0 : s.gpr .r14 + BitVec.ofInt 64 ((0 : Nat) : Int) = St := by
      rw [he.r14, BitVec.ofInt_natCast, BitVec.add_zero]
    have e48 : s.gpr .r14 + BitVec.ofInt 64 ((48 : Nat) : Int) = St + BitVec.ofNat 64 48 := by
      rw [he.r14, BitVec.ofInt_natCast]
    refine ⟨(s.setXmm .xmm5 (s.mem.readW St 128)).setXmm .xmm7 (s.mem.readW (St + BitVec.ofNat 64 48) 128),
      ?_, ?_, ?_, by simp only [gpr_setXmm], by simp only [mem_setXmm], by simp only [rd_setXmm],
      by simp only [wr_setXmm], fun r a b => ?_⟩
    · simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, State.ea, r0, r48,
        gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, e0, e48, r0, r48, ite_true, Option.map_some]
    · simp [State.setXmm]
    · simp [State.setXmm]
    · simp [State.setXmm, a, b]
  have r176 : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 176) 8 := by
    rw [rd₁, wr₁]; exact he.perm.wR (by decide)
  have d4 := dbl4 nr Ctx
  obtain ⟨t, run₂, di, si, r10, g₂, m₂, rd₂, wr₂, x₂⟩ : ∃ t, runBlock isa
      [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .r10 (.reg .rsi),
        .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
        .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] s₁ = some t ∧
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 nr ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * nr) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → t.gpr r = s₁.gpr r) ∧ t.mem = s₁.mem ∧ t.rd = s₁.rd ∧
      t.wr = s₁.wr ∧ t.xmm = s₁.xmm := by
    refine ⟨_, by xrun [g₁, he.r13, he.r15, r176, m₁, hR, d4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp [gpr_setReg, gpr_arithFlags, g₁, he.r13, he.r15, m₁, hR, d4]; done)
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
    all_goals rfl
  have run : runBlock isa finCtrsA s = some t := by
    rw [show finCtrsA = [.movdquLoad .xmm5 (at_ .r14 0), .movdquLoad .xmm7 (at_ .r14 48)] ++
        [.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
        .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
        .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] from rfl,
      runBlock_append, run₁]
    exact run₂
  refine ⟨t, run, by rw [x₂, x5], by rw [x₂, x7], di, si, r10,
    fun r a b c => by rw [g₂ r a b c, g₁], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    fun r a b => by rw [x₂, k₁ r a b]⟩

theorem finKsA_ksOk : KsOk finKsA := by
  intro Ctx W SP nr s he hR hnr
  obtain ⟨s₁, run₁, x5, x7, di₁, si₁, r10₁, g₁, m₁, rd₁, wr₁, k₁⟩ := finCtrsA_ok s he hR
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  generalize hw : bytesAt s.mem Ctx (16 * (nr + 1)) = w
  have hK : Keys nr w s₁ := ⟨by rw [di₁, m₁, hw], by omega, fun j hj => by
    rw [rd₁, wr₁, di₁, BitVec.ofInt_natCast]; exact he.perm.ctxR (by omega)⟩
  refine WP.seq (WP.mono (aes_ok [.xmm5, .xmm7] (by decide) (by decide) hnr s₁ hK si₁ (by rw [r10₁, di₁]))
    fun s₂ ⟨e₂, f₂⟩ => ?_)
  have hw₂ : ∀ d, d + 16 ≤ 64 → InRegions s₂.wr (W + BitVec.ofNat 64 (1024 + d)) 16 := fun d hd => by
    rw [f₂.wr, wr₁]; exact he.perm.wW (by omega)
  have ea : ∀ d, s₂.gpr .r15 + BitVec.ofInt 64 ((kO + d : Nat) : Int) = W + BitVec.ofNat 64 (1024 + d) := by
    intro d; rw [f₂.gpr, g₁ _ (by decide) (by decide) (by decide), he.r15, BitVec.ofInt_natCast]; rfl
  have ea0 : s₂.gpr .r15 + BitVec.ofInt 64 ((kO : Nat) : Int) = W + BitVec.ofNat 64 (1024 + 0) := ea 0
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128_eq, State.ea, ea, ea0,
      hw₂ 0 (by decide), hw₂ 16 (by decide), ite_true, Option.bind_some, State.setMem_gpr, State.setMem_wr,
      State.setMem_xmm]
    rfl, ?_⟩
  have hc : ciphOf s.mem Ctx nr = aesWith nr w := by rw [← hw]
  have c5 := e₂ .xmm5 (by simp)
  have c7 := e₂ .xmm7 (by simp)
  have sep : Mem.Sep (W + BitVec.ofNat 64 (1024 + 0)) (128 / 8) (W + BitVec.ofNat 64 (1024 + 16)) (128 / 8) :=
    Offset.sep W (.inl (by decide)) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setMem_mem]
    rw [show W + BitVec.ofNat 64 1024 = W + BitVec.ofNat 64 (1024 + 0) from rfl, VG.Proof.Gcm.X86_64.blockAt_eq,
      Mem.readW_writeW_sep sep (by decide), Mem.readW_writeW_self _ _ 16 _ (by decide), hc]
    exact ks_lane x5 c5
  · simp only [State.setMem_mem]
    rw [Offset.add_add, VG.Proof.Gcm.X86_64.blockAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hc]
    exact ks_lane x7 c7
  · simp only [State.setMem_mem]
    rw [f₂.mem, m₁]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains W (e := 1024) (k := 64) (d := 1024 + 0) (n := 16) (by decide) (by decide) (by decide)
    · exact Offset.contains W (e := 1024) (k := 64) (d := 1024 + 16) (n := 16) (by decide) (by decide) (by decide)
  · intro r a b c; simp only [State.setMem_gpr]; rw [f₂.gpr, g₁ r a b c]
  · simp only [State.setMem_rd]; rw [f₂.rd, rd₁]
  · simp only [State.setMem_wr]; rw [f₂.wr, wr₁]
  · intro r a b c d
    simp only [State.setMem_xmm]
    rw [f₂.xmm r (by simp [a, b, c]), k₁ r a b]

theorem finKsA_rel : KsRel finKsA := fun {Ctx W SP D R r} _ => by
  have wCtrs : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finCtrsA) s fun t =>
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 R ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * R) := fun s h => by
    obtain ⟨t, run, -, -, di, si, r10, -⟩ := finCtrsA_ok s h.env h.rounds
    exact WP.of_runBlock ⟨t, run, di, si, r10⟩
  exact rel_piece [.rdi, .rsi, .r10] (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ wCtrs wCtrs (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64.Short
