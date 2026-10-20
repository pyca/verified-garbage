module

public import VerifiedGarbage.Proof.Dsa.X86.RandomDraw
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# Sampling a nonce (x86)

`sample` draws until a candidate is accepted, the tape is short, or the
budget of 128 draws is spent, as `Spec.Dsa.Random.sample (rq s₀) 128`
does from the tape's byte `used` on (`SampleOut`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

theorem Smp.mem {s₀ t u : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : Ready s₀ u) (hm : u.mem = t.mem) : Smp s₀ used draws u :=
  S.congr A hr (by rw [hm]; exact Outs.refl _ _ _) (by rw [hm]) (by rw [hm])

theorem SampleOut.mem {s₀ v u : State} (A : RandomSignABI s₀) {base : Nat} {S : Spec.Dsa.Random.Sample}
    (O : SampleOut s₀ base S v) (hr : Ready s₀ u) (hm : u.mem = v.mem) : SampleOut s₀ base S u :=
  ⟨let ⟨d, Sd⟩ := O.smp; ⟨d, Sd.mem A hr hm⟩, by rw [hm]; exact O.status, by rw [hm]; exact O.nonce⟩

/-- A new budget of 128 draws. -/
theorem sampleInit_ok {s₀ t : State} (A : RandomSignABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t) :
    WP isa (.block [.mov .eax (.imm 128), .store (sp oDraws) .eax, .mov .eax (.imm 4), .store (sp oStatus) .eax]) t
      fun u => Smp s₀ used 128 u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧
        Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧ Keeps sampleRegs t u := by
  have h := S.ready
  refine (wp_movS rfl fun t₁ u₁ _ => wp_slot (h.rf.of_keeps u₁.keeps) (by decide) u₁.gpr
    fun t₂ f₂ m₂ g₂ r₂ w₂ _ _ => wp_movS rfl fun t₃ u₃ _ => wp_slot (f₂.of_keeps u₃.keeps) (by decide) u₃.gpr
    fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => WP.block_nil ?_)
  have hm₄ : t₄.mem = (t.mem.writeW (off (rBase s₀) oDraws) (128 : BitVec 32)).writeW
      (off (rBase s₀) oStatus) (4 : BitVec 32) := by rw [m₄, u₃.mem, m₂, u₁.mem]
  have k₄ : Keeps sampleRegs t t₄ := (((u₁.keeps.mono (by decide)).trans ⟨fun r _ => by rw [g₂], r₂, w₂⟩).trans
    (u₃.keeps.mono (by decide))).trans ⟨fun r _ => by rw [g₄], r₄, w₄⟩
  have h₄ : Ready s₀ t₄ := h.congr k₄ (by
    rw [hm₄]; exact (frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _))
  have o₄ : Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem t₄.mem := by
    rw [hm₄]; exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
  have S₄ : Smp s₀ used 128 t₄ := S.of A h₄ (o₄.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [drawRanges])
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
      slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]; rfl) S.usedBound
  have st₄ : slot t₄.mem (rBase s₀) oStatus = 4 := by rw [hm₄, slot_write_self]
  exact ⟨S₄, st₄, o₄, k₄⟩

theorem sample_ok {s₀ t : State} (A : RandomSignABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t)
    (hq : 1 < rq s₀) :
    WP isa sample t fun u => SampleOut s₀ used (spl s₀ 128 used) u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used)) ∧
      Ready s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Keeps sampleRegs t u := by
  unfold sample
  refine WP.seq (WP.mono (sampleInit_ok A S) fun t₄ ⟨S₄, st₄, o₄, k₄⟩ => ?_)
  let S₀ := spl s₀ 128 used
  refine WP.seq (WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used', 1 ≤ n ∧ n ≤ 128 ∧
      Smp s₀ used' n u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧ SampleRel s₀ S₀ used used' n ∧
      Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Keeps sampleRegs t u) (fun n u hu => ?_) 128 t₄
    ⟨used, by decide, by decide, S₄, st₄, ⟨rfl, rfl, rfl⟩, o₄.mono (by decide), k₄⟩)
  obtain ⟨used', hn1, hn, Sm, st, R, ou, ku⟩ := hu
  refine WP.seq (WP.mono (draw_ok A Sm hn1 hn hq st) fun v ⟨hv, ov, kv, hcase⟩ => ?_)
  refine wp_movS (v := slot v.mem (rBase s₀) oStatus) (hv.rf.readSlot (by decide)) fun v₁ uv₁ _ =>
    wp_cmpi fun v₂ fv₂ _ zv₂ => WP.block_nil ?_
  have hv₂ : Ready s₀ v₂ := (hv.upd uv₁ (by decide)).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  have kv₂ : Keeps sampleRegs t v₂ := ((ku.trans kv).trans (uv₁.keeps.mono (by decide))).trans (fv₂.keeps _)
  have ov₂ : Outs (rBase s₀) sampleRanges t.mem v₂.mem := by rw [mv₂]; exact ou.trans ov
  rcases hcase with ⟨stv, h2, Sv, rel, _⟩ | ⟨stv, out, _⟩
  · right
    refine ⟨by simp only [eval, zv₂, uv₁.gpr, stv]; rfl, n - 1, by omega, used' + rWidth s₀, by omega, by omega,
      Sv.mem A hv₂ mv₂, by rw [mv₂]; exact stv, rel S₀ used R, ov₂, kv₂⟩
  · have O := out S₀ used R
    have hz : (slot v.mem (rBase s₀) oStatus - 4 == 0) = false := by
      rw [O.status, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        sub_beq (by have := sampleStatus_le S₀; omega) (by decide)]
      have := sampleStatus_le S₀
      simp only [decide_eq_false_iff_not]; omega
    left
    refine ⟨by simp only [eval, zv₂, uv₁.gpr, hz], ?_⟩
    refine wp_movS (v := slot v₂.mem (rBase s₀) oStatus) (hv₂.rf.readSlot (by decide)) fun u uu _ =>
      WP.block_nil ?_
    have hu : Ready s₀ u := hv₂.upd uu (by decide)
    have mu : u.mem = v.mem := by rw [uu.mem, mv₂]
    refine ⟨O.mem A hu mu, by rw [uu.gpr, mv₂, O.status], hu, by rw [uu.mem]; exact ov₂,
      kv₂.trans (uu.keeps.mono (by decide))⟩

end VG.Proof.Dsa.X86
