module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
public import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `j0` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTJ0.lean`): the invariants fix the context, the state,
`W`, the nonce's address and length (also in `r18`), and leave the rest
existential.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment with the nonce's length `n` in `r18`. -/
def EnvN (c st w sp : Addr) (n : Nat) (s : State) : Prop :=
  n < 2 ^ 64 ∧ ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s7 = BitVec.ofNat 64 n ∧
    Env V sp s

theorem EnvN.c {c st w sp : Addr} {n : Nat} {s : State} (h : EnvN c st w sp n s) : EnvC c st w sp s := by
  obtain ⟨_, V, a, b, d, _, e⟩ := h; exact ⟨V, a, b, d, e⟩

theorem EnvN.s7 {c st w sp : Addr} {n : Nat} {s : State} (h : EnvN c st w sp n s) :
    s.gpr .s7 = BitVec.ofNat 64 n := by
  obtain ⟨_, V, _, _, _, e, he⟩ := h; exact (he.fr _ (by decide)).trans e

theorem EnvN.keep {c st w sp : Addr} {n : Nat} {s s' : State} (h : EnvN c st w sp n s)
    (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    EnvN c st w sp n s' := by
  obtain ⟨hn, V, a, b, d, e, he⟩ := h; exact ⟨hn, V, a, b, d, e, he.keep hg hsp hrd hwr⟩

/-- Before `j0`. -/
def J0I (c st w sp : Addr) (Np : Addr) (n : Nat) (s : State) : Prop :=
  ∃ V H, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ J0In V sp H Np n s

/-- After `J₀` is written. -/
def J0M (c st w sp : Addr) (s : State) : Prop :=
  ∃ V H iv m₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ J0Mid V sp H iv m₀ s

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem j0hash_ct {Np : Addr} {n : Nat} : CT (J0I c st w sp Np n) j0hash := by
  refine CT.seq (J := fun s => AbsI c st w sp 0 Np n 0 s ∧ EnvN c st w sp n s) ?_
    (fun s ⟨V, H, h29, h30, h31, hs⟩ => WP.mono (j0zero_ok (L.v h29 h30 h31) hs) fun s' ⟨hai, _⟩ =>
      ⟨⟨V, H, [], h29, h30, h31, rfl, hai⟩, hs.data.lt, V, h29, h30, h31, hs.s7, hai.env⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s1])
        (.block [.li .t0 0, .store .d .t0 .s1 0, .store .d .t0 .s1 8, .li .s6 0]) h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, b₁, _, h₁⟩ ⟨_, _, _, b₂, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.s1, h₂.env.s1, b₁, b₂]⟩) hc
  refine CT.seq (J := EnvN c st w sp n) ((absorb_ct L (.inl rfl) (q := 0) (by decide)).mono fun s h => h.1)
    (fun s ⟨⟨V, H, x, h29, h30, h31, _, hs⟩, hn'⟩ => ?_) ?_
  · have e18 : V .s7 = BitVec.ofNat 64 n := (hs.env.fr _ (by decide)).symm.trans hn'.s7
    exact WP.mono (absorb_ok (L.v h29 h30 h31) (.inl rfl) hs) fun s' ho =>
      ⟨hn'.1, V, h29, h30, h31, e18, ho.env⟩
  refine CT.seq (J := fun s => EnvN c st w sp n s ∧ s.gpr .s6 = BitVec.ofNat 64 (n % 16)) ?_
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s7])
        (.block [.logicImm .and .s6 .s7 15]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨h₁.c.sp.trans h₂.c.sp.symm, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.s7, h₂.s7]⟩) hc
  · have h18 := hs.s7
    have hlt : n < 2 ^ 64 := hs.1
    have hand := and15 (BitVec.ofNat 64 n)
    rw [toNat64 hlt] at hand
    have h₃ : WP isa (.block [.logicImm .and .s6 .s7 15]) s fun s₃ =>
        s₃.gpr .s6 = BitVec.ofNat 64 (n % 16) ∧ (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧
          Keeps s s₃ := by
      crun [Int.reduceNatCast', h18, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨hs.keep (fun r hr => hg r (by revert r; decide))
      hk.sp hk.rd hk.wr, h26⟩
  refine CT.seq (J := EnvN c st w sp n) ((flush_ct L (.inl rfl) (Nat.mod_lt _ (by decide))).mono
      fun s h => ⟨h.1.c, h.2⟩)
    (fun s ⟨hn', h26⟩ => ?_) ?_
  · obtain ⟨hlt, V, h29, h30, h31, e18, he⟩ := hn'
    refine WP.mono (flush_ok (L.v h29 h30 h31) (.inl rfl) (H := blockAt s.mem (V .s2 + BitVec.ofNat 64 240))
      (x := List.replicate n 0) ⟨he, rfl⟩ (by rw [h26, List.length_replicate])) fun s' hf =>
        ⟨hlt, V, h29, h30, h31, e18, hf.env⟩
  refine CT.seq (J := EnvN c st w sp n) ?_ (fun s hs => ?_) ((lens_ct L (.inl rfl)).mono fun s h => h.c)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s7])
        (.block [.li .s4 0, mov .s6 .s7]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨h₁.c.sp.trans h₂.c.sp.symm, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.s7, h₂.s7]⟩) hc
  · have h18 := hs.s7
    have h₅ : WP isa (.block [.li .s4 0, mov .s6 .s7]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h18, mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => hs.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr

theorem j0_ct {Np : Addr} {n : Nat} : CT (J0I c st w sp Np n) j0 := by
  refine CT.seq (J := fun s => J0I c st w sp Np n s ∧ s.gpr .a2 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) ?_
    (fun s ⟨V, H, h29, h30, h31, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s5])
        (.block [.addi .a2 .s5 (-12)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.s5, h₂.s5]⟩) hc
  · have h₁ : WP isa (.block [.addi .a2 .s5 (-12)]) s fun s₁ =>
        s₁.gpr .a2 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ (∀ r, r ≠ .a2 → s₁.gpr r = s.gpr r) ∧
          Keeps s s₁ := by
      crun [Int.reduceNatCast', hs.s5]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    refine WP.mono h₁ fun s₁ ⟨h6, hg₁, hk₁⟩ => ⟨⟨V, H, h29, h30, h31, ?_⟩, h6⟩
    exact ⟨hs.env.keep (fun r hr => hg₁ r (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr,
      by rw [hk₁.mem]; exact hs.hH, by rw [hg₁ _ (by decide)]; exact hs.s4,
      by rw [hg₁ _ (by decide)]; exact hs.s5, hs.s7, hs.data.of_eq hk₁.rd hk₁.wr hk₁.sp⟩
  refine CT.seq (J := J0M c st w sp) ?_ (fun s ⟨⟨V, H, h29, h30, h31, hs⟩, h6⟩ => ?_) ?_
  · refine CT.ite (decide (n = 12)) (fun s ⟨⟨_, _, _, _, _, hs⟩, h6⟩ => eval_subk h6 hs.data.lt (by decide))
      (fun _ => ?_) fun _ => (j0hash_ct L).mono fun s h => h.1
    obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s1]) (.block j012)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, b₁, _, h₁⟩, _⟩ ⟨⟨_, _, _, b₂, _, h₂⟩, _⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.env.s1, h₂.env.s1, b₁, b₂]
  · have hlt := hs.data.lt
    refine WP.ite (decide (n = 12)) (eval_subk h6 hlt (by decide)) (fun ht => ?_) (fun hf => ?_)
    · have h12 : n = 12 := by simpa using ht
      subst h12
      exact WP.mono (j012_ok (L.v h29 h30 h31) hs) fun s' hm => ⟨V, H, _, _, h29, h30, h31, hm⟩
    · exact WP.mono (j0hash_ok (L.v h29 h30 h31) hs (by simpa using hf)) fun s' hm =>
        ⟨V, H, _, _, h29, h30, h31, hm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s1]) (.block initState)
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, b₁, _, h₁⟩ ⟨_, _, _, _, _, b₂, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.s1, h₂.env.s1, b₁, b₂]⟩) hc

end

end VG.Proof.AesGcm.RISCV64
