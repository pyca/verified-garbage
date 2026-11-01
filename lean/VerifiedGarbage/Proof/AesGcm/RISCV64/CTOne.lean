module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.AesGcm.RISCV64


/-!
# AES-GCM on RISCV64: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOne.lean`): the invariants fix the context, the state
at `W + 16`, `W`, the stack pointer, the rounds, the nonce, the additional
data and the data (their addresses and lengths, held in registers the
environment pins or, for the addresses of the additional data and the data,
in `W`), and leave the rest existential; their correctness lemmas carry them
from one piece to the next.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The registers and buffers of `seal` and `open` after the entry: the
context `c`, `W`, `R` rounds, the `n`-byte nonce (length in `s7`), the
additional data (`Ad` in `W + aadO`, length in `s10`) and the data (`D` in
`W + dataO`, length in `s11`). -/
def OneI (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = W + BitVec.ofNat 64 16 ∧ V .s0 = W ∧
    V .s3 = BitVec.ofNat 64 R ∧ V .s7 = BitVec.ofNat 64 n ∧ V .s10 = A ∧ V .s11 = Ln ∧ Env V sp s ∧
    DataOk (W + BitVec.ofNat 64 16) W s Np n ∧ DataOk (W + BitVec.ofNat 64 16) W s Ad A.toNat ∧
    DataW c (W + BitVec.ofNat 64 16) W s D Ln.toNat ∧ s.mem.readW (W + BitVec.ofNat 64 aadO) 64 = Ad ∧
    s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln : BitVec 64}

/-- `OneI`, after code that keeps the frozen registers, the regions and the
slots of `W`. -/
theorem OneI.keep {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (ha : s'.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s.mem.readW (W + BitVec.ofNat 64 aadO) 64)
    (hd : s'.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s.mem.readW (W + BitVec.ofNat 64 dataO) 64) :
    OneI c W sp R Np n Ad A D Ln s' := by
  obtain ⟨V₀, a, b, d, e, f, i, k, he₀, hN, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, V r = V₀ r := fun r hr => (hV r hr).trans (he₀.fr r hr)
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he, hN.of_eq hrd hwr hsp, hA.of_eq hrd hwr hsp, hD.of_eq hrd hwr hsp,
    ha.trans sa, hd.trans sd⟩
  · rw [q _ (by decide), a]
  · rw [q _ (by decide), b]
  · rw [q _ (by decide), d]
  · rw [q _ (by decide), e]
  · rw [q _ (by decide), f]
  · rw [q _ (by decide), i]
  · rw [q _ (by decide), k]

/-- `OneI`, after a block that keeps the frozen registers and the memory. -/
theorem OneI.block {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W sp R Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  exact ⟨V, a, b, d, e, f, i, k, he.keep hg hk.sp hk.rd hk.wr, hN.of_eq hk.rd hk.wr hk.sp,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩

variable (L : Lay c (W + BitVec.ofNat 64 16) W)
include L

omit L in
/-- `OneI` after a piece whose frame is apart from the slots. -/
theorem OneI.frame {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneI c W sp R Np n Ad A D Ln s' :=
  h.keep hV he hrd hwr hsp (slot_keep hf (hs (by decide))) (slot_keep hf (hs (by decide)))

/-- Before `oneAad`: the nonce's address and length in `s4` and `s5`. -/
theorem oneAad_ct : CT (fun s => OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n) oneAad := by
  -- `j0`
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0)
    ((j0_ct L (Np := Np) (n := n)).mono fun s ⟨⟨V, a, b, d, _, f, _, _, he, hN, _⟩, h24, h25⟩ =>
      ⟨V, _, a, b, d, ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩⟩)
    (fun s ⟨hs, h24, h25⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr
        (j0_ok (L.v a b d) ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩)) fun s' ⟨jo, rd, wr, sp'⟩ =>
        ⟨OneI.frame hs
          (fun r hr => (he.fr r hr).symm) jo.env rd wr sp' jo.frame (fun hd' => by
            rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'), by rw [← b]; exact jo.y⟩) ?_
  -- the additional data's arguments
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0 ∧ s.gpr .s4 = Ad ∧
    s.gpr .s5 = BitVec.ofNat 64 A.toNat ∧ s.gpr .s6 = BitVec.ofNat 64 0) ?_
    (fun s ⟨hs, hy⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0, .s10])
        (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, i₁, _, h₁, _⟩, _⟩
      ⟨⟨_, _, _, d₂, _, _, i₂, _, h₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s0, h₂.s0, d₁, d₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h22 := he.ofNat (r := .s10) (by decide)
    have L' := L.v a b d
    have h₃ : WP isa (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0]) s fun s₃ =>
        s₃.gpr .s4 = Ad ∧ s₃.gpr .s5 = BitVec.ofNat 64 (V .s10).toNat ∧ s₃.gpr .s6 = BitVec.ofNat 64 0 ∧
          (∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
      refine Steps.wp_ld (off := aadO) (a := V .s0 + BitVec.ofNat 64 aadO) (by decide) (by rw [he.s0])
        (L'.wal8 (by decide) (by decide)) (he.perm.wR (by decide)) fun s₃ u₃ => ?_
      refine Steps.wp_mv fun s₄ u₄ => Steps.wp_li (imm := 0) (by decide) fun s₅ u₅ => WP.block_nil ?_
      refine ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, d, sa], by
        rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h22], u₅.gpr, fun r a b c => by
        rw [u₅.other _ c, u₄.other _ b, u₃.other _ a], ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [u₅.mem, u₄.mem, u₃.mem]
      · rw [u₅.rd, u₄.rd, u₃.rd]
      · rw [u₅.wr, u₄.wr, u₃.wr]
      · rw [u₅.sp, u₄.sp, u₃.sp]
    refine WP.mono h₃ fun s₃ ⟨a24, a25, a26, g₃, k₃⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₃ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₃,
      by rw [k₃.mem]; exact hy, a24, by rw [a25, i], a26⟩
  -- the additional data absorbed
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s) ?_
    (fun s ⟨hs, hy, h24, h25, h26⟩ => ?_) ?_
  · exact (absorb_ct L (yo := 16) (.inr rfl) (D := Ad) (n := A.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _, hA, _⟩, _, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩⟩
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    exact WP.mono (WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
      (⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩ : AbsIn V sp 16 _ [] Ad A.toNat s)))
      fun s' ⟨ab, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) ab.env rd wr sp' ab.frame
        (fun hd' => by rw [← d]; exact slot_abs (L.v a b d) he.stk' hd')
  -- padded
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧
    s.gpr .s6 = BitVec.ofNat 64 (A.toNat % 16)) ?_ (fun s hs => ?_)
    ((flush_ct L (yo := 16) (.inr rfl) (q := A.toNat % 16) (Nat.mod_lt _ (by decide))).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
        (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, i₁, _, h₁, _⟩ ⟨_, _, _, _, _, _, i₂, _, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h22 := he.fr .s10 (by decide)
    have hand := and15 (V .s10)
    have h₅ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₅ =>
        s₅.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
          (∀ r, r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h22, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₅ r (by revert r; decide)) k₅, by rw [a26, i]⟩

omit L in
theorem dataArgs_ct : CT (OneI c W sp R Np n Ad A D Ln) (.block dataArgs) := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11, .s0]) (.block dataArgs)
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, k₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, k₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- `dataArgs`, for the invariants. -/
theorem dataArgs_one {s : State} (h : OneI c W sp R Np n Ad A D Ln s) :
    WP isa (.block dataArgs) s fun s' => OneI c W sp R Np n Ad A D Ln s' ∧ s'.gpr .s4 = D ∧
      s'.gpr .s5 = BitVec.ofNat 64 Ln.toNat ∧ s'.gpr .s6 = BitVec.ofNat 64 0 := by
  have hs := h
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  exact WP.mono (dataArgs_ok he (by rw [d]; exact L.wal) (by rw [d]; exact sd)) fun s' ⟨a24, a25, a26, g₁, k₁⟩ =>
    ⟨OneI.block hs
      (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₁,
      a24, by rw [a25, k], a26⟩

theorem oneCrypt_ct (hR : R = 10 ∨ R = 12 ∨ R = 14) : CT (OneI c W sp R Np n Ad A D Ln) oneCrypt := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one L h)
    ((crypt_ct L (R := R) (D := D) (n := Ln.toNat) (q := 0)).mono fun s ⟨⟨V, a, b, d, e, _, _, _, he, _, _, hD, _⟩,
      h24, h25, h26⟩ => ⟨V, blockAt s.mem (V .s1 + BitVec.ofNat 64 48), 0, a, b, d, rfl,
        ⟨he, h24, h25, h26, e, hR, by rw [a, b, d]; exact hD⟩⟩)

theorem oneTag_ct {o : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (OneI c W sp R Np n Ad A D Ln) (oneTag o) := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one L h) ?_
  refine CT.seq (J := OneI c W sp R Np n Ad A D Ln)
    ((absorb_ct L (yo := 16) (.inr rfl) (D := D) (n := Ln.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _, _, hD, _⟩, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hD.ok, rfl⟩⟩)
    (fun s ⟨hs, h24, h25, h26⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
        (⟨he, h24, h25, h26, by rw [b, d]; exact hD.ok, rfl⟩ : AbsIn V sp 16 _ [] D Ln.toNat s)))
        fun s' ⟨ab, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) ab.env rd wr sp' ab.frame
          (fun hd' => by rw [← d]; exact slot_abs (L.v a b d) he.stk' hd')) ?_
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s6 = BitVec.ofNat 64 (Ln.toNat % 16)) ?_
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11])
        (.block [.logicImm .and .s6 .s11 15]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, k₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have hs' := hs
    obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
    have h23 := he.fr .s11 (by decide)
    have hand := and15 (V .s11)
    have h₅ : WP isa (.block [.logicImm .and .s6 .s11 15]) s fun s₅ =>
        s₅.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
          (∀ r, r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', h23, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ =>
      ⟨OneI.block hs
        (fun r hr => g₅ r (by revert r; decide)) k₅, by rw [a26, k]⟩
  have hq : Ln.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  refine CT.seq (J := OneI c W sp R Np n Ad A D Ln)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, _, he, _⟩, h26⟩ =>
      ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨hs, h26⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr (flush_ok (L.v a b d)
        (yo := 16) (.inr rfl) (x := List.replicate (Ln.toNat % 16) 0) ⟨he, rfl⟩ (by simp [h26])))
        fun s' ⟨fl, rd, wr, sp'⟩ => OneI.frame hs (fun r hr => (he.fr r hr).symm) fl.env rd wr sp' fl.frame
          (fun hd' => by rw [← d]; exact slot_t (L.v a b d) he.stk' hd')) ?_
  refine CT.seq (J := EnvR c (W + BitVec.ofNat 64 16) W sp R) ?_
    (fun s ⟨V, a, b, d, e, f, i, k, he, _⟩ => ?_) ((tag_ct L ho hR).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10, .s11])
        (.block [mov .s4 .s10, mov .s6 .s11]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, i₁, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, i₂, k₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr⟩

end

end VG.Proof.AesGcm.RISCV64
