module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Env

/-! ### `AesGcm.RISCV64.CTOne`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOpen.lean`): the invariants fix the context, the state
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
`W + dataO`, length in `s11`), which the code reads; where it writes the
data (`D` itself, or out of place another buffer) is `OD`'s. -/
def OneI (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = W + BitVec.ofNat 64 16 ∧ V .s0 = W ∧
    V .s3 = BitVec.ofNat 64 R ∧ V .s7 = BitVec.ofNat 64 n ∧ V .s10 = A ∧ V .s11 = Ln ∧ Env V sp s ∧
    DataOk (W + BitVec.ofNat 64 16) W s Np n ∧ DataOk (W + BitVec.ofNat 64 16) W s Ad A.toNat ∧
    DataOk (W + BitVec.ofNat 64 16) W s D Ln.toNat ∧ s.mem.readW (W + BitVec.ofNat 64 aadO) 64 = Ad ∧
    s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D

/-- Where `oneCryptWith o` writes the `Ln` bytes of data at `D`: to `Dst`
(`D` itself in place). -/
def OD (o : Bool) (c W : Addr) (D Dst Ln : BitVec 64) (s : State) : Prop :=
  DataW c (W + BitVec.ofNat 64 16) W s Dst Ln.toNat ∧ Alias o D Dst Ln.toNat

theorem OD.of_eq {o : Bool} {c W : Addr} {D Dst Ln : BitVec 64} {s s' : State} (h : OD o c W D Dst Ln s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : OD o c W D Dst Ln s' :=
  ⟨h.1.of_eq hrd hwr hsp, h.2⟩

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
theorem oneAad_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s4 = Np ∧
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

theorem oneCrypt_ct {o : Bool} {Dst : BitVec 64} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => OneI c W sp R Np n Ad A D Ln s ∧ OD o c W D Dst Ln s ∧ (o = true → s.gpr .s9 = Dst - D))
      (oneCryptWith o) := by
  refine CT.seq (J := fun s => (OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s4 = D ∧
      s.gpr .s5 = BitVec.ofNat 64 Ln.toNat ∧ s.gpr .s6 = BitVec.ofNat 64 0) ∧ OD o c W D Dst Ln s ∧
      (o = true → s.gpr .s9 = Dst - D)) (dataArgs_ct.mono fun s h => h.1)
    (fun s h => by
      have hs := h.1
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h.1
      exact WP.mono (dataArgs_ok he (by rw [d]; exact L.wal) (by rw [d]; exact sd)) fun s' ⟨a24, a25, a26, g₁, k₁⟩ =>
        ⟨⟨OneI.block hs (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₁,
          a24, by rw [a25, k], a26⟩,
          h.2.1.of_eq k₁.rd k₁.wr k₁.sp, fun ho => (g₁ _ (by decide) (by decide) (by decide)).trans (h.2.2 ho)⟩)
    ((crypt_ct L (o := o) (R := R) (S := D) (D := Dst) (n := Ln.toNat) (q := 0)).mono
      fun s ⟨⟨⟨V, a, b, d, e, _, _, k, he, _, _, hD, _⟩, h24, h25, h26⟩, ⟨hW, ha⟩, h9⟩ =>
        ⟨V, blockAt s.mem (V .s1 + BitVec.ofNat 64 48), 0, a, b, d, rfl,
          ⟨he, h24, h25, h26, e, hR, by rw [a, b, d]; exact hW, by rw [b, d]; exact hD, ha,
            fun ho => by rw [← he.fr .s9 (by decide)]; exact h9 ho⟩⟩)

theorem oneTag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (OneI c W sp R Np n Ad A D Ln) (oneTag o) := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one L h) ?_
  refine CT.seq (J := OneI c W sp R Np n Ad A D Ln)
    ((absorb_ct L (yo := 16) (.inr rfl) (D := D) (n := Ln.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, he, _, _, hD, _⟩, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .s2 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hD, rfl⟩⟩)
    (fun s ⟨hs, h24, h25, h26⟩ => by
      have hs' := hs
      obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hs'
      exact WP.mono (WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
        (⟨he, h24, h25, h26, by rw [b, d]; exact hD, rfl⟩ : AbsIn V sp 16 _ [] D Ln.toNat s)))
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

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 8`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the
tag's address `T` in `s9`, which the environment pins, and, between them,
the additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 8)) s₀ fun s₁ =>
      OneI (s₀.gpr .a0) (stackArg s₀ 1) s₀.sp (s₀.gpr .a1).toNat (s₀.gpr .a2) (s₀.gpr .a3).toNat (s₀.gpr .a4)
        (s₀.gpr .a5) (s₀.gpr .a6) (s₀.gpr .a7) s₁ ∧
      s₁.gpr .s4 = s₀.gpr .a2 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (s₀.gpr .a3).toNat ∧
      s₁.gpr .s9 = stackArg s₀ 0 ∧ Covers [⟨stackArg s₀ 0, 16⟩] s₁.wr ∧
      OD false (s₀.gpr .a0) (stackArg s₀ 1) (s₀.gpr .a6) (s₀.gpr .a6) (s₀.gpr .a7) s₁ := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, fW, fsp, hR, hstk,
    ca, wa⟩ := h
  have hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp :=
    one_stk hstk (by simp) (by simp)
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 1)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))).symm
  refine WP.mono (one1_wp (off := 8) (W := stackArg s₀ 1) (T := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd)
    fun s₁ h1 => ?_
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hDok : DataOk (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₁ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    ⟨covers_left hDw, (s₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  refine ⟨⟨s₁.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN,
    h1.s10, h1.s11, one_env h1 hC hW hk₀, ?_, ?_, hDok, h1.aad, h1.dat⟩, h1.s4, by rw [h1.s5]; exact toN, h1.s9, ?_,
    ⟨⟨hDok, hDw, dcd⟩, rfl⟩⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `t1`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 8 ∨ off = 16) (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 off]) s₀ fun sA =>
      sA.gpr .t1 = W ∧ (∀ r, r ≠ .t1 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := off) (a := s₀.sp + BitVec.ofNat 64 off) (by omega_using [hoff]) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega_using [hsa]) (by omega_using [hoff])) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => WP.block_nil ?_
  exact ⟨by rw [uB.gpr, uA.mem, hWv], fun r hr => by rw [uB.other r hr, uA.other r hr],
    ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- The rest of the entry, after `W` is in `t1`. -/
abbrev oneRestAt (tagO : Nat) : List Instr :=
  save .t1 ++ ([mov .s2 .a0, mov .s3 .a1, .addi .s1 .s0 16, mov .s4 .a2, mov .s5 .a3, mov .s7 .a3,
    .store .d .a4 .s0 aadO, mov .s10 .a5, .store .d .a6 .s0 dataO, mov .s11 .a7, .addSp .t1 0,
    .load .d .s9 .t1 tagO] : List Instr)

abbrev oneRest : List Instr := oneRestAt 0

theorem oneEntryAt_eq (off tagO : Nat) :
    oneEntryAt off tagO = ([.addSp .t1 0, .load .d .t1 .t1 off] : List Instr) ++ oneRestAt tagO := by
  rw [oneEntryAt, List.append_assoc]

theorem oneEntry_eq (off : Nat) : oneEntry off = ([.addSp .t1 0, .load .d .t1 .t1 off] : List Instr) ++ oneRest :=
  oneEntryAt_eq off 0

theorem oneHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 8]) h).isSome = true := ⟨_, by taint_decide⟩

theorem oneRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1]) (.block oneRest) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `s9`, which the state may write,
and the data, which it may write too. -/
def OneT (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr ∧ OD false c W D D Ln s

theorem OneT.frame {s s' : State} (h : OneT c W sp R Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneT c W sp R Np n Ad A D Ln T s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    by rw [hwr]; exact h.2.2.1, h.2.2.2.of_eq hrd hwr hsp⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L hR hTW

/-- `seal` after its entry. -/
theorem sealBody_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : CT (fun s => OneT c W sp R Np n Ad A D Ln T s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneCrypt`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneCrypt_ct L hR (o := false) (Dst := D)).mono fun s ⟨hT, _⟩ => ⟨hT.1, hT.2.2.2, Bool.noConfusion⟩)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have L' := L.v a b d
    have hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat := by rw [a, b, d, k]; exact hT.2.2.2.1
    refine WP.mono (WP.with_rdwr (oneCrypt_ok L' he e hR hd (by rw [d]; exact sd) rfl)) fun s' ⟨oc, rd, wr, sp'⟩ =>
      ⟨hT.frame (fun r hr => (he.fr r hr).symm) oc.env rd wr sp' oc.frame
        (fun hd' => by rw [← d]; exact slot_crFrame L' hd hd'), H, x, ?_, hl, ?_⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame L' hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame L' hd (by omega_using [])) (by omega_using []))
  -- `oneTag 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .s0 = W ∧ V .s9 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr) ((oneTag_ct L (.inl rfl) hR).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) (o := 0) (.inl rfl) (H := H) (a := x) (D := D) he e hR
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, _, wr, _⟩ => ⟨V, d, (he.fr _ (by decide)).symm.trans hT.2.1, ot.env, by rw [wr]; exact hT.2.2.1⟩
  -- the tag copied out
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp) ?_
    (fun s ⟨V, d, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT) (by rw [i, d]; exact hTW))
      fun s' ⟨_, _, hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, d₁, i₁, h₁, _⟩ ⟨_, d₂, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => W) sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end

theorem seal_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, fW, _, hR, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm, (qa 1 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .a0) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a2)
    (σ₁.gpr .a3).toNat (σ₁.gpr .a4) (σ₁.gpr .a5) (σ₁.gpr .a6) (σ₁.gpr .a7) (stackArg σ₁ 0) s ∧
    s.gpr .s4 = σ₁.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (σ₁.gpr .a3).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1⟩ => ?_)
    (sealBody_ct (oneLay fc fW dcW ca wa) hR (dtW.sub_right (Region.sub_prefix (by decide))))
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 1 else σ₁.gpr r
    rw [oneEntry_eq]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, ea1⟩
      have hA : Covers [args s 2] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := hs
        exact hk.1
      refine WP.mono (oneA_ok (W := stackArg s 1) (.inl rfl) hsa (args_in hA (by decide) (i := 1) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealEntry_wp hs
    rw [ea0, ea1, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT, hOD⟩ => ⟨⟨hO, h20, hT, hOD⟩, h24, h25⟩

end VG.Proof.AesGcm.RISCV64
