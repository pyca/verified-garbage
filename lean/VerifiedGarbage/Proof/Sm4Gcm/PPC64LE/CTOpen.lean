module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
public import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
meta import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
meta import VerifiedGarbage.Spec.TripleDes

/-! ### `Sm4Gcm.PPC64LE.CTSeal`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.PPC64LE.CTOne`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on PPC64LE: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTOne.lean`), with SM4's counter mode: the
invariants fix the context, the state at `W + 16`, `W`, the stack pointer,
the nonce, the additional data and the data (their addresses and lengths,
held in registers the environment pins), and leave the rest existential;
their correctness lemmas carry them from one piece to the next.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov oneAad dataArgs absorb flush)
open VG.Proof.AesGcm.PPC64LE (CT Env Lay Keeps DataOk DataW AbsIn frozen and15 j0_ct j0_ok absorb_ct
  absorb_ok flush_ct flush_ok dataArgs_ok WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The data, as SM4's counter mode needs them: also apart from its working
space `x`, which is writable. -/
structure DataX (c st w x : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  dw : DataW c st w s D n
  xw : Covers [xR x] s.wr
  dx : (⟨D, n⟩ : Region).Disjoint (xR x)

theorem DataX.of_eq {c st w x : Addr} {s s' : State} {D : Addr} {n : Nat}
    (h : DataX c st w x s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataX c st w x s' D n :=
  ⟨h.dw.of_eq hrd hwr, by rw [hwr]; exact h.xw, h.dx⟩

/-- The registers and buffers of `seal` and `open` after the entry: the
context `c`, `W`, SM4's working space `x`, the `n`-byte nonce (length in `r18`), the
additional data (`r21`, `r22`) and the data (`r27`, `r23`). -/
def OneI (c W x sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = W + BitVec.ofNat 64 16 ∧ V .r31 = W ∧ V .r28 = x ∧
    V .r18 = BitVec.ofNat 64 n ∧ V .r21 = Ad ∧ V .r22 = A ∧ V .r27 = D ∧
    V .r23 = Ln ∧ Env V sp s ∧ DataOk (W + BitVec.ofNat 64 16) W s Np n ∧
    DataOk (W + BitVec.ofNat 64 16) W s Ad A.toNat ∧ DataX c (W + BitVec.ofNat 64 16) W x s D Ln.toNat

section
variable {c W x sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln : BitVec 64}

theorem OneI.keep {s s' : State} (h : OneI c W x sp Np n Ad A D Ln s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OneI c W x sp Np n Ad A D Ln s' := by
  obtain ⟨V₀, a, b, d, e, f, g, i, j, k, he₀, hN, hA, hD⟩ := h
  have q : ∀ r ∈ frozen, V r = V₀ r := fun r hr => (hV r hr).trans (he₀.fr r hr)
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he, hN.of_eq hrd hwr, hA.of_eq hrd hwr, hD.of_eq hrd hwr⟩
  · rw [q _ (by decide), a]
  · rw [q _ (by decide), b]
  · rw [q _ (by decide), d]
  · rw [q _ (by decide), e]
  · rw [q _ (by decide), f]
  · rw [q _ (by decide), g]
  · rw [q _ (by decide), i]
  · rw [q _ (by decide), j]
  · rw [q _ (by decide), k]

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (X : XOk c (W + BitVec.ofNat 64 16) W x)
include L X

omit X in
/-- Before `oneAad`: the nonce's address and length in `r24` and `r25`. -/
theorem oneAad_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : CT (fun s => OneI c W x sp Np n Ad A D Ln s ∧ s.gpr .r24 = Np ∧
    s.gpr .r25 = BitVec.ofNat 64 n) oneAad := by
  -- `j0`
  refine CT.seq (J := fun s => OneI c W x sp Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0)
    ((j0_ct L (Np := Np) (n := n)).mono fun s ⟨⟨V, a, b, d, _, f, _, _, _, _, he, hN, _⟩, h24, h25⟩ =>
      ⟨V, _, a, b, d, ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩, h24, h25⟩ => WP.mono (WP.with_rdwr
      (j0_ok (L.v a b d) ⟨he, rfl, h24, h25, f, by rw [b, d]; exact hN⟩)) fun s' ⟨jo, rd, wr, _⟩ =>
        ⟨⟨V, a, b, d, e, f, g, i, j, k, jo.env, hN.of_eq rd wr, hA.of_eq rd wr, hD.of_eq rd wr⟩,
          by rw [← b]; exact jo.y⟩) ?_
  -- the additional data's arguments
  refine CT.seq (J := fun s => OneI c W x sp Np n Ad A D Ln s ∧
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = 0 ∧ s.gpr .r24 = Ad ∧
    s.gpr .r25 = BitVec.ofNat 64 A.toNat ∧ s.gpr .r26 = BitVec.ofNat 64 0) ?_
    (fun s ⟨⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩, hy⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r21, .r22])
        (.block [mov .r24 .r21, mov .r25 .r22, .li .r26 0]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, g₁, i₁, _, _, h₁, _⟩, _⟩
      ⟨⟨_, _, _, _, _, _, g₂, i₂, _, _, h₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have h21 := he.fr .r21 (by decide)
    have h22 := he.ofNat (r := .r22) (by decide)
    have h₃ : WP isa (.block [mov .r24 .r21, mov .r25 .r22, .li .r26 0]) s fun s₃ =>
        s₃.gpr .r24 = V .r21 ∧ s₃.gpr .r25 = BitVec.ofNat 64 (V .r22).toNat ∧
          s₃.gpr .r26 = BitVec.ofNat 64 0 ∧
          (∀ r, r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
      crun [mov, BitVec.or_self, h21, h22]
      exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    refine WP.mono h₃ fun s₃ ⟨a24, a25, a26, g₃, k₃⟩ => ⟨⟨V, a, b, d, e, f, g, i, j, k,
      he.keep (fun r hr => g₃ r (by revert r; decide) (by revert r; decide) (by revert r; decide))
        k₃.sp k₃.rd k₃.wr, hN.of_eq k₃.rd k₃.wr, hA.of_eq k₃.rd k₃.wr, hD.of_eq k₃.rd k₃.wr⟩,
      by rw [k₃.mem]; exact hy, by rw [a24, g], by rw [a25, i], a26⟩
  -- the additional data absorbed
  refine CT.seq (J := fun s => OneI c W x sp Np n Ad A D Ln s) ?_
    (fun s ⟨⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩, hy, h24, h25, h26⟩ => ?_) ?_
  · exact (absorb_ct L (yo := 16) (.inr rfl) (D := Ad) (n := A.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, _, _, he, _, hA, _⟩, _, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .r29 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩⟩
  · exact WP.mono (WP.with_rdwr (absorb_ok (L.v a b d) (.inr rfl)
      (⟨he, h24, h25, h26, by rw [b, d]; exact hA, rfl⟩ : AbsIn V sp 16 _ [] Ad A.toNat s)))
      fun s' ⟨ab, rd, wr, _⟩ => ⟨V, a, b, d, e, f, g, i, j, k, ab.env, hN.of_eq rd wr, hA.of_eq rd wr,
        hD.of_eq rd wr⟩
  -- padded
  refine CT.seq (J := fun s => OneI c W x sp Np n Ad A D Ln s ∧
    s.gpr .r26 = BitVec.ofNat 64 (A.toNat % 16)) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ => ?_)
    ((flush_ct L (yo := 16) (.inr rfl) (q := A.toNat % 16) (Nat.mod_lt _ (by decide))).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22])
        (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, i₁, _, _, h₁, _⟩ ⟨_, _, _, _, _, _, _, i₂, _, _, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
  · have h22 := he.fr .r22 (by decide)
    have hand := and15 (V .r22)
    have h₅ : WP isa (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) s fun s₅ =>
        s₅.gpr .r26 = BitVec.ofNat 64 ((V .r22).toNat % 16) ∧
          (∀ r, r ≠ .r0 → r ≠ .r26 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [h22, hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ => ⟨⟨V, a, b, d, e, f, g, i, j, k,
      he.keep (fun r hr => g₅ r (by revert r; decide) (by revert r; decide)) k₅.sp k₅.rd k₅.wr,
      hN.of_eq k₅.rd k₅.wr, hA.of_eq k₅.rd k₅.wr, hD.of_eq k₅.rd k₅.wr⟩, by rw [a26, i]⟩

omit L X in
theorem dataArgs_ct : CT (OneI c W x sp Np n Ad A D Ln) (.block dataArgs) := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r23, .r27]) (.block dataArgs)
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, j₁, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, j₂, k₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]

omit L X in
/-- `dataArgs`, for the invariants. -/
theorem dataArgs_one {s : State} (h : OneI c W x sp Np n Ad A D Ln s) :
    WP isa (.block dataArgs) s fun s' => OneI c W x sp Np n Ad A D Ln s' ∧ s'.gpr .r24 = D ∧
      s'.gpr .r25 = BitVec.ofNat 64 Ln.toNat ∧ s'.gpr .r26 = BitVec.ofNat 64 0 := by
  obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := h
  exact WP.mono (dataArgs_ok he) fun s' ⟨a24, a25, a26, g₁, k₁⟩ => ⟨⟨V, a, b, d, e, f, g, i, j, k,
    he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)) k₁.sp k₁.rd k₁.wr,
    hN.of_eq k₁.rd k₁.wr, hA.of_eq k₁.rd k₁.wr, hD.of_eq k₁.rd k₁.wr⟩, by rw [a24, j], by rw [a25, k], a26⟩

theorem oneCrypt_ct : CT (OneI c W x sp Np n Ad A D Ln) oneCrypt := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one h)
    ((crypt_ct L X (D := D) (n := Ln.toNat) (q := 0)).mono fun s ⟨⟨V, a, b, d, e, _, _, _, _, _, he, _, _, hD⟩,
      h24, h25, h26⟩ => ⟨V, blockAt s.mem (V .r30 + BitVec.ofNat 64 48), 0, a, b, d, e, rfl,
        ⟨he, h24, h25, h26, by rw [a, b, d]; exact hD.dw, by rw [e]; exact hD.xw, by rw [e]; exact hD.dx⟩⟩)

theorem oneTag_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) :
    CT (OneI c W x sp Np n Ad A D Ln) (oneTag o) := by
  refine CT.seq dataArgs_ct (fun s h => dataArgs_one h) ?_
  refine CT.seq (J := OneI c W x sp Np n Ad A D Ln)
    ((absorb_ct L (yo := 16) (.inr rfl) (D := D) (n := Ln.toNat) (q := 0) (by decide)).mono
      fun s ⟨⟨V, a, b, d, _, _, _, _, _, _, he, _, _, hD⟩, h24, h25, h26⟩ =>
        ⟨V, blockAt s.mem (V .r29 + BitVec.ofNat 64 240), [], a, b, d, rfl,
          ⟨he, h24, h25, h26, by rw [b, d]; exact hD.dw.ok, rfl⟩⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩, h24, h25, h26⟩ => WP.mono (WP.with_rdwr
      (absorb_ok (L.v a b d) (.inr rfl)
        (⟨he, h24, h25, h26, by rw [b, d]; exact hD.dw.ok, rfl⟩ : AbsIn V sp 16 _ [] D Ln.toNat s)))
      fun s' ⟨ab, rd, wr, _⟩ => ⟨V, a, b, d, e, f, g, i, j, k, ab.env, hN.of_eq rd wr, hA.of_eq rd wr,
        hD.of_eq rd wr⟩) ?_
  refine CT.seq (J := fun s => OneI c W x sp Np n Ad A D Ln s ∧ s.gpr .r26 = BitVec.ofNat 64 (Ln.toNat % 16)) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r23])
        (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, _, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, _, k₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have h23 := he.fr .r23 (by decide)
    have hand := and15 (V .r23)
    have h₅ : WP isa (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) s fun s₅ =>
        s₅.gpr .r26 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
          (∀ r, r ≠ .r0 → r ≠ .r26 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [h23, hand]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨a26, g₅, k₅⟩ => ⟨⟨V, a, b, d, e, f, g, i, j, k,
      he.keep (fun r hr => g₅ r (by revert r; decide) (by revert r; decide)) k₅.sp k₅.rd k₅.wr,
      hN.of_eq k₅.rd k₅.wr, hA.of_eq k₅.rd k₅.wr, hD.of_eq k₅.rd k₅.wr⟩, by rw [a26, k]⟩
  have hq : Ln.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  refine CT.seq (J := OneI c W x sp Np n Ad A D Ln)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, _, _, _, he, _⟩, h26⟩ =>
      ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩, h26⟩ => WP.mono (WP.with_rdwr (flush_ok (L.v a b d)
      (yo := 16) (.inr rfl) (x := List.replicate (Ln.toNat % 16) 0) ⟨he, rfl⟩ (by simp [h26])))
      fun s' ⟨fl, rd, wr, _⟩ => ⟨V, a, b, d, e, f, g, i, j, k, fl.env, hN.of_eq rd wr, hA.of_eq rd wr,
        hD.of_eq rd wr⟩) ?_
  refine CT.seq (J := EnvX c (W + BitVec.ofNat 64 16) W x sp) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, j, k, he, _, _, hD⟩ => ?_) ((tag_ct L X ho).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22, .r23])
        (.block [mov .r24 .r22, mov .r26 .r23]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, i₁, _, k₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, i₂, _, k₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), k₁, k₂]
  · have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s fun s₅ =>
        (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [mov, BitVec.or_self]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hD.xw⟩

end

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTSeal.lean`): the entry loads `W` from the stack
argument at `sp + 96`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the
tag's address `T` in `r20`, which the environment pins, and, between them,
the additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov oneAad tagOut restore save)
open VG.Proof.AesGcm.PPC64LE (CT ct_of Env Lay DataW frozen covers_mem covers_left covers_off covers_prefix
  bytesAt_frame blockAt_frame oneLay args_in oneAad_ok tagOut_ok length_bytesAt WP.with_rdwr add_ofNat_assoc savedR)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 96)) s₀ fun s₁ =>
      OneI (s₀.gpr .r3) (stackArg s₀ 0) (stackArg s₀ 1) s₀.sp (s₀.gpr .r4) (s₀.gpr .r5).toNat (s₀.gpr .r6)
        (s₀.gpr .r7) (s₀.gpr .r8) (s₀.gpr .r9) s₁ ∧
      s₁.gpr .r24 = s₀.gpr .r4 ∧ s₁.gpr .r25 = BitVec.ofNat 64 (s₀.gpr .r5).toNat ∧
      s₁.gpr .r20 = s₀.gpr .r10 ∧ Covers [⟨s₀.gpr .r10, 16⟩] s₁.wr := by
  obtain ⟨hrd, hwr, dcd, -, -, dnW, -, daW, -, ddW, -, -, dWA, -, fn, fa, fd, -, -, -, -, -, -, ddx, -, -, -, -⟩ := h
  have hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hXd : (⟨s₀.sp + BitVec.ofNat 64 (96 + 8), 8⟩ : Region).Disjoint (savedR (stackArg s₀ 0)) := by
    have hs := VG.Offset.sub_base (s₀.sp + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide)
    rw [add_ofNat_assoc] at hs
    exact ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm).sub_left hs
  refine WP.mono (one1_wp (off := 96) (W := stackArg s₀ 0) (X := stackArg s₀ 1) (.inl rfl) hW
    (args_in hA (by decide) (i := 0) (by decide)) rfl (args_in hA (by decide) (i := 1) (by decide)) rfl hXd)
    fun s₁ h1 => ?_
  have hk₁ := h1.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hX₁ : Covers [xR (stackArg s₀ 1)] s₁.wr := by rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨s₁.gpr, h1.r29, h1.r30, h1.r31, h1.r28, by rw [h1.r18]; exact toN, h1.r21,
    h1.r22, h1.r27, h1.r23, one_env h1 hC hW, ?_, ?_, ⟨⟨⟨covers_left hDw, (s₀.gpr .r9).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩, hX₁, ddx⟩⟩, h1.r24, by rw [h1.r25]; exact toN, h1.r20, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r5).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r7).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)

theorem oneHead_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [])
    (.block [.addSp .r12 0, .load .d .r12 .r12 96]) h).isSome = true := ⟨_, by taint_decide⟩

theorem oneRest_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12])
    (.block (save .r12 ++ ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5,
      mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0,
      .load .d .r28 .r12 (96 + 8)] : List Instr))) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {c W x sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `r20`, which the state may write. -/
def OneT (c W x sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W x sp Np n Ad A D Ln s ∧ s.gpr .r20 = T ∧ Covers [⟨T, 16⟩] s.wr

theorem OneT.keep {s s' : State} (h : OneT c W x sp Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OneT c W x sp Np n Ad A D Ln T s' :=
  ⟨h.1.keep hV he hrd hwr, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1), by rw [hwr]; exact h.2.2⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (X : XOk c (W + BitVec.ofNat 64 16) W x)
  (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L X hTW

/-- `seal` after its entry. -/
theorem sealBody_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : CT (fun s => OneT c W x sp Np n Ad A D Ln T s ∧ s.gpr .r24 = Np ∧
    s.gpr .r25 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W x sp Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, g, i]; exact hA))) fun s' ⟨oa, rd, wr, _⟩ => ⟨hT.keep (fun r hr => (he.fr r hr).symm) oa.env rd wr,
        blockAt s.mem (V .r29 + BitVec.ofNat 64 240), bytesAt s.mem (V .r21) (V .r22).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneCrypt`
  refine CT.seq (J := fun s => OneT c W x sp Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneCrypt_ct L X).mono fun s ⟨hT, _⟩ => hT.1) (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have L' := L.v a b d
    have X' : XOk (V .r29) (V .r30) (V .r31) (V .r28) := by rw [a, b, d, e]; exact X
    have hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by rw [a, b, d, j, k]; exact hD.dw
    refine WP.mono (WP.with_rdwr (oneCrypt_ok L' X' he hd (by rw [e]; exact hD.xw) (by rw [j, k, e]; exact hD.dx)
      rfl)) fun s' ⟨oc, rd, wr, _⟩ =>
      ⟨hT.keep (fun r hr => (he.fr r hr).symm) oc.env rd wr, H, x, ?_, hl, ?_⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' X' hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame X' hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame X' hd (by omega_using [])) (by omega_using []))
  -- `oneTag 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .r31 = W ∧ V .r20 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr) ((oneTag_ct L X (.inl rfl)).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have X' : XOk (V .r29) (V .r30) (V .r31) (V .r28) := by rw [a, b, d, e]; exact X
    refine WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) X' (o := 0) (.inl rfl) (H := H) (a := x) he
      (by rw [e]; exact hD.xw) (by rw [a]; exact hH)
      (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, j, k]; exact hD.dw.ok)))
      fun s' ⟨ot, _, wr, _⟩ => ⟨V, d, (he.fr _ (by decide)).symm.trans hT.2.1, ot.env, by rw [wr]; exact hT.2.2⟩
  -- the tag copied out
  refine CT.seq (J := fun s => s.gpr .r31 = W ∧ s.sp = sp) ?_
    (fun s ⟨V, d, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT) (by rw [i, d]; exact hTW))
      fun s' ⟨_, _, hg, hk⟩ => ⟨by rw [hg _ (by decide), he.r31, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, d₁, i₁, h₁, _⟩ ⟨_, d₂, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => W) sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end

theorem seal_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, dcx, _, _, _, _, dwx, _, fx⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm, (qa 1 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .r3) (stackArg σ₁ 0) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .r4)
    (σ₁.gpr .r5).toNat (σ₁.gpr .r6) (σ₁.gpr .r7) (σ₁.gpr .r8) (σ₁.gpr .r9) (σ₁.gpr .r10) s ∧
    s.gpr .r24 = σ₁.gpr .r4 ∧ s.gpr .r25 = BitVec.ofNat 64 (σ₁.gpr .r5).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1⟩ => ?_)
    (sealBody_ct (oneLay fc fW dcW) (oneX fx dcx dwx) (dtW.sub_right (Region.sub_prefix (by decide))))
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .r12 then stackArg σ₁ 0 else σ₁.gpr r
    have hl : oneEntry 96 = [.addSp .r12 0, .load .d .r12 .r12 96] ++ (save .r12 ++
        ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5,
          mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0,
          .load .d .r28 .r12 (96 + 8)] : List Instr)) := by
      rw [oneEntry, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, _⟩
      have hA : Covers [args s 2] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      refine WP.mono (oneA_ok (W := stackArg s 0) (.inl rfl) (args_in hA (by decide) (i := 0) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea0, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealEntry_wp hs
    rw [ea0, ea1, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT⟩ => ⟨⟨hO, h20, hT⟩, h24, h25⟩

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-! ### `Sm4Gcm.PPC64LE.Open`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/Open.lean`), with SM4's counter mode: `open` checks
the tag length; if it is allowed, it computes the tag of the ciphertext into
`W + 112` (`oneAad`, `oneTag 112`), copies the received tag to `W + 256` and
compares the first `tag_len` bytes of each (`recv`, `cmp 112`), and decrypts
the data in place only if they are equal; `r3` is the result (`open_wp`).
Until the data is decrypted, everything `open` writes is in the working
space `W` and SM4's (`Frame (WX W X)`), which every buffer is apart from.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov recv cmp tagLenOk oneAad)
open VG.Proof.AesGcm.PPC64LE (Env Env.self Keeps Lay DataW DataOk SavedAt savedR frozen restore_ok covers_mem covers_left
  covers_off covers_prefix bytesAt_frame blockAt_frame ctxH_keep saved_w WP.with_rdwr saved_j0Frame oneAad_ok
  oneLay args_in j0Frame length_bytesAt tagLenOk_bounds recv_ok cmp_ok tagLenOk_ok eval_zero ld_ok bytesAt_take
  add_ofNat_assoc)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH fullTag zeros padLen j0 inc32 gctr decryptWith openResult)
open VG.Spec.Sm4.Gcm (ctxCiph)

/-- What `open` promises, given the result `r3` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r3 = 1 ∧ bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = pt
  | none => s.gpr .r3 = 0 ∧ bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r3 = 0)
    (hd : bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r3 = 1)
    (hd : bytesAt s.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  r31 : s.gpr .r31 = stackArg s₀ 1
  sp : s.sp = s₀.sp
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  post : OpenPost s₀ s

/-- The working spaces, AES-GCM's `W` and SM4's `X`. -/
abbrev WX (W X : Addr) : List Region := [⟨W, scrBytes⟩, ⟨X, xBytes⟩]

section
variable {W x : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in the working spaces. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [j0Frame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W x 112, ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ scrBytes) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ hd⟩

theorem inW_saved : ∀ r ∈ [savedR W], ∃ r' ∈ WX W x, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base _ (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (X : XOk c (W + BitVec.ofNat 64 16) W x) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W x 112 ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := W + BitVec.ofNat 64 16) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide))
      (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact X.sx.sub_left (Lay.stSub (by decide))
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

end

/-- A buffer apart from the working spaces is as it was. -/
theorem bytes_W {m m' : Mem} {W X p : Addr} {n : Nat} (hf : Frame (WX W X) m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, scrBytes⟩) (hx : (⟨p, n⟩ : Region).Disjoint ⟨X, xBytes⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hx) hn

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3))
      (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) (bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat)
      (bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat)).take (stackArg s₀ 0).toNat =
    bytesAt s₀.mem (s₀.gpr .r10) (stackArg s₀ 0).toNat

/-- After the tags are compared, with the result in `r19`, from `s₄` (after
the entry). -/
structure OpenMid (s₀ s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .r19 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem (stackArg s₀ 1) s₀
  frame : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s.mem
  cb : blockAt s.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat))
  r19 : s.gpr .r19 = BitVec.ofNat 64 (if openTagOk s₀ then 1 else 0)

/-- `open`, once the tag length is allowed, up to the comparison of the tags,
followed by any `T`. -/
theorem open_head [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) {T : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMid s₀ s₄ s₉ → WP isa T s₉ Q) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3]) T))))) s₄ Q := by
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, dcx, dnx,
    dax, ddx, dtx, dwx, dxA, fx⟩ := hh
  obtain hW' : Covers [⟨stackArg s₀ 1, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hXw : Covers [xR (stackArg s₀ 2)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  obtain L₀ := oneLay fc fW dcW
  obtain hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := covers_prefix hW' (by decide)
  obtain he₄ := one_env h4 hC hW
  obtain L := L₀.v h4.r29 h4.r30 h4.r31
  obtain X₀ := oneX fx dcx dwx
  obtain X : XOk (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) (s₄.gpr .r28) := by
    rw [h4.r29, h4.r30, h4.r31, h4.r28]; exact X₀
  have hk₄ := h4.en.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ WX (stackArg s₀ 1) (stackArg s₀ 2), (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact dcx
  obtain F₄ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₄.mem := h4.en.frame.sub inW_saved
  -- `oneAad`
  obtain hN : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₀.gpr .r4) (s₀.gpr .r5).toNat := by
    rw [h4.r30, h4.r31]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r5).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  obtain hAd : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r21) (s₄.gpr .r22).toNat := by
    rw [h4.r30, h4.r31, h4.r21, h4.r22]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .r7).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.r24 (by rw [h4.r25]; exact toN)
    (by rw [h4.r18]; exact toN) hN hAd)) fun s₅ ⟨oa, rd₅, wr₅, _⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.r30, h4.r31] at f₅
  obtain F₅ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  obtain hDw₄ : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  obtain hd₄ : DataW (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
    rw [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .r9).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw₄, dcd⟩
  obtain hxw₅ : Covers [xR (s₄.gpr .r28)] s₅.wr := by
    rw [wr₅, hk₄.wr, h4.r28]; exact hXw
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L X (o := 112) (.inr rfl) oa.env hxw₅ oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hd₄.ok.of_eq rd₅ wr₅))) fun s₆ ⟨ot, rd₆, wr₆, _⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.r30, h4.r31, h4.r28] at f₆
  obtain F₆ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  obtain h19' : s₄.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; exact toN
  obtain hTr : Covers [⟨s₄.gpr .r20, (stackArg s₀ 0).toNat⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.r20]
    exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hTd : (⟨s₄.gpr .r20, (stackArg s₀ 0).toNat⟩ : Region).Disjoint ⟨s₄.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.r20, h4.r31]; exact dtW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (recv_ok ot.env h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  obtain he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.r31] at hf₇ hb₇
  obtain F₇ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  obtain he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.r31] at hf₈ h3₈
  obtain F₈ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat
  let a := bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat
  let tg := bytesAt s₀.mem (s₀.gpr .r10) (stackArg s₀ 0).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3)
  let H := ctxH s₀.mem (s₀.gpr .r3)
  obtain hH₄ : blockAt s₄.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [h4.r29]; exact ctxH_keep F₄ dcF
  obtain iv₄ : bytesAt s₄.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat = iv :=
    bytes_W F₄ dnW dnx (by have := (s₀.gpr .r5).isLt; omega_arith)
  obtain a₄ : bytesAt s₄.mem (s₄.gpr .r21) (s₄.gpr .r22).toNat = a := by
    rw [h4.r21, h4.r22]; exact bytes_W F₄ daW dax (by have := (s₀.gpr .r7).isLt; omega_arith)
  obtain ct₅ : bytesAt s₅.mem (s₄.gpr .r27) (s₄.gpr .r23).toNat = ct := by
    rw [h4.r27, h4.r23]; exact bytes_W F₅ ddW ddx (by have := (s₀.gpr .r9).isLt; omega_arith)
  obtain hc₅ : ciphOf s₅.mem (s₄.gpr .r29) = ciph := by rw [h4.r29]; exact ciph_keep F₅ dcF
  obtain hj₅ : blockAt s₅.mem (s₄.gpr .r30) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  obtain hT₆ : bytesAt s₆.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.r31, hc₅, hj₅, ct₅, ← h4.r31, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.r31]; exact ho
  obtain hT₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  obtain hr₇ : bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 0).toNat) := by
    rw [hb₇, h4.r20]; congr 1; exact bytes_W F₆ dtW dtx (by omega_arith)
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 0).toNat = tg
  obtain hX : (bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 112) (stackArg s₀ 0).toNat ++
      zeros (16 - (stackArg s₀ 0).toNat) = bytesAt s₇.mem (stackArg s₀ 1 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  obtain r3₈ : s₈.gpr .r3 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  obtain dat₈ : bytesAt s₈.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = ct :=
    bytes_W F₈ ddW ddx (by have := (s₀.gpr .r9).isLt; omega_arith)
  obtain cb₈ : blockAt s₈.mem (stackArg s₀ 1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    obtain f₆₈ : Frame (otFrame (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) (stackArg s₀ 2) 112 ++
        [⟨stackArg s₀ 1 + BitVec.ofNat 64 256, 16⟩, ⟨stackArg s₀ 1 + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
      ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp)
    rw [blockAt_frame f₆₈ (cb_ot L₀ X₀), ← h4.r30, oa.cb, hH₄, iv₄]
  obtain sv₈ : SavedAt s₈.mem (stackArg s₀ 1) s₀ :=
    (((h4.en.saved.frame f₅ (saved_j0Frame L₀)).frame f₆ (saved_otFrame L₀ X₀ (.inr rfl))).frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame hf₈
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `r19`
  obtain ⟨s₉, run₉, h19₉, g₉, k₉⟩ : ∃ s₉, runBlock isa [mov .r19 .r3] s₈ = some s₉ ∧ s₉.gpr .r19 = s₈.gpr .r3 ∧
      (∀ r, r ≠ .r19 → s₉.gpr r = s₈.gpr r) ∧ Keeps s₈ s₉ := by
    refine ⟨_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · simp [State.write]
    · intro r hr; simp [State.write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain he₉ := Env.self he₈ g₉ k₉
  obtain e : ∀ r ∈ frozen, r ≠ .r19 → s₉.gpr r = s₄.gpr r := fun r hf hr => (g₉ r hr).trans (he₈.fr r hf)
  obtain rd₉ : s₉.rd = s₄.rd := k₉.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans rd₅)))
  obtain wr₉ : s₉.wr = s₄.wr := k₉.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans wr₅)))
  refine k s₉ ⟨he₉, e, rd₉, wr₉, k₉.mem ▸ sv₈, k₉.mem ▸ F₈, by rw [k₉.mem]; exact cb₈, ?_⟩
  rw [h19₉, r3₈]
  show _ = BitVec.ofNat 64 (if X then 1 else 0)
  by_cases hx : X
  · simp only [eq_true hx, ite_true]; rfl
  · simp only [eq_false hx, ite_false]; rfl

/-- `open` from the comparison's result on. -/
theorem open_tail {s₀ s₄ s₉ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) (om : OpenMid s₀ s₄ s₉) :
    WP isa (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19])) s₉ (OpenOut s₀) := by
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, dcx, dnx,
    dax, ddx, dtx, dwx, dxA, fx⟩ := hh
  obtain hW' : Covers [⟨stackArg s₀ 1, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hXw : Covers [xR (stackArg s₀ 2)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain L₀ := oneLay fc fW dcW
  have hk₄ := h4.en.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ WX (stackArg s₀ 1) (stackArg s₀ 2), (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact dcx
  obtain hDw₄ : Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] s₄.wr := by
    rw [hk₄.wr, hwr]; exact covers_mem (by simp)
  obtain hd₄ : DataW (s₄.gpr .r29) (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
    rw [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23]
    exact ⟨⟨covers_left hDw₄, (s₀.gpr .r9).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw₄, dcd⟩
  obtain X₀ := oneX fx dcx dwx
  let iv := bytesAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3)
  let H := ctxH s₀.mem (s₀.gpr .r3)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  obtain dat₉ : bytesAt s₉.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = ct :=
    bytes_W F₉ ddW ddx (by have := (s₀.gpr .r9).isLt; omega_arith)
  obtain hd₉₀ : DataW (s₀.gpr .r3) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₉ (s₀.gpr .r8)
      (s₀.gpr .r9).toNat := by
    have := hd₄.of_eq rd₉ wr₉
    rwa [h4.r29, h4.r30, h4.r31, h4.r27, h4.r23] at this
  -- the data decrypted only if the tags are equal
  obtain mid : WP isa (.ite (.zero .d .r19) (.block []) oneCrypt) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 1) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      ((openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬(openTagOk s₀) → bytesAt s₁₀.mem (s₀.gpr .r8) (s₀.gpr .r9).toNat = ct) := by
    refine WP.ite _ (eval_zero om.r19 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(openTagOk s₀) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨he₉, sv₉, rd₉, wr₉, fun x => absurd x hx, fun _ => dat₉⟩
    · have hx : (openTagOk s₀) := Classical.byContradiction fun x => by simp [x] at hf
      obtain L₉ : Lay (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r29, h4.r30,
          h4.r31]
        exact L₀
      obtain hd₉ : DataW (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) s₉ (s₉.gpr .r27) (s₉.gpr .r23).toNat := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide), e _ (by decide) (by decide)]
        exact hd₄.of_eq rd₉ wr₉
      obtain X₉ : XOk (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) (s₉.gpr .r28) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
          e _ (by decide) (by decide), h4.r29, h4.r30, h4.r31, h4.r28]
        exact X₀
      obtain hxw₉ : Covers [xR (s₉.gpr .r28)] s₉.wr := by
        rw [e _ (by decide) (by decide), h4.r28, wr₉, hk₄.wr]; exact hXw
      obtain hdx₉ : (⟨s₉.gpr .r27, (s₉.gpr .r23).toNat⟩ : Region).Disjoint (xR (s₉.gpr .r28)) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r27, h4.r23,
          h4.r28]
        exact ddx
      obtain cb₉ : blockAt s₉.mem (s₉.gpr .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide), h4.r30]; exact om.cb
      refine WP.mono (WP.with_rdwr (oneCrypt_ok L₉ X₉ he₉ hd₉ hxw₉ hdx₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide),
        e _ (by decide) (by decide), h4.r30, h4.r28, h4.r27, h4.r23] at cf
      refine ⟨oc.env, sv₉.frame cf (saved_crFrame L₀ X₀ hd₉₀), rd₁₀.trans rd₉, wr₁₀.trans wr₉, fun _ => ?_,
        fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r27, h4.r23,
        h4.r29, ciph_keep F₉ dcF, dat₉] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨he₁₀, sv₁₀, rd₁₀, wr₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `r3`
  refine WP.of_runBlock ⟨_, rfl, ?_⟩
  obtain g₁₁ : ∀ r, r ≠ .r3 → (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr r = s₁₀.gpr r := fun r hr => by
    simp [State.write, hr]
  obtain r3₁₁ : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = if (openTagOk s₀) then 1 else 0 := by
    have : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = s₁₀.gpr .r19 := by simp [State.write]
    rw [this, he₁₀.fr _ (by decide), om.r19]
    by_cases hx : openTagOk s₀
    · simp only [eq_true hx, ite_true]; rfl
    · simp only [eq_false hx, ite_false]; rfl
  obtain hres : openRes s₀ = if (openTagOk s₀) then some (gctr ciph (inc32 (j0 H iv)) ct) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]; rfl
  refine ⟨by rw [g₁₁ _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.r31],
    by simp only [State.write]; exact he₁₀.sp, fun r hr => ?_, by simp only [State.write]; rw [rd₁₀, hk₄.rd],
    by simp only [State.write]; rw [wr₁₀, hk₄.wr], by simp only [State.write]; exact sv₁₀, ?_⟩
  · have hf : r ∈ frozen := by revert hr; revert r; decide
    rw [g₁₁ r (by revert hr; revert r; decide), he₁₀.fr r hf, e r hf (by revert hr; revert r; decide)]
    exact h4.en.low r hr
  · by_cases hx : (openTagOk s₀)
    · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx)))
        (r3₁₁.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (hd₁ hx)
    · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx)))
        (r3₁₁.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (hd₂ hx)


theorem open_good [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ s₄ : State} (h : openPre s₀) (h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄)
    (h19 : s₄.gpr .r19 = stackArg s₀ 0) (hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19]))))))) s₄ (OpenOut s₀) :=
  open_head h h4 h19 hok fun _ om => open_tail h h4 hok om

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .r3 = s.gpr .r3) :
    openPPC64LE.post s₀ s' := by
  unfold OpenPost at op
  unfold openPPC64LE
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- `tag_len` into `r19`. -/
theorem tl_ok {s : State} {v : BitVec 64} (hi : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8)
    (hv : s.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = v) :
    WP isa (.block [.addSp .r12 0, .load .d .r19 .r12 96]) s fun s' =>
      s'.gpr .r19 = v ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r19 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.write, Size.bytes,
    hi, Proof.Gcm.PPC64LE.read_8, hv, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true, Nat.reduceLT, Nat.reducePow, Nat.reduceMod, ↓reduceIte,
    and_self, implies_true, BitVec.setWidth_eq, BitVec.add_zero]
  exact ⟨trivial, fun r a b c => by simp [b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The entry of `open`, and `tag_len` in `r19`. -/
theorem openEntry_wp {s₀ : State} (h : openPre s₀) :
    WP isa (.block openEntry) s₀ fun s₂ =>
      SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₂ ∧ s₂.gpr .r19 = stackArg s₀ 0 := by
  have hh := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, dXA, -⟩ := hh
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dA : (args s₀ 3).Disjoint (savedR (stackArg s₀ 1)) :=
    (dXA.sub_left (VG.Offset.sub_base _ (d := 128) (n := 120) (by decide))).symm
  obtain hTd : (⟨s₀.sp + BitVec.ofNat 64 96, 8⟩ : Region).Disjoint (savedR (stackArg s₀ 1)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))
  obtain hXd : (⟨s₀.sp + BitVec.ofNat 64 (104 + 8), 8⟩ : Region).Disjoint (savedR (stackArg s₀ 1)) := by
    obtain hs := VG.Offset.sub_base (s₀.sp + BitVec.ofNat 64 96) (d := 16) (n := 8) (k := 24) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 104) (W := stackArg s₀ 1) (X := stackArg s₀ 2) (.inr rfl) hW
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 2) (by decide)) rfl hXd)
    fun s₁ h1 => ?_)
  obtain hi : InRegions (s₁.rd ++ s₁.wr) (s₁.sp + BitVec.ofNat 64 96) 8 := by
    rw [h1.en.keeps.sp, h1.en.keeps.rd, h1.en.keeps.wr]; exact args_in hA (by decide) (i := 0) (by decide)
  obtain hv : s₁.mem.readW (s₁.sp + BitVec.ofNat 64 96) 64 = stackArg s₀ 0 := by
    rw [h1.en.keeps.sp, Frame.readW h1.en.frame (r := ⟨s₀.sp + BitVec.ofNat 64 96, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd) (by decide)]
    rfl
  refine WP.mono (tl_ok hi hv) fun s₂ ⟨h19, g₂, k₂⟩ => ?_
  exact ⟨h1.keep g₂ k₂, h19⟩

theorem open_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : openPPC64LE.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openPPC64LE.post s₀ s' := by
  have h' : openPre s₀ := h
  have hh := h'
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, dcx, dnx,
    dax, ddx, dtx, dwx, dxA, fx⟩ := hh
  obtain hW' : Covers [⟨stackArg s₀ 1, scrBytes⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hXw : Covers [xR (stackArg s₀ 2)] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := covers_prefix hW' (by decide)
  unfold «open»
  refine WP.seq (WP.mono (openEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  obtain h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 0).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 0).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  obtain F₂ : Frame (WX (stackArg s₀ 1) (stackArg s₀ 2)) s₀.mem s₂.mem := h2.en.frame.sub inW_saved
  obtain mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) openGood) s₃ (OpenOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
        · rfl
        · simp [e] at ht
      obtain h₀ : WP isa (.block [.li .r3 0]) s₃ fun s' => s'.gpr .r3 = 0 ∧
          (∀ r, r ≠ .r3 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
      · rw [g _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.r31
      · rw [k.sp, k₃.sp]; exact h2.en.keeps.sp
      · rw [g r (by revert hr; revert r; decide), g₃ r (by revert hr; revert r; decide)
          (by revert hr; revert r; decide)]
        exact h2.en.low r hr
      · rw [k.rd, k₃.rd]; exact h2.en.keeps.rd
      · rw [k.wr, k₃.wr]; exact h2.en.keeps.wr
      · rw [k.mem, k₃.mem]; exact h2.en.saved
      · refine openPost_none (by simp only [openRes, openResult, hbad]; rfl) z3 ?_
        rw [k.mem, k₃.mem]
        exact bytes_W F₂ ddW ddx (by have := (s₀.gpr .r9).isLt; omega_arith)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 0).toNat
        · simp [e] at hf
        · rfl
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      let s₄ := s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)
      obtain g₄ : ∀ r, r ≠ .r0 → r ≠ .r19 → s₄.gpr r = s₂.gpr r := fun r h0 h19 => by
        by_cases e : r = .r25
        · subst e
          have : s₄.gpr .r25 = s₃.gpr .r18 := by simp [s₄, State.write]
          rw [this, g₃ _ (by decide) (by decide), h2.r18, h2.r25]
        · have : s₄.gpr r = s₃.gpr r := by simp [s₄, State.write, e]
          rw [this, g₃ r h0 e]
      obtain h4 : SO1 (stackArg s₀ 1) (stackArg s₀ 2) s₀ s₄ := h2.keep (fun r h0 _ h19 => g₄ r h0 h19) ⟨k₃.mem, k₃.rd, k₃.wr, k₃.sp, k₃.lr⟩
      obtain e19 : s₄.gpr .r19 = s₃.gpr .r19 := by simp [s₄, State.write]
      exact open_good h' h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out oo.post hm h3⟩

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_open` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTOpen.lean`): `open` branches on the tag length, which
is public, and on whether the tags are equal, which it may leak (its
contract's `pub`: whether it succeeds). The invariants of the pieces up to
that comparison carry what the rest of each run reaches (`CT.seqG`, from
`open_head`): the result in `r19`, which is then the same in both runs.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov oneAad recv cmp tagLenOk save restore)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.seqG Env Env.self Lay Keeps DataW frozen covers_mem covers_left
  covers_off covers_prefix oneLay args_in oneAad_ok length_bytesAt recv_ok cmp_ok tagLenOk_ok tagLenOk_bounds
  eval_zero recv_taint tagLenOk_taint' cmp112_taint nil_taint Res WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 0).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Sm4.Gcm.ctxCiph t.mem (t.gpr .r3))
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .r3)) (bytesAt t.mem (t.gpr .r4) (t.gpr .r5).toNat)))
        (bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openHead_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [])
    (.block [.addSp .r12 0, .load .d .r12 .r12 104]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openRest_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12])
    (.block (save .r12 ++ (([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5,
      mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0,
      .load .d .r28 .r12 (104 + 8)] : List Instr) ++
      ([.addSp .r12 0, .load .d .r19 .r12 96] : List Instr)))) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `OneI`, with the tag's address `T` and length `TL` in `r20` and `r19`. -/
def OneO (c W x sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln T TL : BitVec 64) (s : State) : Prop :=
  OneI c W x sp Np n Ad A D Ln s ∧ s.gpr .r20 = T ∧ s.gpr .r19 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr)

section
variable {c W x sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln T TL : BitVec 64}

theorem OneO.keep {s s' : State} (h : OneO c W x sp Np n Ad A D Ln T TL s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    OneO c W x sp Np n Ad A D Ln T TL s' :=
  ⟨h.1.keep hV he hrd hwr, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2⟩

/-- `OneI` after a step that changes only `r19` among the registers it pins. -/
theorem OneI.self {s s' : State} (h : OneI c W x sp Np n Ad A D Ln s) (hg : ∀ r, r ≠ .r19 → s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W x sp Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := h
  have q : ∀ r ∈ frozen, r ≠ .r19 → s'.gpr r = V r := fun r hr h19 => (hg r h19).trans (he.fr r hr)
  refine ⟨s'.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Env.self he hg hk, hN.of_eq hk.rd hk.wr, hA.of_eq hk.rd hk.wr,
    hD.of_eq hk.rd hk.wr⟩
  · rw [q _ (by decide) (by decide), a]
  · rw [q _ (by decide) (by decide), b]
  · rw [q _ (by decide) (by decide), d]
  · rw [q _ (by decide) (by decide), e]
  · rw [q _ (by decide) (by decide), f]
  · rw [q _ (by decide) (by decide), g]
  · rw [q _ (by decide) (by decide), i]
  · rw [q _ (by decide) (by decide), j]
  · rw [q _ (by decide) (by decide), k]

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (X : XOk c (W + BitVec.ofNat 64 16) W x)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool)
include L X hTd t1 t16

/-- `open` from `oneAad` on, once the tag length is allowed, with what the
comparison of the tags gives (`Res b`). -/
theorem openGood_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : CT (fun s => (OneO c W x sp Np n Ad A D Ln T TL s ∧ s.gpr .r24 = Np ∧
    s.gpr .r25 = BitVec.ofNat 64 n) ∧ WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112)
      (.seq (.block [mov .r19 .r3]) (.block [])))))) s (Res b))
    (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCrypt) (.block [mov .r3 .r19]))))))) := by
  -- `oneAad`
  refine CT.seqG (J := fun s => OneO c W x sp Np n Ad A D Ln T TL s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, g, i]; exact hA))) fun s' ⟨oa, rd, wr, _⟩ => ⟨hT.keep (fun r hr => (he.fr r hr).symm) oa.env rd wr,
        blockAt s.mem (V .r29 + BitVec.ofNat 64 240), bytesAt s.mem (V .r21) (V .r22).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneTag 112`
  refine CT.seqG (J := OneO c W x sp Np n Ad A D Ln T TL) ((oneTag_ct L X (.inr rfl)).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have X' : XOk (V .r29) (V .r30) (V .r31) (V .r28) := by rw [a, b, d, e]; exact X
    exact WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) X' (o := 112) (.inr rfl) (H := H) (a := x) he
      (by rw [e]; exact hD.xw) (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab)
      (by rw [b, d, j, k]; exact hD.dw.ok)))
      fun s' ⟨ot, rd, wr, _⟩ => hT.keep (fun r hr => (he.fr r hr).symm) ot.env rd wr
  -- `recv`
  refine CT.seqG (J := OneO c W x sp Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have h19 : V .r19 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .r20 = T := by rw [← he.fr _ (by decide), hT.2.1]
    exact WP.mono (recv_ok he h19 t1 t16 (by rw [h20]; exact hT.2.2.2) (by rw [h20, d]; exact hTd))
      fun s' ⟨_, _, g', k'⟩ => hT.keep (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr
  -- `cmp 112`
  refine CT.seqG (J := OneO c W x sp Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := cmp112_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, _, _, h₁, _⟩, _, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, _, _, h₂, _⟩, _, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b₁, b₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, g, i, j, k, he, hN, hA, hD⟩ := hT.1
    have h19 : V .r19 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    exact WP.mono (cmp_ok he (o := 112) (.inr rfl) h19 t1 t16)
      fun s' ⟨_, _, g', k'⟩ => hT.keep (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr
  -- the result into `r19`
  refine CT.seqG (J := OneI c W x sp Np n Ad A D Ln) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [mov .r19 .r3] (.inr (.inr (.inl rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨⟨_, _, _, _, _, _, _, _, _, _, h₁, _⟩, _⟩ => ⟨h₁.sp, by simp⟩) hc
  · refine WP.of_runBlock ⟨_, rfl, hT.1.self (fun r hr => ?_) ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [State.write, hr]
  -- the data decrypted only if the tags are equal, which both runs agree on
  have ev : ∀ s, OneI c W x sp Np n Ad A D Ln s ∧ WP isa (.block []) s (Res b) →
      isa.eval (.zero .d .r19) s = some (decide ((if b then 1 else 0) = 0)) := fun s h =>
    eval_zero (WP.block_nil_iff.mp h.2) (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .r31 = W ∧ s.sp = sp)
    (CT.ite _ ev (fun _ => CT.skip) (fun _ => (oneCrypt_ct L X).mono fun s h => h.1)) (fun s h => ?_) ?_
  · obtain ⟨V, a, b', d, e, f, g, i, j, k, he, hN, hA, hD⟩ := h.1
    refine WP.ite _ (ev s h) (fun _ => WP.block_nil_iff.mpr ⟨by rw [he.r31, d], he.sp⟩) (fun _ => ?_)
    have X' : XOk (V .r29) (V .r30) (V .r31) (V .r28) := by rw [a, b', d, e]; exact X
    exact WP.mono (oneCrypt_ok (L.v a b' d) X' he (by rw [a, b', d, j, k]; exact hD.dw) (by rw [e]; exact hD.xw)
      (by rw [j, k, e]; exact hD.dx) rfl)
      fun s' oc => ⟨by rw [oc.env.r31, d], oc.env.sp⟩
  · obtain ⟨_, hc⟩ := nil_taint [mov .r3 .r19] (.inr (.inr (.inr rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨_, hsp⟩ => ⟨hsp, by simp⟩) hc

end

/-- `mov r25 r18` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so1 {W X : Addr} {t₀ s₂ s₃ : State} (h2 : SO1 W X t₀ s₂)
    (g : ∀ r, r ≠ .r0 → r ≠ .r25 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) :
    SO1 W X t₀ (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)) ∧
      (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr .r19 = s₂.gpr .r19 := by
  have e19 : (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr .r19 = s₃.gpr .r19 := by simp [State.write]
  refine ⟨h2.keep (fun r h0 _ _ => ?_) ⟨k.mem, k.rd, k.wr, k.sp, k.lr⟩, by rw [e19, g _ (by decide) (by decide)]⟩
  by_cases e : r = .r25
  · subst e
    have : (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr .r25 = s₃.gpr .r18 := by simp [State.write]
    rw [this, g _ (by decide) (by decide), h2.r18, h2.r25]
  · have : (s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)).gpr r = s₃.gpr r := by simp [State.write, e]
    rw [this, g r h0 e]

/-- After the entry (and `r25` restored), what the pieces need. -/
theorem open_one {t₀ s : State} (h : openPre t₀) (h1 : SO1 (stackArg t₀ 1) (stackArg t₀ 2) t₀ s)
    (h19 : s.gpr .r19 = stackArg t₀ 0) :
    OneO (t₀.gpr .r3) (stackArg t₀ 1) (stackArg t₀ 2) t₀.sp (t₀.gpr .r4) (t₀.gpr .r5).toNat (t₀.gpr .r6)
        (t₀.gpr .r7) (t₀.gpr .r8) (t₀.gpr .r9) (t₀.gpr .r10) (stackArg t₀ 0) s ∧
      s.gpr .r24 = t₀.gpr .r4 ∧ s.gpr .r25 = BitVec.ofNat 64 (t₀.gpr .r5).toNat := by
  obtain ⟨hrd, hwr, dcd, -, -, dnW, -, daW, -, ddW, -, -, -, -, fn, fa, fd, -, -, -, -, -, -, ddx, -, -, -, -⟩ := h
  have hC : Covers [⟨t₀.gpr .r3, 256⟩] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW' : Covers [⟨stackArg t₀ 1, scrBytes⟩] t₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hW : Covers [⟨stackArg t₀ 1, 2560⟩] t₀.wr := covers_prefix hW' (by decide)
  have hk₁ := h1.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨t₀.gpr .r8, (t₀.gpr .r9).toNat⟩] s.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hX₁ : Covers [xR (stackArg t₀ 2)] s.wr := by rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨⟨s.gpr, h1.r29, h1.r30, h1.r31, h1.r28, by rw [h1.r18]; exact toN, h1.r21,
    h1.r22, h1.r27, h1.r23, one_env h1 hC hW, ?_, ?_, ⟨⟨⟨covers_left hDw, (t₀.gpr .r9).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩, hX₁, ddx⟩⟩, h1.r20, h19, ?_⟩, h1.r24,
    by rw [h1.r25]; exact toN⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .r5).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .r7).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  · rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))

theorem open_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa openPPC64LE.pre openPPC64LE.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, dcx, _, _, _, _, dwx, _, fx⟩ := h₁'
  let I₀ : State → Prop := fun s => openPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.gpr .r10 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, qres.symm⟩, ?_⟩
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 1) (stackArg t₀ 2) t₀ s ∧
    s.gpr .r19 = stackArg t₀ 0
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .r12 then stackArg σ₁ 1 else σ₁.gpr r
    have hl : openEntry = [.addSp .r12 0, .load .d .r12 .r12 104] ++ (save .r12 ++
        (([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5,
          mov .r21 .r6, mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0,
          .load .d .r28 .r12 (104 + 8)] : List Instr) ++ ([.addSp .r12 0, .load .d .r19 .r12 96] : List Instr))) := by
      rw [openEntry, oneEntry, List.append_assoc, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, ea1, _, _⟩
      have hA : Covers [args s 3] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      refine WP.mono (oneA_ok (W := stackArg s 1) (.inr rfl) (args_in hA (by decide) (i := 1) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 0).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 1) (stackArg t₀ 2) t₀ s₂ ∧
    s₂.gpr .r19 = stackArg t₀ 0 ∧ (∀ r, r ≠ .r0 → r ≠ .r25 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .r25 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 0) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.en.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .r19 = BitVec.ofNat 64 (stackArg t₀ 0).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 0).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .d .r25) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := oneLay fc fW dcW
  have X₀ := oneX fx dcx dwx
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  refine CT.seq (J := fun s => s.gpr .r31 = stackArg σ₁ 1 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .r3 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.en.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .r4) (n := (σ₁.gpr .r5).toNat) (Ad := σ₁.gpr .r6) (A := σ₁.gpr .r7)
        (D := σ₁.gpr .r8) (Ln := σ₁.gpr .r9) L₀ X₀ (dtW.sub_right (Lay.wSub (by decide))) t1 t16
        (openRes σ₁).isSome)
    · obtain ⟨_, hc⟩ := nil_taint [mov .r25 .r18] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.en.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩ := ht
      refine WP.of_runBlock ⟨_, rfl, ?_⟩
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 0).toNat = true := by rw [ea0]; exact hok
      have o := open_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, ea2, esp] at o
      refine ⟨o, open_head hpre h4 (h19₄.trans h19) hok₀ (T := .block []) fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .r19 = _
      rw [om.r19, ← eres, openRes_isSome hok₀]
      by_cases hx : openTagOk t₀
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩ := hs
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩)
      (fun ht => ?_) (fun hf => ?_)
    · have h₀ : WP isa (.block [.li .r3 0]) s fun s' => (∀ r, r ≠ .r3 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨g', k'⟩ => ⟨by rw [g' _ (by decide), g _ (by decide) (by decide), h1.r31, ea1],
        by rw [k'.sp, k.sp, h1.en.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 0).toNat = true := by rw [ea0]; exact hok
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k
      exact WP.mono (open_good hpre h4 (h19₄.trans h19) hok₀) fun s' oo =>
        ⟨by rw [oo.r31, ea1], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
