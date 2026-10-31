module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTCrypt
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTJ0
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.OneShot
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
meta import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

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
