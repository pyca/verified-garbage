module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.KemB
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
meta import VerifiedGarbage.Proof.MlKem.AArch64.KemB
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM on AArch64: `encaps`, its contract and its layout

The contract of `encaps` on AArch64 (`encapsAArch64`), where its arguments
and the buffers of `scratch` are (`enL`, `offs`, `pre_of`), what it
encapsulates (`ekE`, `mE`, `gE`, `rhoE`), the arguments of K-PKE.Encrypt
(`encArgs`, `ekT_eq`), and a state satisfying the precondition (`sat`), for
the functions of `Kem16/` and `Kem16P/`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64 (KemLay)

/-- AArch64 contract for `encaps(ek = x0, m = x1, key = x2, ct = x3,
scratch = x4) -> w0` of the parameter set `P`. -/
def encapsAArch64 (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let ek : Region := ⟨s.gpr .x0, P.ekLen⟩
    let msg : Region := ⟨s.gpr .x1, 32⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let ct : Region := ⟨s.gpr .x3, P.ctLen⟩
    let scratch : Region := ⟨s.gpr .x4, P.scl⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    ek ∈ s.rd ∧ msg ∈ s.rd ∧ s.wr = [key, ct, scratch] ∧ ek.Disjoint key ∧ ek.Disjoint ct ∧
    ek.Disjoint scratch ∧ msg.Disjoint key ∧ msg.Disjoint ct ∧ msg.Disjoint scratch ∧ key.Disjoint ct ∧
    key.Disjoint scratch ∧ ct.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint ek ∧ stack.Disjoint msg ∧
    stack.Disjoint key ∧ stack.Disjoint ct ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => encapsInternal P.params iters (bytesAt s.mem (s.gpr .x0) P.ekLen)
        (bytesAt s.mem (s.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
      (bytesAt s'.mem (s.gpr .x2) 32, bytesAt s'.mem (s.gpr .x3) P.ctLen)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
      leakRho (ekRho P.params (bytesAt s₁.mem (s₁.gpr .x0) P.ekLen)) =
        leakRho (ekRho P.params (bytesAt s₂.mem (s₂.gpr .x0) P.ekLen))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- 0 `ek`, 1 `m` (read); 2 `key`, 3 `ct`, 4 `scratch` (written); `ek`, `key`,
`ct` and `scratch` kept in `x25`–`x28`. -/
def enL (P : KemLay) : Layout where
  nb := 5
  nrd := 2
  len b := [P.ekLen, 32, 32, P.ctLen, P.scl].getD b 0
  slot k := [0, 2, 3, 4].getD k 4

/-- The offsets of the buffers of the first phase in `scratch`, proved once. -/
theorem offs (hP : P.Wf) : MB + 32 ≤ SV P ∧ RB + 32 ≤ SV P ∧ HB + 32 ≤ SV P ∧ SB + 32 ≤ SV P ∧
    WK + 640 ≤ SV P ∧ KEM.ST + 200 ≤ SV P ∧ SV P + 48 ≤ P.scl ∧ 384 * P.k + 32 ≤ P.ekLen ∧
    P.ekLen < 65536 := by
  have := hP; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lom

/-- Arithmetic on the offsets and the buffers of `enL`: decided, or from `offs`,
or by `kom`. -/
tactic_template "enk" : tactic => `(tactic| (
  simp -failIfUnchanged only [enL, List.getD_cons_zero, List.getD_cons_succ, Layout.sc]
  first | decide | omega_using [offs (‹Pre _ _ _›).wf] | kom))

theorem pre_of (hP : P.Wf) {s₀ : State} (h : (encapsAArch64 P).pre s₀) : Pre P (enL P) s₀ := by
  obtain ⟨rd0, rd1, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, sp16, k0, k1, k2, k3, k4⟩ := h
  refine ⟨by
    intro b hb
    have hb' : b = 0 ∨ b = 1 := by change b < 2 at hb; omega_using [hb]
    rcases hb' with rfl | rfl
    · exact rd0
    · exact rd1, by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    by enk, by enk, rfl, hP⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [enL] at hb hc hw
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega_using [hc] : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [enL] at hb
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [enL, List.getD_cons_zero, List.getD_cons_succ] <;> lom
  · simp only [enL] at hb
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- `ek`. -/
abbrev ekE (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0) P.ekLen
/-- `m`. -/
abbrev mE (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 1) 32
/-- `(K, r) = G(m ‖ H(ek))`. -/
abbrev gE (P : KemLay) (s₀ : State) : List Byte × List Byte := G (mE s₀ ++ H (ekE P s₀))
/-- `ρ`. -/
abbrev rhoE (P : KemLay) (s₀ : State) : List Byte := ekRho P.params (ekE P s₀)

/-! ## `ŷ`, `u`, `v` and the epilogue -/

theorem encArgs : EncArgs P (enL P) 0 0 2 0 :=
  ⟨by decide, by enk, by simp [enL], by decide, by enk, by simp [enL], .inl (by enk)⟩

theorem ekT_eq (s₀ : State) : ∀ j < P.k,
    decode12 (bytesAt s₀.mem (kA s₀ ((enL P).slot 0) + BitVec.ofNat 64 (0 + 384 * j)) 384) = ekT (ekE P s₀) j :=
  fun j hj => by
    rw [ekT, bytesAt_slice _ _ (show 384 * j + 384 ≤ P.ekLen by
      have := mul_succ_le (a := 384) hj; simp only [KemLay.ekLen]; omega_using [hj]),
      Nat.zero_add]
    rfl

/-- The key is apart from what the rest writes. -/
theorem key_far {s₀ : State} (hp : Pre P (enL P) s₀) {r : Region}
    (h : r ∈ bW P (enL P) s₀ ∨ r ∈ encW P (enL P) s₀ 2 0) : Region.Disjoint ⟨kA s₀ 2, 32⟩ r := by
  have hw := hp.wf
  have hs : ∀ {b o l : Nat}, b < 5 → b ≠ 2 → 2 ≤ b → o + l ≤ (enL P).len b →
      Region.Disjoint ⟨kA s₀ 2, 32⟩ (R (kA s₀) b o l) := fun hb hb2 hw f =>
    (hp.args.disj 2 (by enk) _ hb (Ne.symm hb2) (.inl (by enk))).sub_right (R.sub f)
  have hb : Region.Disjoint ⟨kA s₀ 2, 32⟩ (below s₀.sp 16) := by
    rw [below16]; exact (hp.args.stk 2 (by enk)).symm
  rcases h with h | h
  · rcases mem4 h with rfl | rfl | rfl | rfl
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hb
  · rcases mem5 h with rfl | rfl | rfl | rfl | rfl
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hb
    · exact hs (b := 3) (by decide) (by decide) (by decide) (by simp [enL])

/-! ## ML-KEM-768 -/

theorem calls768 : Calls lay768 :=
  ⟨fun h0 h1 h2 h3 hd => compressEncode_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => decodeDecompress_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

end VG.Proof.MlKem.AArch64.Encaps
