module

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: `vg_mlkem_compress_encode`

The contract, the dispatch on `len` to the loop of each width (`loop1_ok`, `loop4_ok`,
`loop10_ok`, from `Proof/MlKem/AArch64/CodecV/`), and constant time: every address and branch
depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_compress_encode(f = x0, d = w1, out = x2,
len = x3)`: if `d` is 1, 4 or 10, `len = 32 d` and the polynomial at `f` is
reduced, writes `ByteEncode_d(Compress_d(f))` to the `len` bytes at `out`. The
code may read `f` and write `out`, which do not overlap. -/
def compressEncodeAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    ((s.gpr .x1).setWidth 32).toNat ∈ compressWidths ∧
    (s.gpr .x3).toNat = 32 * ((s.gpr .x1).setWidth 32).toNat ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    compressEncode ((s.gpr .x1).setWidth 32).toNat (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} {c : Prog isa} {s₀ s : State} (hs : compressEncodeAArch64.pre s₀)
    (hd : ((s₀.gpr .x1).setWidth 32).toNat = w.d) (hk : Keep [.x9] s₀ s) (hm : s.mem = s₀.mem)
    (hl : ∀ s, Pre w s → WP isa c s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      bytesAt s'.mem (oP s) (32 * w.d) = Spec.MlKem.compressEncode w.d (P s)) :
    WP isa c s fun s' => s'.sp = s₀.sp ∧ compressEncodeAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, h5, h6'⟩ := hs
  rw [hd] at h5
  have e0 : fP s = s₀.gpr .x0 := hk.get .x0
  have e2 : oP s = s₀.gpr .x2 := hk.get .x2
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, e0], by rw [hk.wr, h2, oR, e2, h5], by rw [e0, oR, e2, ← h5]; exact h3,
      by rw [hm, e0]; exact h6'⟩
  refine WP.mono (hl s hp) fun s' ⟨_, _, sp, e⟩ => ⟨by rw [sp, hk.sp], ?_⟩
  show bytesAt s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = _
  rw [h5, hd, ← hk.get .x2, e, P, fP, hm, hk.get .x0]

theorem loop1_ok {s₀ : State} (hp : Pre width1 s₀) :
    WP isa (ceLoop width1 8 [] ce1Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (oP s₀) (32 * width1.d) = Spec.MlKem.compressEncode width1.d (P s₀) :=
  vloop_ok width1_ok (G := 4) (K := fun _ => True) rfl (by decide) rfl (by decide) (by decide)
    (fun s => wp_nil ⟨GFr.refl s, fun _ _ _ _ => rfl, trivial⟩) (fun _ _ _ _ => trivial)
    fun _ hk _ h => step1 hp hk h

theorem loop4_ok {s₀ : State} (hp : Pre width4 s₀) :
    WP isa (ceLoop width4 8 [] ce4Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (oP s₀) (32 * width4.d) = Spec.MlKem.compressEncode width4.d (P s₀) :=
  vloop_ok width4_ok (G := 16) (K := fun _ => True) rfl (by decide) rfl (by decide) (by decide)
    (fun s => wp_nil ⟨GFr.refl s, fun _ _ _ _ => rfl, trivial⟩) (fun _ _ _ _ => trivial)
    fun _ hk _ h => step4 hp hk h

theorem idx10_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10Idx.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce10Idx := by decide +kernel

theorem idx10Hi_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10IdxHi.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce10IdxHi := by decide +kernel

theorem loop10_ok {s₀ : State} (hp : Pre width10 s₀) :
    WP isa (ceLoop width10 16 (bytesVec .v20 ce10Idx ++ bytesVec .v21 ce10IdxHi) ce10Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        bytesAt s'.mem (oP s₀) (32 * width10.d) = Spec.MlKem.compressEncode width10.d (P s₀) :=
  vloop_ok width10_ok (G := 4) (K := K10) rfl (by decide) rfl (by decide) (by decide)
    (fun s => by
      rw [← List.append_nil (bytesVec .v21 _)]
      exact wp_bytesVec fun s1 g1 v1 e1 => wp_bytesVec fun s2 g2 v2 e2 => wp_nil ⟨g1.trans g2,
        fun r a b _ => by rw [v2 r b, v1 r a], by rw [v2 .v20 (by decide), e1, idx10_eq], by rw [e2, idx10Hi_eq]⟩)
    (fun _ _ hv hk => by rw [K10, hv]; exact hk)
    fun _ hk _ h => step10 hp hk h

theorem correct (s : State) (hs : compressEncodeAArch64.pre s) :
    ∃ t s', Exec isa compressEncode s t s' ∧ abiPreserved s s' ∧ compressEncodeAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen, -⟩ := hs'
  suffices h : WP isa compressEncode s fun s' => s'.sp = s.sp ∧ compressEncodeAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x3).toNat = 32)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 1 := by simp at hb; omega
    exact width_ok (w := width1) hs e k₂ m₂ fun _ hp => loop1_ok hp
  refine WP.seq (wp_subImm (by decide) fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ : Keep [.x9] s s₃ := (k₂.trans h₃.keep).mono
  have z₃ : isa.eval (.zero .x .x9) s₃ = some (decide ((s.gpr .x3).toNat = 128)) := by
    rw [eval_zero, eq_zero_iff, e₃, k₂.get .x3, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₃ (fun hb' => ?_) (fun hb' => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 4 := by simp at hb'; omega
    exact width_ok (w := width4) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop4_ok hp
  · have e : ((s.gpr .x1).setWidth 32).toNat = 10 := by
      simp at hb hb'
      rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width10) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop10_ok hp

theorem ct : ConstantTime isa compressEncodeAArch64.pre compressEncodeAArch64.pub compressEncode :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 4 | .x2 => 0x2000 | .x3 => 128 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem compressEncode_verified :
    Verified AArch64.target compressEncode (Proof.MlKem.compressEncodeContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Proof.MlKem.compressEncodeContract, Proof.MlKem.compressEncodeSig,
      compressEncodeAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.CE
