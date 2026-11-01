module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce11Step
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract
import VerifiedGarbage.Proof.MlKem.Compress1024
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce5Step
import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce11Step
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem1024.Contract
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce5Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_compress_encode`

The contract, the dispatch on `len` to the loop of each width (`loop5_ok`, `loop11_ok`, from
`Proof/MlKem1024/AArch64/CodecV/` and the loops of ML-KEM-768's vector codecs), and constant time:
every address and branch depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem1024_compress_encode(f = x0, d = w1, out =
x2, len = x3)`: if `d` is 5 or 11, `len = 32 d` and the polynomial at `f` is
reduced, writes `ByteEncode_d(Compress_d(f))` to the `len` bytes at `out`. The
code may read `f` and write `out`, which do not overlap. -/
def compressEncodeAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    ((s.gpr .x1).setWidth 32).toNat ∈ Proof.MlKem1024.compressWidths ∧
    (s.gpr .x3).toNat = 32 * ((s.gpr .x1).setWidth 32).toNat ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    compressEncode ((s.gpr .x1).setWidth 32).toNat (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.CE VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem
open VG.Proof.MlKem
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

theorem loop5_ok {s₀ : State} (hp : Pre width5 s₀) :
    WP isa (ceLoop width5 8 (bytesVec .v20 ce10Idx ++ bytesVec .v21 ce10IdxHi) ce5Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        bytesAt s'.mem (oP s₀) (32 * width5.d) = Spec.MlKem.compressEncode width5.d (P s₀) :=
  vloop_ok width5_ok (G := 4) (K := K10) rfl (by decide) rfl (by decide) (by decide)
    (fun s => by
      rw [← List.append_nil (bytesVec .v21 _)]
      exact wp_bytesVec fun s1 g1 v1 e1 => wp_bytesVec fun s2 g2 v2 e2 => wp_nil ⟨g1.trans g2,
        fun r a b _ => by rw [v2 r b, v1 r a], by rw [v2 .v20 (by decide), e1, idx10_eq], by rw [e2, idx10Hi_eq]⟩)
    (fun _ _ hv hk => by rw [K10, hv]; exact hk)
    fun _ hk _ h => step5 hp hk h

theorem idx11a_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce11Idx0.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce11Idx0.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce11Idx0.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce11Idx0 := by decide +kernel

theorem idx11b_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce11Idx1.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce11Idx1.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce11Idx1.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce11Idx1 := by decide +kernel

theorem idx11c_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce11Idx2.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce11Idx2.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce11Idx2.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce11Idx2 := by decide +kernel

theorem loop11_ok {s₀ : State} (hp : Pre width11 s₀) :
    WP isa (ceLoop width11 8 (bytesVec .v20 ce11Idx0 ++ bytesVec .v21 ce11Idx1 ++ bytesVec .v22 ce11Idx2)
      ce11Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        bytesAt s'.mem (oP s₀) (32 * width11.d) = Spec.MlKem.compressEncode width11.d (P s₀) :=
  vloop_ok width11_ok (G := 4) (K := K11) rfl (by decide) rfl (by decide) (by decide)
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (bytesVec .v22 _)]
      exact wp_bytesVec fun s1 g1 v1 e1 => wp_bytesVec fun s2 g2 v2 e2 => wp_bytesVec fun s3 g3 v3 e3 =>
        wp_nil ⟨(g1.trans g2).trans g3, fun r a b c => by rw [v3 r c, v2 r b, v1 r a],
          by rw [v3 .v20 (by decide), v2 .v20 (by decide), e1, idx11a_eq],
          by rw [v3 .v21 (by decide), e2, idx11b_eq], by rw [e3, idx11c_eq]⟩)
    (fun _ _ hv hk => by rw [K11, hv]; exact hk)
    fun _ hk _ h => step11 hp hk h

theorem correct (s : State) (hs : compressEncodeAArch64.pre s) :
    ∃ t s', Exec isa Impl.MlKem1024.AArch64.compressEncode s t s' ∧ abiPreserved s s' ∧ compressEncodeAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen, -⟩ := hs'
  have hd' := mem_compressWidths1024 hd
  suffices h : WP isa Impl.MlKem1024.AArch64.compressEncode s fun s' => s'.sp = s.sp ∧ compressEncodeAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x3).toNat = 160)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases hd' with h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 5 := by simp at hb; omega
    exact width_ok (w := width5) hs e k₂ m₂ fun _ hp => loop5_ok hp
  · have e : ((s.gpr .x1).setWidth 32).toNat = 11 := by
      simp at hb
      rcases hd' with h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width11) hs e k₂ m₂ fun _ hp => loop11_ok hp

theorem ct : ConstantTime isa compressEncodeAArch64.pre compressEncodeAArch64.pub Impl.MlKem1024.AArch64.compressEncode :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 5 | .x2 => 0x2000 | .x3 => 160 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 160⟩]

theorem compressEncode_verified :
    Verified AArch64.target Impl.MlKem1024.AArch64.compressEncode (Proof.MlKem1024.compressEncodeContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Proof.MlKem1024.compressEncodeContract, Proof.MlKem1024.compressEncodeSig,
      compressEncodeAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem1024.AArch64.CE
