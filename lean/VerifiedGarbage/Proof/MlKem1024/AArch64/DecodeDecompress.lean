module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dd5Step
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dd11Step
import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract
import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dd5Step
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dd11Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem1024.Contract
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSpec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSpec

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decode_decompress`

The contract, the dispatch on `len` to the loop of each width (`loop5_ok`, `loop11_ok`, from
`Proof/MlKem1024/AArch64/CodecV/` and the loops of ML-KEM-768's vector codecs), and constant time:
every address and branch depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem1024_decode_decompress(b = x0, len = x1, d =
w2, f = x3)`: if `d` is 5 or 11 and `len = 32 d`, writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`, reduced.
The code may read `b` and write `f`, which do not overlap. -/
def decodeDecompressAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 1024⟩ ∧
    ((s.gpr .x2).setWidth 32).toNat ∈ Proof.MlKem1024.compressWidths ∧
    (s.gpr .x1).toNat = 32 * ((s.gpr .x2).setWidth 32).toNat
  post s s' := PolyIs s'.mem (s.gpr .x3)
    (decodeDecompress ((s.gpr .x2).setWidth 32).toNat (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.DD VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Proof.MlKem.AArch64.CE (GFr wp_dupW wp_bytesVec)
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} {c : Prog isa} {s₀ s : State} (hs : decodeDecompressAArch64.pre s₀)
    (hd : ((s₀.gpr .x2).setWidth 32).toNat = w.d) (hk : Keep [.x9] s₀ s) (hm : s.mem = s₀.mem)
    (hl : ∀ s, Pre w s → WP isa c s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (fP s) (decodeDecompress w.d (B w s))) :
    WP isa c s fun s' => s'.sp = s₀.sp ∧ decodeDecompressAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, hlen⟩ := hs
  rw [hd] at hlen
  have e0 : bP s = s₀.gpr .x0 := hk.get .x0
  have e3 : fP s = s₀.gpr .x3 := hk.get .x3
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, bR, e0, hlen], by rw [hk.wr, h2, e3], by rw [e3, bR, e0, ← hlen]; exact h3⟩
  refine WP.mono (hl s hp) fun s' ⟨_, _, sp, e⟩ => ⟨by rw [sp, hk.sp], ?_⟩
  show PolyIs s'.mem (s₀.gpr .x3) (decodeDecompress ((s₀.gpr .x2).setWidth 32).toNat
    (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
  rw [hlen, hd, ← e3, ← e0, ← hm]
  exact e

theorem loop5_ok {s₀ : State} (hp : Pre width5 s₀) :
    WP isa (ddLoop 5 8 (dupW .v18 (2 ^ 20 - 1) ++ dupW .v19 1023 ++ bytesVec .v20 dd10Idx ++
      bytesVec .v21 dd10IdxHi ++ dupW .v22 31) dd5Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.sp = s₀.sp ∧ PolyIs s'.mem (fP s₀) (decodeDecompress width5.d (B width5 s₀)) :=
  dloop_ok width5_ok (Ng := 4) (K := K5) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (dupW .v22 _)]
      exact wp_dupW (by decide) fun s1 g1 v1 l1 => wp_dupW (by decide) fun s2 g2 v2 l2 =>
        wp_bytesVec fun s3 g3 v3 e3 => wp_bytesVec fun s4 g4 v4 e4 => wp_dupW (by decide) fun s5 g5 v5 l5 =>
          wp_nil ⟨(((g1.trans g2).trans g3).trans g4).trans g5,
            fun r a b c d e _ => by rw [v5 r e, v4 r d, v3 r c, v2 r b, v1 r a],
            by rw [v5 .v18 (by decide), v4 .v18 (by decide), v3 .v18 (by decide), v2 .v18 (by decide)]; exact l1,
            by rw [v5 .v19 (by decide), v4 .v19 (by decide), v3 .v19 (by decide)]; exact l2,
            by rw [v5 .v20 (by decide), v4 .v20 (by decide), e3, dd10idx],
            by rw [v5 .v21 (by decide), e4, dd10idxHi], l5⟩)
    (fun _ _ hv hk => by rw [K5, hv]; exact hk)
    fun _ hk _ h => step5 hp hk h

theorem dd11idx : ∀ g < 4, setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + ((dd11Idx g).getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + ((dd11Idx g).getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + ((dd11Idx g).getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec (dd11Idx g) := by decide +kernel

theorem loop11_ok {s₀ : State} (hp : Pre width11 s₀) :
    WP isa (ddLoop 11 8 (dupW .v18 (2 ^ 22 - 1) ++ dupW .v19 2047 ++ bytesVec .v20 (dd11Idx 0) ++
      bytesVec .v21 (dd11Idx 1) ++ bytesVec .v22 (dd11Idx 2) ++ bytesVec .v23 (dd11Idx 3)) dd11Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width11.d (B width11 s₀)) :=
  dloop_ok width11_ok (Ng := 4) (K := K11) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (bytesVec .v23 _)]
      exact wp_dupW (by decide) fun s1 g1 v1 l1 => wp_dupW (by decide) fun s2 g2 v2 l2 =>
        wp_bytesVec fun s3 g3 v3 e3 => wp_bytesVec fun s4 g4 v4 e4 =>
        wp_bytesVec fun s5 g5 v5 e5 => wp_bytesVec fun s6 g6 v6 e6 =>
          wp_nil ⟨((((g1.trans g2).trans g3).trans g4).trans g5).trans g6,
            fun r a b c d e f => by rw [v6 r f, v5 r e, v4 r d, v3 r c, v2 r b, v1 r a],
            by rw [v6 .v18 (by decide), v5 .v18 (by decide), v4 .v18 (by decide), v3 .v18 (by decide),
              v2 .v18 (by decide)]; exact l1,
            by rw [v6 .v19 (by decide), v5 .v19 (by decide), v4 .v19 (by decide), v3 .v19 (by decide)]; exact l2,
            fun g hg => by
              rcases (show g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 by omega) with rfl | rfl | rfl | rfl
              · show s6.v .v20 = _
                rw [v6 .v20 (by decide), v5 .v20 (by decide), v4 .v20 (by decide), e3, dd11idx 0 (by decide)]
              · show s6.v .v21 = _
                rw [v6 .v21 (by decide), v5 .v21 (by decide), e4, dd11idx 1 (by decide)]
              · show s6.v .v22 = _
                rw [v6 .v22 (by decide), e5, dd11idx 2 (by decide)]
              · show s6.v .v23 = _
                rw [e6, dd11idx 3 (by decide)]⟩)
    (fun _ _ hv hk => by rw [K11, hv]; exact hk)
    fun _ hk _ h => step11 hp hk h

theorem correct (s : State) (hs : decodeDecompressAArch64.pre s) :
    ∃ t s', Exec isa Impl.MlKem1024.AArch64.decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen⟩ := hs'
  have hd' := mem_compressWidths1024 hd
  suffices h : WP isa Impl.MlKem1024.AArch64.decodeDecompress s fun s' =>
      s'.sp = s.sp ∧ decodeDecompressAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x1).toNat = 160)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases hd' with h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 5 := by simp at hb; omega
    exact width_ok (w := width5) hs e k₂ m₂ fun _ hp => loop5_ok hp
  · have e : ((s.gpr .x2).setWidth 32).toNat = 11 := by
      simp at hb
      rcases hd' with h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width11) hs e k₂ m₂ fun _ hp => loop11_ok hp

theorem ct : ConstantTime isa decodeDecompressAArch64.pre decodeDecompressAArch64.pub
    Impl.MlKem1024.AArch64.decodeDecompress :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x3])
    (fun _ _ _ _ ⟨h0, h1, h3, hsp⟩ => agree_of hsp (by simp [h0, h1, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 160 | .x2 => 5 | .x3 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 160⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress_verified :
    Verified AArch64.target Impl.MlKem1024.AArch64.decodeDecompress
      (Proof.MlKem1024.decodeDecompressContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Proof.MlKem1024.decodeDecompressContract, Proof.MlKem1024.decodeDecompressSig,
      decodeDecompressAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem1024.AArch64.DD
