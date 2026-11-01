module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd1
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd4Step
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd1
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd4Step
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: `vg_mlkem_decode_decompress`

The contract, the dispatch on `len` to the loop of each width (`loop1_ok`, `loop4_ok`,
`loop10_ok`, from `Proof/MlKem/AArch64/CodecV/`), and constant time: every address and branch
depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_decode_decompress(b = x0, len = x1, d = w2,
f = x3)`: if `d` is 1, 4 or 10 and `len = 32 d`, writes
`Decompress_d(ByteDecode_d(B))` of the `len` bytes `B` at `b` to `f`, reduced.
The code may read `b` and write `f`, which do not overlap. -/
def decodeDecompressAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, 1024⟩ ∧
    ((s.gpr .x2).setWidth 32).toNat ∈ compressWidths ∧
    (s.gpr .x1).toNat = 32 * ((s.gpr .x2).setWidth 32).toNat
  post s s' := PolyIs s'.mem (s.gpr .x3)
    (decodeDecompress ((s.gpr .x2).setWidth 32).toNat (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Proof.MlKem.AArch64.CE (GFr wp_dupW wp_bytesVec wp_movImm9)
open VG.Spec.MlKem
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

theorem dd1idx18 : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0)))
    64 1 (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] : List Nat).getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      ofVWords 1#32 2#32 4#32 8#32 := by decide +kernel

theorem dd1idx19 : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] : List Nat).getD (0 + i) 255) * 2 ^ (8 * i)) 0)))
    64 1 (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (([16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] : List Nat).getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      ofVWords 16#32 32#32 64#32 128#32 := by decide +kernel

theorem dd10idx : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (dd10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10Idx.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec dd10Idx := by decide +kernel

theorem dd10idxHi : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (dd10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (dd10IdxHi.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec dd10IdxHi := by decide +kernel

theorem vword_ofVWords4 (a b c d : BitVec 32) : ∀ e < 4, vword (ofVWords a b c d) e = [a, b, c, d][e]! := by
  intro e he
  rw [vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem loop1_ok {s₀ : State} (hp : Pre width1 s₀) :
    WP isa (ddLoop 1 2 (bytesVec .v18 [1, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0] ++
      bytesVec .v19 [16, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 128, 0, 0, 0] ++ dupW .v20 1665 ++
      ([.vop (.movi0 .v21)] : List Instr)) dd1Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width1.d (B width1 s₀)) :=
  dloop_ok width1_ok (Ng := 16) (K := K1) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      exact wp_bytesVec fun s1 g1 v1 e1 => wp_bytesVec fun s2 g2 v2 e2 => wp_dupW (by decide) fun s3 g3 v3 e3 =>
        wp_vop rfl fun s4 h4 => wp_nil ⟨(g1.trans g2).trans (g3.trans (.of_upd h4)),
          fun r a b c d _ _ => by rw [h4.get r d, v3 r c, v2 r b, v1 r a],
          ⟨by rw [h4.get .v18 (by decide), v3 .v18 (by decide), v2 .v18 (by decide), e1, dd1idx18]
              exact fun e he => by rw [vword_ofVWords4 _ _ _ _ e he]
                                   rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl,
           by rw [h4.get .v19 (by decide), v3 .v19 (by decide), e2, dd1idx19]
              exact fun e he => by rw [vword_ofVWords4 _ _ _ _ e he]
                                   rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl,
           fun e he => by
             rw [h4.get .v20 (by decide)]
             apply BitVec.eq_of_toNat_eq; rw [e3 e he]; rfl,
           by rw [h4.v]⟩⟩)
    (fun _ _ hv hk => by rw [K1, hv]; exact hk)
    fun _ hk _ h => step1 hp hk h

theorem loop4_ok {s₀ : State} (hp : Pre width4 s₀) :
    WP isa (ddLoop 4 8 (movImm .x9 15 ++ ([.vop (.dup .b16 .v18 .x9), .vop (.movi0 .v19)] : List Instr)) dd4Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width4.d (B width4 s₀)) :=
  dloop_ok width4_ok (Ng := 16) (K := K4) rfl (by decide) rfl
    (fun s => wp_movImm9 fun s1 g1 v1 e1 => wp_vop rfl fun s2 h2 => wp_vop rfl fun s3 h3 => wp_nil
      ⟨g1.trans ((GFr.of_upd h2).trans (.of_upd h3)), fun r a b _ _ _ _ => by rw [h3.get r b, h2.get r a, v1],
        fun j hj => by
          rw [h3.get .v18 (by decide), h2.v, vbyte_ofVBytes _ hj, e1]; rfl,
        by rw [h3.v]⟩)
    (fun _ _ hv hk => by rw [K4, hv]; exact hk)
    fun _ hk _ h => step4 hp hk h

theorem loop10_ok {s₀ : State} (hp : Pre width10 s₀) :
    WP isa (ddLoop 10 16 (dupW .v18 (2 ^ 20 - 1) ++ dupW .v19 1023 ++ bytesVec .v20 dd10Idx ++
      bytesVec .v21 dd10IdxHi) dd10Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        PolyIs s'.mem (fP s₀) (decodeDecompress width10.d (B width10 s₀)) :=
  dloop_ok width10_ok (Ng := 4) (K := K10) rfl (by decide) rfl
    (fun s => by
      simp only [List.append_assoc]
      rw [← List.append_nil (bytesVec .v21 _)]
      exact wp_dupW (by decide) fun s1 g1 v1 l1 => wp_dupW (by decide) fun s2 g2 v2 l2 =>
        wp_bytesVec fun s3 g3 v3 e3 => wp_bytesVec fun s4 g4 v4 e4 => wp_nil
          ⟨((g1.trans g2).trans g3).trans g4, fun r a b c d _ _ => by rw [v4 r d, v3 r c, v2 r b, v1 r a],
            by rw [v4 .v18 (by decide), v3 .v18 (by decide), v2 .v18 (by decide)]; exact l1,
            by rw [v4 .v19 (by decide), v3 .v19 (by decide)]; exact l2,
            by rw [v4 .v20 (by decide), e3, dd10idx], by rw [e4, dd10idxHi]⟩)
    (fun _ _ hv hk => by rw [K10, hv]; exact hk)
    fun _ hk _ h => step10 hp hk h

theorem correct (s : State) (hs : decodeDecompressAArch64.pre s) :
    ∃ t s', Exec isa decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen⟩ := hs'
  suffices h : WP isa decodeDecompress s fun s' => s'.sp = s.sp ∧ decodeDecompressAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x1).toNat = 32)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 1 := by simp at hb; omega
    exact width_ok (w := width1) hs e k₂ m₂ fun _ hp => loop1_ok hp
  refine WP.seq (wp_subImm (by decide) fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ : Keep [.x9] s s₃ := (k₂.trans h₃.keep).mono
  have z₃ : isa.eval (.zero .x .x9) s₃ = some (decide ((s.gpr .x1).toNat = 128)) := by
    rw [eval_zero, eq_zero_iff, e₃, k₂.get .x1, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₃ (fun hb' => ?_) (fun hb' => ?_)
  · have e : ((s.gpr .x2).setWidth 32).toNat = 4 := by simp at hb'; omega
    exact width_ok (w := width4) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop4_ok hp
  · have e : ((s.gpr .x2).setWidth 32).toNat = 10 := by
      simp at hb hb'
      rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width10) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop10_ok hp

theorem ct : ConstantTime isa decodeDecompressAArch64.pre decodeDecompressAArch64.pub
    decodeDecompress :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x3])
    (fun _ _ _ _ ⟨h0, h1, h3, hsp⟩ => agree_of hsp (by simp [h0, h1, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 4 | .x3 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress_verified :
    Verified AArch64.target decodeDecompress (Proof.MlKem.decodeDecompressContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Proof.MlKem.decodeDecompressContract, Proof.MlKem.decodeDecompressSig,
      decodeDecompressAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.DD
