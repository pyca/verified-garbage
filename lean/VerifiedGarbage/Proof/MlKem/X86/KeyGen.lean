import VerifiedGarbage.Proof.MlKem.X86.CheckEk
import VerifiedGarbage.Impl.MlKem.X86.KeyGen
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.NttInv
import VerifiedGarbage.Spec.MlKem.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGenPre`. -/
section

/-!
# ML-KEM on x86 (32-bit): the setting of key generation

The layout of the arguments (`Y L`: `seed`, `ek`, `dk`, `scratch`, and the
88 bytes of stack), which each parameter set's contract implies; the public
data, which includes `ρ`; and `d`, `z` and the values the body computes from
them.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `seed` (64 bytes, read), `ek`, `dk` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay := ⟨[(64, false), (L.p.ekLen, true), (L.p.dkLen, true), (L.scratch, true)], 3, 88⟩

section
variable (s₀ : State)
/-- `d`. -/
abbrev d : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `z`. -/
abbrev z : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 32, 32⟩) 32
end

/-- What keygen may leak: `ρ`. -/
abbrev lk (L : KemLay) (s₀ : State) : List Byte := KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)

theorem addr0 (s₀ : State) (i : Nat) : Buf.addr s₀ ⟨i, 0, 32⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- A taint check of code with `scratch` at `(Y L).sc`, through `esi`. -/
macro "yk_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 3 from fun _ => rfl]); (try simp only
  [ptrTo, reduceIte, Nat.reduceEqDiff, List.cons_append, List.nil_append]); taint_rfl))

end VG.Proof.MlKem.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGenG`. -/
section

/-!
# ML-KEM on x86 (32-bit): the start of key generation

`esi = scratch`, the word `kgACC` set to 1, and `ρ ‖ σ = G(d ‖ k)` at `kgRS`
(`start_piece`), which is `P 0`: the state of the loop over `N` that computes
`ŝ` and `ê`.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt Repr stateAt squeezeFrom absorb pad sha3_512 sha3Suffix shakeSuffix)

/-! ## Buffers -/

abbrev bSE (j : Nat) : Buf := ⟨3, 1024 * j, 1024⟩

section
variable (L : KemLay)
abbrev bT : Buf := ⟨3, L.kgT, 1024⟩
abbrev bA : Buf := ⟨3, L.kgA, 1024⟩
abbrev bP : Buf := ⟨3, L.kgP, 1024⟩
abbrev bNS : Buf := ⟨3, L.kgNS, 1024⟩
abbrev bSS : Buf := ⟨3, L.kgSS, 2048⟩
abbrev bST : Buf := ⟨3, L.kgST, 200⟩
abbrev bWK : Buf := ⟨3, L.kgWK, 640⟩
abbrev bRS : Buf := ⟨3, L.kgRS, 64⟩
abbrev bRho : Buf := ⟨3, L.kgRS, 32⟩
abbrev bSig : Buf := ⟨3, L.kgRS + 32, 32⟩
abbrev bNB : Buf := ⟨3, L.kgRS + 64, 1⟩
abbrev bPRF : Buf := ⟨3, L.kgPRF, 128⟩
abbrev bACC : Buf := ⟨3, L.kgACC, 4⟩

/-- `σ ‖ N`, `PRF`'s input. -/
abbrev bSigN : Buf := ⟨3, L.kgRS + 32, 33⟩
end

section
variable (L : KemLay) (s₀ : State)
/-- `ŝ[j]` (`j < k`) or `ê[j - k]`. -/
abbrev seP (j : Nat) : VG.Spec.MlKem.Poly := ntt (cbd (KPke.kgSigma L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) j)
end

/-- The facts of the layout that the start of key generation uses. -/
class GOK (L : KemLay) : Prop where
  rs : (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSig L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bRS L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bACC L) = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bNB L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [⟨3, L.kgRS + 64, 1⟩] = true
  g : ((VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgST, 200⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨0, 0, 32⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨3, L.kgRS + 64, 1⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgRS, 64⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨0, 0, 32⟩ ⟨3, L.kgST, 200⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨0, 0, 32⟩ ⟨3, L.kgWK, 640⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgST, 200⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgWK, 640⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgRS, 64⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgRS, 64⟩ ⟨3, L.kgWK, 640⟩) = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, ⟨3, L.kgRS, 64⟩] = true
variable {L : KemLay}

/-- While `ŝ` and `ê` are computed: `ŝ[j]` or `ê[j - k]` for `j < N`. -/
structure P (L : KemLay) (N : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s
  acc : s.mem.readW (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bACC L)) 32 = 1
  rho : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)
  sig : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSig L)) 32 = KPke.kgSigma L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)
  se : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSE j)) (VG.Proof.MlKem.X86.KeyGen.seP L s₀ j)

/-- After `kgACC` is set. -/
structure I1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s
  acc : s.mem.readW (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bACC L)) 32 = 1

/-- After the `k` of `G`'s input is stored. -/
structure I2 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.I1 L s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bNB L)) 1 = [BitVec.ofNat 8 L.p.k]

theorem rs_split [VG.Proof.MlKem.X86.KeyGen.GOK L] {s₀ : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) {m : Mem} {o : List Byte}
    (h : bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRS L)) 64 = o) :
    bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L)) 32 = o.take 32 ∧ bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSig L)) 32 = o.drop 32 := by
  have e₁ : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L) = Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRS L) := rfl
  have e₂ : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSig L) = Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRS L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bSig L) GOK.rs.1, Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bRS L) GOK.rs.2.1, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  refine ⟨by rw [e₁, ← bytesAt_take _ _ (show 32 ≤ 64 by decide), h], ?_⟩
  rw [e₂, ← h, bytesAt_drop _ _ (show 32 ≤ 64 by decide)]

/-- The start, then `c`. -/
theorem start_piece [VG.Proof.MlKem.X86.KeyGen.GOK L] {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.P L 0) Q c) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
        .seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.kgACC) .eax]) <|
        .seq (.block (st8 (L.kgRS + 64) L.p.k)) <|
        .seq (hash2 3 L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩) c) := by
  obtain ⟨-, -, o₃, o₄, a₁⟩ := GOK.rs (L := L)
  obtain ⟨g₁, g₂⟩ := GOK.g (L := L)
  refine Piece.seq (ldsc_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) (by yk_taint)) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.I1 L) (st32_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) L.kgACC 1 o₃ (by taint_rfl) (fun _ _ _ h => h)
    fun s₀ s s' hp _ h' m' => ⟨h', by rw [m']; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.I2 L) (st8_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) (L.kgRS + 64) L.p.k o₄ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨⟨h', ?_⟩, ?_⟩) ?_
  · rw [← h.acc, m']; exact keepW hp (N := 0) (by rdecide) a₁ (frW8 (Y := VG.Proof.MlKem.X86.KeyGen.Y L))
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 L.p.k]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega
    simp only [BitVec.add_zero, VG.WriteBytes.writeW8_apply, List.getElem_cons_zero]
    exact (ite_eq_left (rfl : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bNB L) = Buf.addr s₀ ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgRS + 64, 1⟩)).trans
      (by rw [BitVec.setWidth_ofNat_of_le (by decide)])
  refine Piece.seq (hash2_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩
    rate72 g₁ (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint)
    (by yk_taint) (by yk_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr out => ?_) hc
  have hd : bytesAt s.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32 = VG.Proof.MlKem.X86.KeyGen.d s₀ :=
    h.ctx.roBytes hp (b := ⟨0, 0, 32⟩) (by rdecide) rfl
  rw [hd, h.nb, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq] at out
  obtain ⟨r₁, r₂⟩ := VG.Proof.MlKem.X86.KeyGen.rs_split hp out
  refine ⟨h', ?_, r₁, r₂, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [← h.acc]; exact keepW hp (by rdecide) g₂ fr

end VG.Proof.MlKem.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGenPrf`. -/
section

/-!
# ML-KEM on x86 (32-bit): `ŝ` and `ê` in key generation

`kgPrf L N` computes `NTT(SamplePolyCBD₂(PRF₂(σ, N)))` into `scratch[1024N]`
(`prf_piece`), and the `2k` of them take `P 0` to `P (2k)` (`prfs_piece`).
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad shakeSuffix)

variable {L : KemLay}

/-- `P N` holds after a block or call whose frame is apart from what it states. -/
theorem P.keep {N : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (VG.Proof.MlKem.X86.KeyGen.Y L).stk) (h₁ : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) bs = true) (h₂ : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bRho L) bs = true)
    (h₃ : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSig L) bs = true) (h₄ : ∀ j < N, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSE j) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.KeyGen.P L N s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s') : VG.Proof.MlKem.X86.KeyGen.P L N s₀ s' :=
  ⟨c, by rw [keepW hp hM h₁ fr]; exact h.acc, by rw [keepBytes hp hM h₂ fr]; exact h.rho,
    by rw [keepBytes hp hM h₃ fr]; exact h.sig, fun j hj => keepPoly hp hM (h₄ j hj) fr (h.se j hj)⟩

/-- `σ ‖ N` is stored. -/
structure Q1 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.P L N s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bNB L)) 1 = [BitVec.ofNat 8 N]

/-- `PRF₂(σ, N)` is computed. -/
structure Q2 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.P L N s₀ s where
  prf : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bPRF L)) 128 = prf 2 (KPke.kgSigma L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) (BitVec.ofNat 8 N)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` is computed. -/
structure Q3 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.P L N s₀ s where
  cbd : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSE N)) (cbd (KPke.kgSigma L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) N)

/-- The facts of the layout that `ŝ` and `ê` use. -/
class PrfOK (L : KemLay) : Prop where
  sig : (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bNB L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSig L) = true
  nb : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [⟨3, L.kgRS + 64, 1⟩] = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bRho L) [⟨3, L.kgRS + 64, 1⟩] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSig L) [⟨3, L.kgRS + 64, 1⟩] = true
  hash : ((VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgST, 200⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSigN L) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bPRF L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bSigN L) ⟨3, L.kgST, 200⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bSigN L) ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgST, 200⟩ (VG.Proof.MlKem.X86.KeyGen.bPRF L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bPRF L) ⟨3, L.kgWK, 640⟩) = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, VG.Proof.MlKem.X86.KeyGen.bPRF L] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bRho L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, VG.Proof.MlKem.X86.KeyGen.bPRF L] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSig L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, VG.Proof.MlKem.X86.KeyGen.bPRF L] = true
  prf : ∀ N < 2 * L.p.k,
    (∀ j < N, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSE j) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, VG.Proof.MlKem.X86.KeyGen.bPRF L] = true) ∧
    (∀ j < N, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSE j) [⟨3, L.kgRS + 64, 1⟩] = true) ∧
    (∀ j < N, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSE j) [VG.Proof.MlKem.X86.KeyGen.bSE N] = true) ∧
    (∀ j < N, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSE j) [VG.Proof.MlKem.X86.KeyGen.bSE N, VG.Proof.MlKem.X86.KeyGen.bNS L] = true) ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bSE N] && (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bRho L) [VG.Proof.MlKem.X86.KeyGen.bSE N] && (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSig L) [VG.Proof.MlKem.X86.KeyGen.bSE N]) = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bSE N, VG.Proof.MlKem.X86.KeyGen.bNS L] && (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bRho L) [VG.Proof.MlKem.X86.KeyGen.bSE N, VG.Proof.MlKem.X86.KeyGen.bNS L] &&
      (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSig L) [VG.Proof.MlKem.X86.KeyGen.bSE N, VG.Proof.MlKem.X86.KeyGen.bNS L]) = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bPRF L) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bSE N) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bPRF L) (VG.Proof.MlKem.X86.KeyGen.bSE N)) = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bSE N) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bNS L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bSE N) (VG.Proof.MlKem.X86.KeyGen.bNS L)) = true

theorem sigN_split [VG.Proof.MlKem.X86.KeyGen.PrfOK L] {s₀ : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSigN L)) 33 =
      bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSig L)) 32 ++ bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bNB L)) 1 := by
  have e : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bNB L) = Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSig L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bNB L) PrfOK.sig.1, Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bSig L) PrfOK.sig.2, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [e]
  exact bytesAt_add m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSig L)) 32 1

variable [VG.Proof.MlKem.X86.KeyGen.GOK L] [VG.Proof.MlKem.X86.KeyGen.PrfOK L]

/-- `ŝ[N]` or `ê[N - k]`. -/
theorem prf_piece (N : Nat) (hN : N < 2 * L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.P L N) (VG.Proof.MlKem.X86.KeyGen.P L (N + 1)) (kgPrf L N) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := PrfOK.prf N hN
  obtain ⟨b₁, b₂, b₃⟩ := PrfOK.nb (L := L)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := PrfOK.hash (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.Q1 L N) (st8_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) (L.kgRS + 64) N (GOK.rs (L := L)).2.2.2.1 (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (M := 0) (by rdecide) b₁ b₂ b₃ (fun j hj => a₂ j hj) (m' ▸ frW8 (Y := VG.Proof.MlKem.X86.KeyGen.Y L)) h'
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 N]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega
    simp only [BitVec.add_zero, VG.WriteBytes.writeW8_apply, List.getElem_cons_zero]
    refine (ite_eq_left (rfl : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bNB L) = Buf.addr s₀ ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgRS + 64, 1⟩)).trans ?_
    rw [BitVec.setWidth_ofNat_of_le (by decide)]
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.Q2 L N) (hash1_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) L.kgST L.kgWK 136 0x1f (VG.Proof.MlKem.X86.KeyGen.bSigN L) (VG.Proof.MlKem.X86.KeyGen.bPRF L) rate136 c₁
    (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint) (by yk_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (by rdecide) c₂ c₃ c₄ (fun j hj => a₁ j hj) fr h'
  · rw [out, VG.Proof.MlKem.X86.KeyGen.sigN_split hp, h.sig, h.nb, show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32,
      prf_eq]
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.Q3 L N) (cbd2C_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 L.kgPRF 3 (1024 * N) a₇ (by rdecide) (by yk_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨?_, ?_⟩) ?_
  · simp only [Bool.and_eq_true] at a₅
    exact h.keep hp (by rdecide) a₅.1.1 a₅.1.2 a₅.2 a₃ fr h'
  · rw [h.prf] at post; exact post
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 (1024 * N) 3 L.kgNS a₈ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, h.cbd.1⟩) fun s₀ s s' hp h h' fr post => ?_
  simp only [Bool.and_eq_true] at a₆
  have k := h.keep hp (by rdecide) a₆.1.1 a₆.1.2 a₆.2 a₄ fr h'
  refine ⟨h', k.acc, k.rho, k.sig, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.se j hj
  · rw [h.cbd.2] at post; exact post

/-- The `2k` of them, then `c`. -/
theorem prfs_piece {B : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.P L (2 * L.p.k)) B c) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.P L 0) B (seqs ((List.range (2 * L.p.k)).map (kgPrf L)) c) :=
  Piece.seqs0 (P := VG.Proof.MlKem.X86.KeyGen.P L) (2 * L.p.k) VG.Proof.MlKem.X86.KeyGen.prf_piece h

end VG.Proof.MlKem.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGenRow`. -/
section

/-!
# ML-KEM on x86 (32-bit): `t̂` in key generation

Row `i` of `Â` (`kgRow L i`): each entry `Â[i, j]` is sampled from `ρ ‖ j ‖ i`,
masked by the value `vg_mlkem_sample_ntt` returned, which is ANDed into
`kgACC` (`entry0_piece`, `entry_piece`), and multiplied by `ŝ[j]` into
`t̂[i]`; then `ê[i]` is added and `t̂[i]` encoded into `ek` (`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `kgACC` is 0 or 1; if
1, the first `k` samples succeeded, and the first `e` rows of `ek` are those
of `ek_PKE` for the matrix `aM` they sampled; if 0, one of the `k²` samples
failed within `minIterations` iterations.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Row `i` of `ek`. -/
abbrev bEK (i : Nat) : Buf := ⟨1, 384 * i, 384⟩

section
variable (L : KemLay) (s₀ : State)
/-- The seed of the `k`th entry of `Â`, `Â[k / k, k % k]`. -/
abbrev mS (k : Nat) : List Byte := matSeed (KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) (k / L.p.k) (k % L.p.k)
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aM (i j : Nat) : VG.Spec.MlKem.Poly := sv (matSeed (KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) i j)

/-- `Â[i, 0] ×_T ŝ[0] + … + Â[i, j - 1] ×_T ŝ[j - 1]`. -/
noncomputable abbrev part (i j : Nat) : VG.Spec.MlKem.Poly := KPke.dotK (VG.Proof.MlKem.X86.KeyGen.aM L s₀ i) (VG.Proof.MlKem.X86.KeyGen.seP L s₀) j
end

/-- `kgACC`. -/
abbrev accV (L : KemLay) (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bACC L)) 32

/-- See the module documentation. -/
structure B (L : KemLay) (k e : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)
  se : ∀ j < 2 * L.p.k, PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSE j)) (VG.Proof.MlKem.X86.KeyGen.seP L s₀ j)
  acc : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 0 ∨ VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1
  ok : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → ∀ k' < k, ∃ a, Samp (VG.Proof.MlKem.X86.KeyGen.mS L s₀ k') a
  fail : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 0 → ∃ k' < L.p.k * L.p.k, sampleNTT minIterations (VG.Proof.MlKem.X86.KeyGen.mS L s₀ k') = none
  ek : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → ∀ i < e,
    bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bEK i)) 384 = encode12 (KPke.kgT L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀) i)

/-- Whether `bs` is apart from `ρ`, `ŝ` and `ê`. -/
def safeS (L : KemLay) (bs : List Buf) : Bool :=
  (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bRho L) bs && (List.range (2 * L.p.k)).all fun j => (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bSE j) bs

/-- Whether `bs` is also apart from `kgACC` and `ek`. -/
def safe (L : KemLay) (bs : List Buf) : Bool :=
  (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) bs && VG.Proof.MlKem.X86.KeyGen.safeS L bs && (List.range L.p.k).all fun i => (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bEK i) bs

variable {L : KemLay}

/-- What `B` states of `ρ`, `ŝ` and `ê`, kept. -/
theorem keepS {s₀ : State} {m m' : Mem} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (VG.Proof.MlKem.X86.KeyGen.Y L).stk)
    (hs : VG.Proof.MlKem.X86.KeyGen.safeS L bs = true) (fr : Frame (FR s₀ bs M) m m')
    (h₁ : bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀))
    (h₂ : ∀ j < 2 * L.p.k, PolyIs m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSE j)) (VG.Proof.MlKem.X86.KeyGen.seP L s₀ j)) :
    bytesAt m' (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀) ∧
      ∀ j < 2 * L.p.k, PolyIs m' (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSE j)) (VG.Proof.MlKem.X86.KeyGen.seP L s₀ j) := by
  simp only [VG.Proof.MlKem.X86.KeyGen.safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨by rw [keepBytes hp hM hs.1 fr]; exact h₁, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {k e : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (VG.Proof.MlKem.X86.KeyGen.Y L).stk) (hs : VG.Proof.MlKem.X86.KeyGen.safe L bs = true) (he : e ≤ L.p.k)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.KeyGen.B L k e s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s') : VG.Proof.MlKem.X86.KeyGen.B L k e s₀ s' := by
  simp only [VG.Proof.MlKem.X86.KeyGen.safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := VG.Proof.MlKem.X86.KeyGen.keepS hp hM h₂ fr h.rho h.se
  refine ⟨c, k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega)) fr]
  exact h.ek (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `t̂[i]` so far, if `0 < j`. -/
structure R (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * i + j) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bT L)) ∧
    (VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bT L)) = VG.Proof.MlKem.X86.KeyGen.part L s₀ i j)

theorem R.keep {i j : Nat} (hi : i < L.p.k) {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (VG.Proof.MlKem.X86.KeyGen.Y L).stk) (hs : VG.Proof.MlKem.X86.KeyGen.safe L bs = true) (hT : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bT L) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.KeyGen.R L i j s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s') : VG.Proof.MlKem.X86.KeyGen.R L i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega) fr c
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s :=
    keepW hp hM (by simp only [VG.Proof.MlKem.X86.KeyGen.safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hT fr (h.t hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hT fr)]
  exact (h.t hj).2 (ea ▸ e₁)

/-! ## Bytes -/

theorem st8_byte {s₀ : State} (m : Mem) (o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨3, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, VG.WriteBytes.writeW8_apply, List.getElem_cons_zero]
  refine (ite_eq_left (rfl : Buf.addr s₀ ⟨3, o, 1⟩ = Buf.addr s₀ ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, o, 1⟩)).trans ?_
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

section
variable (L : KemLay)
/-- `ρ ‖ j ‖ i`, the seed of `Â[i, j]`. -/
abbrev bSeed : Buf := ⟨3, L.kgRS, 34⟩
abbrev bJ : Buf := ⟨3, L.kgRS + 32, 1⟩
abbrev bI : Buf := ⟨3, L.kgRS + 33, 1⟩
end

/-- The facts of the layout that the rows use. -/
class KgRowOK (L : KemLay) : Prop where
  seed : (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bJ L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bI L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bRho L) = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bJ L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bI L) = true
  nb : VG.Proof.MlKem.X86.KeyGen.safe L [⟨3, L.kgRS + 32, 1⟩] = true ∧ VG.Proof.MlKem.X86.KeyGen.safe L [⟨3, L.kgRS + 33, 1⟩] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bT L) [⟨3, L.kgRS + 32, 1⟩] = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bT L) [⟨3, L.kgRS + 33, 1⟩] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bJ L) [⟨3, L.kgRS + 33, 1⟩] = true
  samp : VG.Proof.MlKem.X86.KeyGen.safe L [VG.Proof.MlKem.X86.KeyGen.bA L, VG.Proof.MlKem.X86.KeyGen.bSS L] = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bT L) [VG.Proof.MlKem.X86.KeyGen.bA L, VG.Proof.MlKem.X86.KeyGen.bSS L] = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨3, L.kgRS, 34⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgA, 1024⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgSS, 2048⟩ &&
      (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgRS, 34⟩ ⟨3, L.kgSS, 2048⟩ &&
      (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) = true
  mask : VG.Proof.MlKem.X86.KeyGen.safeS L [VG.Proof.MlKem.X86.KeyGen.bACC L, VG.Proof.MlKem.X86.KeyGen.bA L] = true ∧ (∀ i < L.p.k, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bEK i) [VG.Proof.MlKem.X86.KeyGen.bACC L, VG.Proof.MlKem.X86.KeyGen.bA L] = true) ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bT L) [VG.Proof.MlKem.X86.KeyGen.bACC L, VG.Proof.MlKem.X86.KeyGen.bA L] = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgACC, 4⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgA, 1024⟩ &&
      (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgACC, 4⟩ ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgA, 1024⟩) = true
  mul : VG.Proof.MlKem.X86.KeyGen.safe L [VG.Proof.MlKem.X86.KeyGen.bT L, VG.Proof.MlKem.X86.KeyGen.bNS L] = true ∧ VG.Proof.MlKem.X86.KeyGen.safe L [VG.Proof.MlKem.X86.KeyGen.bP L, VG.Proof.MlKem.X86.KeyGen.bNS L] = true ∧ VG.Proof.MlKem.X86.KeyGen.safe L [VG.Proof.MlKem.X86.KeyGen.bT L] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bT L) [VG.Proof.MlKem.X86.KeyGen.bP L, VG.Proof.MlKem.X86.KeyGen.bNS L] = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bA L) [VG.Proof.MlKem.X86.KeyGen.bP L, VG.Proof.MlKem.X86.KeyGen.bNS L] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bT L, VG.Proof.MlKem.X86.KeyGen.bNS L] = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bP L, VG.Proof.MlKem.X86.KeyGen.bNS L] = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bT L) && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bP L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bT L) (VG.Proof.MlKem.X86.KeyGen.bP L)) = true
  mul0 : ((VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bT L) && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bA L) && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSE 0) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bNS L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bT L) (VG.Proof.MlKem.X86.KeyGen.bA L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bT L) (VG.Proof.MlKem.X86.KeyGen.bSE 0) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bT L) (VG.Proof.MlKem.X86.KeyGen.bNS L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bA L) (VG.Proof.MlKem.X86.KeyGen.bNS L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bSE 0) (VG.Proof.MlKem.X86.KeyGen.bNS L)) = true
  mulJ : ∀ j < L.p.k, ((VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bP L) && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bA L) && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSE j) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bNS L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bP L) (VG.Proof.MlKem.X86.KeyGen.bA L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bP L) (VG.Proof.MlKem.X86.KeyGen.bSE j) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bP L) (VG.Proof.MlKem.X86.KeyGen.bNS L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bA L) (VG.Proof.MlKem.X86.KeyGen.bNS L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bSE j) (VG.Proof.MlKem.X86.KeyGen.bNS L)) = true
  row : ∀ i < L.p.k, ((VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bT L) && (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSE (L.p.k + i)) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bT L) (VG.Proof.MlKem.X86.KeyGen.bSE (L.p.k + i))) = true ∧
    ((VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bT L) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bEK i) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bT L) (VG.Proof.MlKem.X86.KeyGen.bEK i)) = true ∧ VG.Proof.MlKem.X86.KeyGen.safeS L [VG.Proof.MlKem.X86.KeyGen.bEK i] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bEK i] = true ∧ ∀ i' < i, (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bEK i') [VG.Proof.MlKem.X86.KeyGen.bEK i] = true

theorem seed_split [VG.Proof.MlKem.X86.KeyGen.KgRowOK L] {s₀ : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSeed L)) 34 =
      bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L)) 32 ++ (bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bJ L)) 1 ++ bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bI L)) 1) := by
  obtain ⟨o₁, o₂, o₃, -⟩ := KgRowOK.seed (L := L)
  have e₁ : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bJ L) = Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bJ L) o₁, Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bRho L) o₃, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e₂ : Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bI L) = Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bJ L) + BitVec.ofNat 64 1 := by
    rw [Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bJ L) o₁, Buf.addr_eq hp (b := VG.Proof.MlKem.X86.KeyGen.bI L) o₂, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e₂, e₁, ← bytesAt_add, show Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSeed L) = Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bRho L) from rfl]
  exact bytesAt_add m _ 32 2

/-! ## The value returned by `SampleNTT`, and `kgACC` -/

theorem mS_eq (s₀ : State) {i j : Nat} (hj : j < L.p.k) : VG.Proof.MlKem.X86.KeyGen.mS L s₀ (L.p.k * i + j) = matSeed (KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) i j := by
  simp only [VG.Proof.MlKem.X86.KeyGen.mS]
  rw [idx_div hj, idx_mod hj]

/-! ## An entry -/

/-- After `ρ ‖ j` is stored. -/
structure S1 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.R L i j s₀ s where
  bj : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bJ L)) 1 = [BitVec.ofNat 8 j]

/-- After `ρ ‖ j ‖ i` is stored. -/
structure S2 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.R L i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bSeed L)) 34 = matSeed (KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) i j

/-- After `Â[i, j]` is sampled, `r` returned. -/
structure S3 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.R L i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bA L))
  out : Outcome (fun iters => sampleNTT iters (matSeed (KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) i j)) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bA L)))

/-- After it is masked, and `kgACC` updated. -/
structure S4 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * i + j + 1) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bT L)) ∧
    (VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bT L)) = VG.Proof.MlKem.X86.KeyGen.part L s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bA L))
  a : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bA L)) = VG.Proof.MlKem.X86.KeyGen.aM L s₀ i j

variable [VG.Proof.MlKem.X86.KeyGen.KgRowOK L]

/-- `ρ ‖ j ‖ i`, `Â[i, j]` sampled and masked, then `c`. -/
theorem sample_piece (i j : Nat) (hi : i < L.p.k) (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.S4 L i j) Q c) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.R L i j) Q
      (.seq (.block (st8 (L.kgRS + 32) j)) <| .seq (.block (st8 (L.kgRS + 33) i)) <|
        .seq (sampleC 3 ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) (.seq (maskA L.kgACC L.kgA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅⟩ := KgRowOK.nb (L := L)
  obtain ⟨-, -, -, w₁, w₂⟩ := KgRowOK.seed (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.S1 L i j) (st8_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) (L.kgRS + 32) j w₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp (M := 0) (by rdecide) n₁ n₃ (m' ▸ frW8 (Y := VG.Proof.MlKem.X86.KeyGen.Y L)) h', by rw [m']; exact VG.Proof.MlKem.X86.KeyGen.st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.S2 L i j) (st8_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) (L.kgRS + 33) i w₂ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp (M := 0) (by rdecide) n₂ n₄ (m' ▸ frW8 (Y := VG.Proof.MlKem.X86.KeyGen.Y L)) h'
    refine ⟨k, ?_⟩
    rw [VG.Proof.MlKem.X86.KeyGen.seed_split hp, k.rho, keepBytes hp (N := 0) (by rdecide) n₅ (m' ▸ frW8 (Y := VG.Proof.MlKem.X86.KeyGen.Y L)), h.bj, m', VG.Proof.MlKem.X86.KeyGen.st8_byte]
    rfl
  obtain ⟨p₁, p₂, p₃⟩ := KgRowOK.samp (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.S3 L i j) (sampleC_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 L.kgRS 3 L.kgA 3 L.kgSS p₃ (by rdecide)
    (by yk_taint) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' _ _ hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp (by rdecide) p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed]; exact congrArg (matSeed · i j) hq.2.2
  · rw [h.seed] at out; exact out
  obtain ⟨q₁, q₂, q₃, q₄⟩ := KgRowOK.mask (L := L)
  refine Piece.seq (maskA_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) L.kgACC L.kgA q₄ (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  obtain ⟨s₁, s₂, s₃⟩ := acc_step h.acc hr
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s &&& s.gpr .eax := ha
  rw [← ea] at s₁ s₂ s₃
  obtain ⟨k₁, k₂⟩ := VG.Proof.MlKem.X86.KeyGen.keepS hp (M := 0) (by rdecide) q₁ fr' h.rho h.se
  obtain ⟨mr, ma⟩ := mask_poly hr hc h.red
  refine ⟨⟨h', k₁, k₂, s₁, fun e₁ k' hk' => ?_, fun e₁ => ?_, fun e₁ i' hi' => ?_⟩,
    fun hj => ⟨keepRed hp (by rdecide) q₃ fr' (h.t hj).1, fun e₁ => ?_⟩, mr, fun e₁ => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · exact h.ok (s₂ e₁).1 k' hk'
    · rw [VG.Proof.MlKem.X86.KeyGen.mS_eq s₀ hj]
      rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
      · exact ⟨_, it, e⟩
      · exact absurd ((s₂ e₁).2) (by rw [e]; decide)
  · rcases s₃ e₁ with e₂ | e₂
    · exact h.fail e₂
    · refine ⟨L.p.k * i + j, idx_lt hi hj, ?_⟩
      rw [VG.Proof.MlKem.X86.KeyGen.mS_eq s₀ hj]
      rcases h.out with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by rw [e₂]; decide)
      · exact e
  · rw [keepBytes hp (N := 0) (by rdecide) (q₂ i' (by omega)) fr']
    exact h.ek (s₂ e₁).1 i' hi'
  · rw [polyAt_congr (Top.keep hp (by rdecide) q₃ fr')]
    exact (h.t hj).2 (s₂ e₁).1
  · refine (ma (s₂ e₁).2).trans ?_
    rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
    · exact (sv_eq ⟨it, e⟩).symm
    · exact absurd ((s₂ e₁).2) (by rw [e]; decide)

/-- After `Â[i, j] ×_T ŝ[j]` is computed, for `0 < j`. -/
structure S5 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.S4 L i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bP L)) ∧
    (VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bP L)) = multiplyNTTs (VG.Proof.MlKem.X86.KeyGen.aM L s₀ i j) (VG.Proof.MlKem.X86.KeyGen.seP L s₀ j))

/-- Entry `(i, 0)`: `t̂[i] ← Â[i, 0] ×_T ŝ[0]`. -/
theorem entry0_piece (i : Nat) (hi : i < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.R L i 0) (VG.Proof.MlKem.X86.KeyGen.R L i 1) (kgEntry L i 0) := by
  obtain ⟨m₁, -, -, -, -, a₁, -, -⟩ := KgRowOK.mul (L := L)
  have hk : 0 < L.p.k := by omega
  refine VG.Proof.MlKem.X86.KeyGen.sample_piece i 0 hi hk (mulC_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 L.kgT 3 L.kgA 3 0 3 L.kgNS KgRowOK.mul0
    (by rdecide) (by yk_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se 0 (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp (by rdecide) m₁ (by omega) fr h'
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (by rdecide) a₁ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.se 0 (by omega)).2]
  rfl

/-- Entry `(i, j + 1)`: `t̂[i] ← t̂[i] + Â[i, j + 1] ×_T ŝ[j + 1]`. -/
theorem entry_piece (i j : Nat) (hi : i < L.p.k) (hj : j + 1 < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.R L i (j + 1)) (VG.Proof.MlKem.X86.KeyGen.R L i (j + 2)) (kgEntry L i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅, -, a₂, o₃⟩ := KgRowOK.mul (L := L)
  have a₃ : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bT L] = true := by
    have := (KgRowOK.mul (L := L)).2.2.1; simp only [VG.Proof.MlKem.X86.KeyGen.safe, Bool.and_eq_true] at this; exact this.1.1
  refine VG.Proof.MlKem.X86.KeyGen.sample_piece i (j + 1) hi hj (.seq (B := VG.Proof.MlKem.X86.KeyGen.S5 L i (j + 1))
    (mulC_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 L.kgP 3 L.kgA 3 (1024 * (j + 1)) 3 L.kgNS (KgRowOK.mulJ (j + 1) hj) (by rdecide)
      (by yk_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se (j + 1) (by omega)).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp (by rdecide) m₂ (by omega) fr h'
    have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (by rdecide) a₂ fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp (by rdecide) m₄ fr (h.t hj').1, fun e₁ => ?_⟩,
      keepRed hp (by rdecide) m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp (by rdecide) m₄ fr)]; exact (h.t hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp (by rdecide) m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.se (j + 1) (by omega)).2]
  refine accC_piece add_verified add_nosp add_stack 3 L.kgT 3 L.kgP o₃ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.t (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp (by rdecide) m₃ (by omega) fr h'
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (by rdecide) a₃ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.t (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

/-! ## A row -/

/-- `t̂[i]` is computed. -/
structure S6 (L : KemLay) (i : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * i + L.p.k) i s₀ s where
  t : Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bT L)) ∧
    (VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bT L)) = KPke.kgT L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀) i)

/-- Row `i`: `t̂[i] = Â[i] ∘ ŝ + ê[i]`, encoded into `ek`. -/
theorem row_piece (i : Nat) (hi : i < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * i) i) (VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * (i + 1)) (i + 1)) (kgRow L i) := by
  obtain ⟨o₁, o₂, o₃, o₄, o₅⟩ := KgRowOK.row i hi
  obtain ⟨-, -, m₃, -, -, -, -, -⟩ := KgRowOK.mul (L := L)
  have a₃ : (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bT L] = true := by
    simp only [VG.Proof.MlKem.X86.KeyGen.safe, Bool.and_eq_true] at m₃; exact m₃.1.1
  refine (Piece.seqs0 (P := VG.Proof.MlKem.X86.KeyGen.R L i) L.p.k (fun j hj => match j, hj with
    | 0, _ => VG.Proof.MlKem.X86.KeyGen.entry0_piece i hi
    | j + 1, hj => VG.Proof.MlKem.X86.KeyGen.entry_piece i j hi hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.S6 L i) (accC_piece add_verified add_nosp add_stack 3 L.kgT 3 (1024 * (L.p.k + i))
    o₁ (by rdecide) (by yk_taint) (fun _ _ _ h => ⟨h.ctx, (h.t (by omega)).1, (h.se (L.p.k + i) (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp (by rdecide) m₃ (by omega) fr h'
    have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (by rdecide) a₃ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.t (by omega)).2 (ea ▸ e₁), (h.se (L.p.k + i) (by omega)).2]
    rfl
  refine enc12C_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 L.kgT 1 (384 * i) o₂ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, h.t.1⟩) fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := VG.Proof.MlKem.X86.KeyGen.keepS hp (by rdecide) o₃ fr h.rho h.se
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (by rdecide) o₄ fr
  refine ⟨h', k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp (by rdecide) (o₅ i' hi') fr]; exact h.ek (ea ▸ e₁) i' hi'
  · rw [post, h.t.2 (ea ▸ e₁)]

/-- The `k` rows, then `c`. -/
theorem rows_piece {Q : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * L.p.k) L.p.k) Q c) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.B L 0 0) Q (seqs ((List.range L.p.k).map (kgRow L)) c) :=
  Piece.seqs0 (P := fun i => VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * i) i) L.p.k VG.Proof.MlKem.X86.KeyGen.row_piece h

end VG.Proof.MlKem.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGenFin`. -/
section

/-!
# ML-KEM on x86 (32-bit): the keys in key generation

After the rows: `ρ` copied into `ek` (which completes `ek_PKE`), `ŝ` encoded
into `dk` (`dk_PKE`, `enc_piece`), `ek` copied into `dk`, `H(ek)` hashed into
`dk`, `z` copied into `dk`, and `kgACC` loaded to be returned (`fin_piece`).
`F n` is what holds after `n` of these steps.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad sha3Suffix)

section
variable (L : KemLay)
/-- `ρ` in `ek`. -/
abbrev bEKr : Buf := ⟨1, 384 * L.p.k, 32⟩
/-- `ByteEncode₁₂(ŝ[j])` in `dk`. -/
abbrev bDK (j : Nat) : Buf := ⟨2, 384 * j, 384⟩
/-- `ek` in `dk`. -/
abbrev bDKE : Buf := ⟨2, 384 * L.p.k, L.p.ekLen⟩
/-- `H(ek)` in `dk`. -/
abbrev bDKH : Buf := ⟨2, 768 * L.p.k + 32, 32⟩
/-- `z` in `dk`. -/
abbrev bDKZ : Buf := ⟨2, 768 * L.p.k + 64, 32⟩
end

/-- After `n` of the steps that write the keys. -/
structure F (L : KemLay) (n : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * L.p.k) L.p.k s₀ s where
  rhoE : 1 ≤ n → bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bEKr L)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)
  dk : ∀ j < L.p.k, j + 2 ≤ n → bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bDK j)) 384 = encode12 (VG.Proof.MlKem.X86.KeyGen.seP L s₀ j)
  cp : L.p.k + 2 ≤ n → VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bDKE L)) L.p.ekLen = KPke.ekPKE L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀)
  hh : L.p.k + 3 ≤ n → VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bDKH L)) 32 = H (KPke.ekPKE L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀))
  zk : L.p.k + 4 ≤ n → bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bDKZ L)) 32 = VG.Proof.MlKem.X86.KeyGen.z s₀

/-- Whether `bs` is apart from what `B` and the first `n` steps state. -/
def safeF (L : KemLay) (bs : List Buf) (n : Nat) : Bool :=
  VG.Proof.MlKem.X86.KeyGen.safe L bs && (n < 1 || (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bEKr L) bs) &&
    ((List.range L.p.k).all fun j => n < j + 2 || (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bDK j) bs) &&
    (n < L.p.k + 2 || (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bDKE L) bs) && (n < L.p.k + 3 || (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bDKH L) bs) &&
    (n < L.p.k + 4 || (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bDKZ L) bs)

variable {L : KemLay}

theorem F.keep {n : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (VG.Proof.MlKem.X86.KeyGen.Y L).stk) (hs : VG.Proof.MlKem.X86.KeyGen.safeF L bs n = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.KeyGen.F L n s₀ s)
    (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.KeyGen.Y L) s₀ s') : VG.Proof.MlKem.X86.KeyGen.F L n s₀ s' := by
  simp only [VG.Proof.MlKem.X86.KeyGen.safeF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hs
  have k := h.toB.keep hp hM h₀ (Nat.le_refl _) fr c
  have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp hM (by simp only [VG.Proof.MlKem.X86.KeyGen.safe, Bool.and_eq_true] at h₀; exact h₀.1.1) fr
  refine ⟨k, fun hn => ?_, fun j hj hn => ?_, fun hn e₁ => ?_, fun hn e₁ => ?_, fun hn => ?_⟩
  · rcases h₁ with h₁ | h₁
    · omega
    · rw [keepBytes hp hM h₁ fr]; exact h.rhoE hn
  · rcases h₂ j hj with h₂ | h₂
    · omega
    · rw [keepBytes hp hM h₂ fr]; exact h.dk j hj hn
  · rcases h₃ with h₃ | h₃
    · omega
    · rw [keepBytes hp hM h₃ fr]; exact h.cp hn (ea ▸ e₁)
  · rcases h₄ with h₄ | h₄
    · omega
    · rw [keepBytes hp hM h₄ fr]; exact h.hh hn (ea ▸ e₁)
  · rcases h₅ with h₅ | h₅
    · omega
    · rw [keepBytes hp hM h₅ fr]; exact h.zk hn

/-- The facts of the layout that writing the keys uses. -/
class FinOK (L : KemLay) : Prop where
  fin : VG.Proof.MlKem.X86.KeyGen.safeF L [VG.Proof.MlKem.X86.KeyGen.bEKr L] 0 = true ∧ (∀ j < L.p.k, VG.Proof.MlKem.X86.KeyGen.safeF L [VG.Proof.MlKem.X86.KeyGen.bDK j] (j + 1) = true) ∧
    VG.Proof.MlKem.X86.KeyGen.safeF L [VG.Proof.MlKem.X86.KeyGen.bDKE L] (L.p.k + 1) = true ∧
    VG.Proof.MlKem.X86.KeyGen.safeF L [⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgST, 200⟩, ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgWK, 640⟩, VG.Proof.MlKem.X86.KeyGen.bDKH L] (L.p.k + 2) = true ∧
    VG.Proof.MlKem.X86.KeyGen.safeF L [VG.Proof.MlKem.X86.KeyGen.bDKZ L] (L.p.k + 3) = true ∧ VG.Proof.MlKem.X86.KeyGen.safeF L [] (L.p.k + 4) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [VG.Proof.MlKem.X86.KeyGen.bDKE L] = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).apart (VG.Proof.MlKem.X86.KeyGen.bACC L) [⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgST, 200⟩, ⟨(VG.Proof.MlKem.X86.KeyGen.Y L).sc, L.kgWK, 640⟩, VG.Proof.MlKem.X86.KeyGen.bDKH L] = true
  enc : ∀ j < L.p.k, ((VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bSE j) && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bDK j) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bSE j) (VG.Proof.MlKem.X86.KeyGen.bDK j)) = true
  ek : (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨1, 0, 384 * L.p.k⟩ = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bEKr L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨2, 0, 384 * L.p.k⟩ = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bDKE L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bDKH L) = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok (VG.Proof.MlKem.X86.KeyGen.bDKZ L) = true ∧
    (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨2, 0, 384 * L.p.k + L.p.ekLen⟩ = true ∧ (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨2, 0, 768 * L.p.k + 64⟩ = true
  rho : ((VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨3, L.kgRS, 4 * 8⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨1, 384 * L.p.k, 4 * 8⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgRS, 4 * 8⟩ ⟨1, 384 * L.p.k, 4 * 8⟩) = true
  cp : ((VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨1, 0, L.p.ekLen⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bDKE L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨1, 0, L.p.ekLen⟩ (VG.Proof.MlKem.X86.KeyGen.bDKE L)) = true ∧
    4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ekLen < 2 ^ 32
  hh : ((VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgST, 200⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨1, 0, L.p.ekLen⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).okW (VG.Proof.MlKem.X86.KeyGen.bDKH L) && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨1, 0, L.p.ekLen⟩ ⟨3, L.kgST, 200⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨1, 0, L.p.ekLen⟩ ⟨3, L.kgWK, 640⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨3, L.kgST, 200⟩ (VG.Proof.MlKem.X86.KeyGen.bDKH L) &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep (VG.Proof.MlKem.X86.KeyGen.bDKH L) ⟨3, L.kgWK, 640⟩) = true
  zk : ((VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨0, 32, 4 * 8⟩ && (VG.Proof.MlKem.X86.KeyGen.Y L).okW ⟨2, 768 * L.p.k + 64, 4 * 8⟩ &&
    (VG.Proof.MlKem.X86.KeyGen.Y L).sep ⟨0, 32, 4 * 8⟩ ⟨2, 768 * L.p.k + 64, 4 * 8⟩) = true
  acc : (VG.Proof.MlKem.X86.KeyGen.Y L).ok ⟨3, L.kgACC, 4⟩ = true

/-- `ek`, if every sample succeeded. -/
theorem ek_full [VG.Proof.MlKem.X86.KeyGen.FinOK L] {n : Nat} {s₀ s : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) (h : VG.Proof.MlKem.X86.KeyGen.F L n s₀ s) (hn : 1 ≤ n)
    (e : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, L.p.ekLen⟩) L.p.ekLen = KPke.ekPKE L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀) := by
  obtain ⟨o₁, o₂, -⟩ := FinOK.ek (L := L)
  rw [bytes_split hp _ (o' := 384 * L.p.k) (l₁ := 384 * L.p.k) (l₂ := 32) (L := L.p.ekLen) (Nat.zero_add _) rfl o₁ o₂,
    bytes_catK hp _ o₁, h.rhoE hn, KPke.ekPKE]
  exact congrArg (· ++ _) (catK_congr fun i hi => by rw [Nat.zero_add]; exact h.ek e i hi)

/-- `dk`, if every sample succeeded. -/
theorem dk_full [VG.Proof.MlKem.X86.KeyGen.FinOK L] {s₀ s : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) (h : VG.Proof.MlKem.X86.KeyGen.F L (L.p.k + 4) s₀ s) (e : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, L.p.dkLen⟩) L.p.dkLen =
      KPke.dkPKE L.p (VG.Proof.MlKem.X86.KeyGen.d s₀) ++ KPke.ekPKE L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀) ++ H (KPke.ekPKE L.p (VG.Proof.MlKem.X86.KeyGen.aM L s₀) (VG.Proof.MlKem.X86.KeyGen.d s₀)) ++ VG.Proof.MlKem.X86.KeyGen.z s₀ := by
  obtain ⟨-, -, o₃, o₄, o₅, o₆, o₇, o₈⟩ := FinOK.ek (L := L)
  rw [bytes_split hp _ (o' := 768 * L.p.k + 64) (l₁ := 768 * L.p.k + 64) (l₂ := 32) (Nat.zero_add _)
      (by unfold Params.dkLen; omega) o₈ o₆,
    bytes_split hp _ (o' := 768 * L.p.k + 32) (l₁ := 768 * L.p.k + 32) (l₂ := 32) (Nat.zero_add _) rfl
      (by unfold Params.ekLen at o₇; rw [show 768 * L.p.k + 32 = 384 * L.p.k + (384 * L.p.k + 32) by omega]; exact o₇) o₅,
    bytes_split hp _ (o' := 384 * L.p.k) (l₁ := 384 * L.p.k) (l₂ := L.p.ekLen) (Nat.zero_add _)
      (by unfold Params.ekLen; omega) o₃ o₄,
    bytes_catK hp _ o₃, h.cp (by omega) e, h.hh (by omega) e, h.zk (by omega), KPke.dkPKE]
  refine congrArg (fun x => x ++ _ ++ _ ++ _) (catK_congr fun j hj => ?_)
  rw [Nat.zero_add]; exact h.dk j hj (by omega)

variable [VG.Proof.MlKem.X86.KeyGen.FinOK L]

/-- `dk[384j : 384j + 384] ← ByteEncode₁₂(ŝ[j])`. -/
theorem enc_piece (j : Nat) (hj : j < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.F L (j + 1)) (VG.Proof.MlKem.X86.KeyGen.F L (j + 2)) (kgEnc j) := by
  refine enc12C_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 (1024 * j) 2 (384 * j) (FinOK.enc j hj) (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.se j (by omega)).1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.keep hp (by rdecide) ((FinOK.fin (L := L)).2.1 j hj) fr h'
  refine ⟨k.toB, fun hn => k.rhoE (by omega), fun j' hj' hn => ?_, fun hn => by omega, fun hn => by omega,
    fun hn => by omega⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | e
  · exact k.dk j' hj' (by omega)
  · obtain rfl : j' = j := by omega
    rw [post, (h.se j' (by omega)).2]

/-- After the keys are written: `kgACC` returned. -/
structure Done (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.KeyGen.F L (L.p.k + 4) s₀ s where
  eax : s.gpr .eax = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s

/-- The keys, from the rows. -/
theorem fin_piece [VG.Proof.MlKem.X86.KeyGen.GOK L] :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (VG.Proof.MlKem.X86.KeyGen.B L (L.p.k * L.p.k) L.p.k) (VG.Proof.MlKem.X86.KeyGen.Done L)
      (.seq (copyW 3 ⟨3, L.kgRS, 32⟩ ⟨1, 384 * L.p.k, 32⟩ 8) <|
        seqs ((List.range L.p.k).map kgEnc) <|
        .seq (copyW 3 ⟨1, 0, L.p.ekLen⟩ ⟨2, 384 * L.p.k, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (hash1 3 L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩ ⟨2, 768 * L.p.k + 32, 32⟩) <|
        .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 768 * L.p.k + 64, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi L.kgACC))])) := by
  obtain ⟨f₁, -, f₄, f₅, f₆, f₇, f₈, f₉⟩ := FinOK.fin (L := L)
  obtain ⟨c₁, c₂, c₃, c₄, c₅⟩ := FinOK.cp (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.F L 1) (copyW_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 3 L.kgRS 1 (384 * L.p.k) 8 (by decide) (by decide)
    FinOK.rho (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (M := 0) (by rdecide)
      (by simp only [VG.Proof.MlKem.X86.KeyGen.safeF, Bool.and_eq_true] at f₁; exact f₁.1.1.1.1.1) (Nat.le_refl _) (fr1 fr) h'
    refine ⟨k, fun _ => ?_, fun _ _ hn => by omega, fun hn => by omega, fun hn => by omega, fun hn => by omega⟩
    rw [show Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bEKr L) = Buf.addr s₀ ⟨1, 384 * L.p.k, 4 * 8⟩ from rfl, post]
    exact h.rho
  refine Piece.seqs0 (P := fun i => VG.Proof.MlKem.X86.KeyGen.F L (i + 1)) L.p.k (fun j hj => VG.Proof.MlKem.X86.KeyGen.enc_piece j hj) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.F L (L.p.k + 2)) (copyW_piece' (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 1 0 2 (384 * L.p.k) (L.p.ekLen / 4) L.p.ekLen
    c₂ c₃ c₄ c₁ (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by rdecide) f₄ (fr1 fr) h'
    have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (N := 0) (by rdecide) f₈ (fr1 fr)
    refine ⟨k.toB, fun _ => k.rhoE (by omega), fun j hj _ => k.dk j hj (by omega), fun _ e₁ => ?_,
      fun hn => by omega, fun hn => by omega⟩
    rw [post]
    exact VG.Proof.MlKem.X86.KeyGen.ek_full hp h (by omega) (ea ▸ e₁)
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.F L (L.p.k + 3)) (hash1_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩
    ⟨2, 768 * L.p.k + 32, 32⟩ rate136 FinOK.hh (by rdecide) c₅ (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint)
    (by yk_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ?_) ?_
  · have k := h.keep hp (by rdecide) f₅ fr h'
    have ea : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s' = VG.Proof.MlKem.X86.KeyGen.accV L s₀ s := keepW hp (by rdecide) f₉ fr
    refine ⟨k.toB, fun _ => k.rhoE (by omega), fun j hj _ => k.dk j hj (by omega), fun _ => k.cp (by omega),
      fun _ e₁ => ?_, fun hn => by omega⟩
    rw [out, VG.Proof.MlKem.X86.KeyGen.ek_full hp h (by omega) (ea ▸ e₁), show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32,
      ← padded, ← H_eq]
  refine Piece.seq (B := VG.Proof.MlKem.X86.KeyGen.F L (L.p.k + 4)) (copyW_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) 0 32 2 (768 * L.p.k + 64) 8 (by decide)
    (by decide) FinOK.zk (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by rdecide) f₆ (fr1 fr) h'
    refine ⟨k.toB, fun _ => k.rhoE (by omega), fun j hj _ => k.dk j hj (by omega), fun _ => k.cp (by omega),
      fun _ => k.hh (by omega), fun _ => ?_⟩
    rw [show Buf.addr s₀ (VG.Proof.MlKem.X86.KeyGen.bDKZ L) = Buf.addr s₀ ⟨2, 768 * L.p.k + 64, 4 * 8⟩ from rfl, post]
    exact h.ctx.roBytes hp (b := ⟨0, 32, 32⟩) (by rdecide) rfl
  exact ld32_piece (Y := VG.Proof.MlKem.X86.KeyGen.Y L) L.kgACC FinOK.acc (by yk_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨h.keep hp (bs := []) (M := 0) (by rdecide) f₇
      (m' ▸ Frame.refl _ _) h',
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']; rfl⟩

end VG.Proof.MlKem.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGenBody`. -/
section

/-!
# ML-KEM on x86 (32-bit): the body of key generation

The body is the start (`KeyGenG.lean`), `ŝ` and `ê` (`KeyGenPrf.lean`), the
rows of `t̂` (`KeyGenRow.lean`) and the keys (`KeyGenFin.lean`). If every
`SampleNTT` succeeded (`kgACC` is 1), `samp_bound` gives one bound on their
iterations, within which K-PKE.KeyGen succeeds with the matrix sampled
(`KPke.kpkeKeyGen_some`); if one failed within `minIterations`, K-PKE.KeyGen
fails with that bound (`KPke.kpkeKeyGen_none`) (`post`). Two runs with the
same pointers and `ρ` leak the same: the contract lets the function leak `ρ`.
Each parameter set's contract implies `TPre (Y L)` and its public data
(`Proof/MlKem/X86/KeyGen.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay}

theorem body_piece [VG.Proof.MlKem.X86.KeyGen.GOK L] [VG.Proof.MlKem.X86.KeyGen.PrfOK L] [VG.Proof.MlKem.X86.KeyGen.KgRowOK L] [VG.Proof.MlKem.X86.KeyGen.FinOK L] :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (fun s₀ s => s = P0 s₀) (VG.Proof.MlKem.X86.KeyGen.Done L) (kgBody L) :=
  VG.Proof.MlKem.X86.KeyGen.start_piece <| prfs_piece <| rows_piece VG.Proof.MlKem.X86.KeyGen.fin_piece |>.mono (fun _ _ _ h =>
    ⟨h.ctx, h.rho, h.se, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

theorem piece [VG.Proof.MlKem.X86.KeyGen.GOK L] [VG.Proof.MlKem.X86.KeyGen.PrfOK L] [VG.Proof.MlKem.X86.KeyGen.KgRowOK L] [VG.Proof.MlKem.X86.KeyGen.FinOK L] (hsp : NoSp (kgBody L)) :
    Piece (TPre (VG.Proof.MlKem.X86.KeyGen.Y L)) (TPub (VG.Proof.MlKem.X86.KeyGen.Y L) (VG.Proof.MlKem.X86.KeyGen.lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.KeyGen.Done L s₀) s₀ s')
      (leaf (kgBody L)) :=
  topLeaf hsp (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- Every sample, within one bound. -/
theorem samples {s₀ s : State} (h : VG.Proof.MlKem.X86.KeyGen.Done L s₀ s) (e : VG.Proof.MlKem.X86.KeyGen.accV L s₀ s = 1) :
    ∃ M, ∀ i < L.p.k, ∀ j < L.p.k, sampleNTT M (matSeed (KPke.kgRho L.p (VG.Proof.MlKem.X86.KeyGen.d s₀)) i j) = some (VG.Proof.MlKem.X86.KeyGen.aM L s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range (L.p.k * L.p.k)).map fun k =>
      (VG.Proof.MlKem.X86.KeyGen.mS L s₀ k, VG.Proof.MlKem.X86.KeyGen.aM L s₀ (k / L.p.k) (k % L.p.k))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (VG.Proof.MlKem.X86.KeyGen.mS L s₀ k) (sv (VG.Proof.MlKem.X86.KeyGen.mS L s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (VG.Proof.MlKem.X86.KeyGen.mS L s₀ (L.p.k * i + j), VG.Proof.MlKem.X86.KeyGen.aM L s₀ ((L.p.k * i + j) / L.p.k) ((L.p.k * i + j) % L.p.k))
    (List.mem_map.mpr ⟨L.p.k * i + j, List.mem_range.mpr (idx_lt hi hj), rfl⟩)
  rw [VG.Proof.MlKem.X86.KeyGen.mS_eq s₀ hj, idx_div hj, idx_mod hj] at r
  exact r

/-- The postcondition, from the final state of the body. -/
theorem post [VG.Proof.MlKem.X86.KeyGen.FinOK L] (hη : L.p.η₁ = 2) {s₀ s : State} (hp : TPre (VG.Proof.MlKem.X86.KeyGen.Y L) s₀) (h : VG.Proof.MlKem.X86.KeyGen.Done L s₀ s) :
    Outcome (fun iters => keyGenInternal L.p iters (VG.Proof.MlKem.X86.KeyGen.d s₀) (VG.Proof.MlKem.X86.KeyGen.z s₀)) (VG.Proof.MlKem.X86.KeyGen.accV L s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, L.p.ekLen⟩) L.p.ekLen,
        bytesAt s.mem (Buf.addr s₀ ⟨2, 0, L.p.dkLen⟩) L.p.dkLen) := by
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; omega
    refine .inr ⟨e, ?_⟩
    show keyGenInternal L.p minIterations (VG.Proof.MlKem.X86.KeyGen.d s₀) (VG.Proof.MlKem.X86.KeyGen.z s₀) = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (i := k / L.p.k) (j := k % L.p.k)
      (Nat.div_lt_of_lt_mul hk) (Nat.mod_lt _ hk0) hn]
    rfl
  · obtain ⟨M, hM⟩ := VG.Proof.MlKem.X86.KeyGen.samples h e
    refine .inl ⟨e, M, ?_⟩
    show keyGenInternal L.p M (VG.Proof.MlKem.X86.KeyGen.d s₀) (VG.Proof.MlKem.X86.KeyGen.z s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some hη hM, VG.Proof.MlKem.X86.KeyGen.ek_full hp h.toF (by omega) e, VG.Proof.MlKem.X86.KeyGen.dk_full hp h.toF e]
    rfl

end VG.Proof.MlKem.X86.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.KeyGen`. -/
section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_keygen`

Key generation (`KeyGenBody.lean`) for ML-KEM-768 (`L768`): the facts of its
layout (`GOK`, `PrfOK`, `KgRowOK`, `FinOK`), computed from its offsets; the
contract's precondition implies `TPre (Y L768)` (`pre_of`) and its public data
`TPub`, which includes `ρ` (`pub_of`).
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

instance : VG.Proof.MlKem.X86.KeyGen.GOK L768 where
  rs := by decide
  g := by decide

instance : VG.Proof.MlKem.X86.KeyGen.PrfOK L768 where
  sig := by decide
  nb := by decide
  hash := by decide
  prf := by decide

instance : VG.Proof.MlKem.X86.KeyGen.KgRowOK L768 where
  seed := by decide
  nb := by decide
  samp := by decide
  mask := by decide
  mul := by decide
  mul0 := by decide
  mulJ := by decide
  row := by decide

instance : VG.Proof.MlKem.X86.KeyGen.FinOK L768 where
  fin := by decide
  enc := by decide
  ek := by decide
  rho := by decide
  cp := by decide
  hh := by decide
  zk := by decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (keyGenContract X86.abi 88).pre s₀) : TPre (VG.Proof.MlKem.X86.KeyGen.Y L768) s₀ := by
  sig_pre [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (VG.Proof.MlKem.X86.KeyGen.Y L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [VG.Proof.MlKem.X86.KeyGen.Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [VG.Proof.MlKem.X86.KeyGen.Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    all_goals simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlKem.X86.KeyGen.Y, L768, Params.ekLen, Params.dkLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, VG.Proof.MlKem.X86.KeyGen.Y]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, h5, h6, h7, h5.symm, absurd rfl hne, h9, h10, h6.symm, h9.symm, absurd rfl hne, h12,
      h7.symm, h10.symm, h12.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {s₀ s₀' : State} (h : (keyGenContract X86.abi 88).pub s₀ s₀') : TPub (VG.Proof.MlKem.X86.KeyGen.Y L768) (VG.Proof.MlKem.X86.KeyGen.lk L768) s₀ s₀' := by
  sig_pub [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [VG.Proof.MlKem.X86.KeyGen.Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · simp only [VG.Proof.MlKem.X86.KeyGen.lk, VG.Proof.MlKem.X86.KeyGen.d, VG.Proof.MlKem.X86.KeyGen.addr0]
    exact map_toNat_inj e₂

/-- Memory with the arguments `0`, `0x100`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.keyGen (keyGenContract X86.abi 88) := by
  refine Piece.verified (((VG.Proof.MlKem.X86.KeyGen.piece (L := L768) (NoSp.of_all (by decide +kernel))).pre_mono (fun _ h => VG.Proof.MlKem.X86.KeyGen.pre_of h) fun _ _ _ _ h => VG.Proof.MlKem.X86.KeyGen.pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := VG.Proof.MlKem.X86.KeyGen.pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := VG.Proof.MlKem.X86.KeyGen.post (by decide) hp hfin
    have ez : Buf.addr s₀ ⟨0, 32, 32⟩ = (arg s₀ 0).setWidth 64 + 32 := Buf.addr_eq hp (by decide)
    simp only [VG.Proof.MlKem.X86.KeyGen.d, VG.Proof.MlKem.X86.KeyGen.z, VG.Proof.MlKem.X86.KeyGen.addr0, ez, show Buf.addr s₀ ⟨1, 0, L768.p.ekLen⟩ = (arg s₀ 1).setWidth 64 from VG.Proof.MlKem.X86.KeyGen.addr0 s₀ 1,
      show Buf.addr s₀ ⟨2, 0, L768.p.dkLen⟩ = (arg s₀ 2).setWidth 64 from VG.Proof.MlKem.X86.KeyGen.addr0 s₀ 2] at r
    exact r
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlKem.X86.KeyGen.satMem [⟨0, 64⟩]
      [⟨0x100, 1184⟩, ⟨0x1000, 2400⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [keyGenContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.KeyGen

end
