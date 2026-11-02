module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: the contracts by register

For a modulus `S` of `k ≥ 7` words, `mulFn k m`, `addFn k m` and `subFn k m`
(`Impl/Weierstrass/RISCV64/GenWide.lean`) meet the contracts by register of
`Proof/Weierstrass/RISCV64/FieldRV.lean` (`mul_rv`, `add_rv`, `sub_rv`), from
`fn_ok`: `numAt` of an offset is the `k` doublewords there (`numAt_xv`), and
the regions the functions write, the top `64 k` bytes of the working space
(`rvOwn k`) and the result, keep every other byte (`keeps_of_frame`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X448.RISCV64.R64 (dw colsV)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV rvOwn rvOwnEnd)

theorem wordsVal_colsV (m : Mem) (P : Addr) : ∀ (k d : Nat),
    VG.Proof.Mont.wordsVal m P d k = colsV (fun i => dw m P (d + 8 * i)) k
  | 0, _ => rfl
  | k + 1, d => by
    rw [VG.Proof.Mont.wordsVal, wordsVal_colsV m P k (d + 8), colsV_shift]
    simp only [Nat.mul_zero, Nat.add_zero, show ∀ i, d + 8 + 8 * i = d + 8 * (i + 1) from fun i => by omega]
    rfl

theorem numAt_xv (m : Mem) (W : Addr) (o : BitVec 32) (k : Nat) :
    numAt m W o k = xv m (W + BitVec.ofNat 64 o.toNat) k := by
  have h := VG.Proof.Mont.read_eq_wordsVal m (W + BitVec.ofNat 64 o.toNat) k 0
  simp only [VG.Proof.Mont.off, BitVec.add_zero] at h
  rw [numAt, h, wordsVal_colsV]
  simp only [Nat.zero_add]

theorem rvOwn_gt {k : Nat} (h : 6 < k) : rvOwn k = 8192 - 64 * k := by
  simp [rvOwn, show ¬ k ≤ 6 by omega, Impl.Weierstrass.Mont.wsBytes, Impl.Weierstrass.Mont.ownBytes]

theorem rvOwnEnd_gt {k : Nat} (h : 6 < k) : rvOwnEnd k = 8192 := by
  simp [rvOwnEnd, show ¬ k ≤ 6 by omega, Impl.Weierstrass.Mont.wsBytes]

/-- A byte of the working space outside a range of it. -/
theorem byte_out {W : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Contains (W + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint W (d := i) (n := 1) (e := e) (k := k) (by omega) (by omega) (by omega) _
    (Region.contains_self _ _) hc

/-- The regions the functions write keep every byte the contracts do. -/
theorem keeps_of_frame {k : Nat} (hk : 6 < k) (hk' : k ≤ 30) {W : Addr} {o : BitVec 32}
    (ho : o.toNat + 8 * k ≤ 8192 - 64 * k) {m m' : Mem} (hf : Frame (fnW k W o.toNat) m m') :
    Keeps k W o m m' (rvOwn k) (rvOwnEnd k) := by
  intro i hi hown hoi
  rw [rvOwn_gt hk, rvOwnEnd_gt hk] at hown
  simp only [Impl.Weierstrass.Mont.wsBytes] at hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega) (by omega) (by omega)
  · exact byte_out (by omega) (by omega) hoi

/-- `fn k core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {S : Modulus} (hk : 7 ≤ S.k) (hk' : S.k ≤ 30) {core : List Instr} {pre : Nat → Nat → Prop}
    {res : Nat → Nat → Nat → Prop} (hcore : CoreSpec S.k core pre res) {s : State} (hs : rvPre S s)
    (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fn S.k core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) S.k) ∧
      Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k) := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, rvOwn_gt (show 6 < S.k by omega)] at fo fa fb
  simp only [arg, numAt_xv] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hk hk' hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame (by omega) hk' fo f⟩

/-- What a wide modulus needs: its words, and `m'`. -/
structure WideOk (S : Modulus) : Prop where
  k7 : 7 ≤ S.k
  k30 : S.k ≤ 30
  lt : S.m < 2 ^ (64 * S.k)
  inv : (wordOf S.m 0).toNat * negInv S.m % 2 ^ 64 = 2 ^ 64 - 1

theorem mul_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv hS.k7 hS.k30 (@mulCore_spec S.k S.m hS.lt hS.inv) hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem add_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa (addFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hS.k7 hS.k30 (@addCore_spec S.k S.m hS.lt) hs.1 hs.2
  exact ⟨t, s', he, a, v, k⟩

theorem sub_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa (subFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hS.k7 hS.k30 (@subCore_spec S.k S.m hS.lt) hs.1 hs.2
  exact ⟨t, s', he, a, v, k⟩

end VG.Proof.Weierstrass.RISCV64.GenWide
