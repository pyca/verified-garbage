module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rsa.MontMulFixedContract
public import VerifiedGarbage.Impl.Bignum.AArch64.MulFixedCall
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Callable Montgomery products against the fixed-index contract
(`Proof.Rsa.MontMulFixed`), for the indices of `MulFixedCall.shared`. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.MulFixedHelper
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Keeps arrAt aM minvWord Operand)
open VG.Proof.Rsa.MontMulFixed (Indices)
open VG.Impl.Bignum.AArch64.MulFixedCall (shared)

/-- The shared ABI specialized to its two arguments. -/
def fnContract (o a b : Nat) : Contract isa where
  pre s :=
    let ws := s.gpr .x0
    let n := (s.gpr .x1).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ ws.toNat + n * 8 ≤ 2 ^ 64 ∧
      Layout s.mem ws n ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
        (wordAt s.mem ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
      numAt s.mem ws w b < numAt s.mem ws w aM
  post s t :=
    let ws := s.gpr .x0
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt t.mem ws w o < M ∧
      numAt t.mem ws w o * 2 ^ (64 * w) % M = numAt s.mem ws w a * numAt s.mem ws w b % M ∧
      Keeps ws (s.gpr .x1).toNat w o s.mem t.mem
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    wOf s.mem (s.gpr .x0) = wOf t.mem (t.gpr .x0)

def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 512 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 64 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 512⟩]

theorem read_eq_wv (m : Mem) (B : Addr) (d : Nat) :
    ∀ k, (m.read (off B d) (8 * k)).toNat = wv m B d k
  | 0 => by simp [Mem.read, wv]
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Proof.Mont.read_toNat_add,
      read_eq_wv m B d k, wv, Offset.add_add, show 8 * (8 * k) = 64 * k by omega]
    congr 2

theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) :
    numAt m B w j = wv m B (slot w j) w := by
  rw [← read_eq_wv]; rfl

theorem fn_good {o a b : Nat} {s : State} (h : (fnContract o a b).pre s) :
    Good s (s.gpr .x0) ((s.gpr .x1).toNat * 8) (wOf s.mem (s.gpr .x0))
      (wordAt s.mem (s.gpr .x0) minvWord) ∧
    slot (wOf s.mem (s.gpr .x0)) 8 ≤ (s.gpr .x1).toNat * 8 ∧
    2 ≤ wOf s.mem (s.gpr .x0) ∧ wOf s.mem (s.gpr .x0) < 2 ^ 31 := by
  obtain ⟨_, hwr, hnw, ⟨h2, h31, h8, harr⟩, _⟩ := h
  refine ⟨⟨Scr.of_mem (by rw [hwr]; simp) hnw, rfl, ⟨?_, rfl, fun j hj => harr j hj⟩⟩,
    ?_, h2, h31⟩
  · simp [word, wOf, wordAt, Proof.Rsa.Mont.wWord, sW, off]
  · simpa only [slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.mul_comm] using h8

/-- The shared indices are operands, with a constant-time product. -/
theorem shared_ok {o a b : Nat} (h : (o, a, b) ∈ shared) :
    Operand o ∧ Operand a ∧ Operand b ∧ MmUse o a b := by
  simp only [shared, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · unfold Operand MmUse; decide

theorem fn_implies (ix : Indices) (h : (ix.o, ix.a, ix.b) ∈ shared) :
    (fnContract ix.o ix.a ix.b).Implies (Proof.Rsa.MontMulFixed.mulContract ix abi) where
  pre := by
    sig_implies_pre [Proof.Rsa.MontMulFixed.mulContract, Proof.Rsa.MontMulFixed.sig, fnContract, abi, argRegs]
  post := by
    sig_implies_post [Proof.Rsa.MontMulFixed.mulContract, Proof.Rsa.MontMulFixed.sig, fnContract, abi, argRegs]
  pub := by
    rintro s t _ _ h
    sig_pub [Proof.Rsa.MontMulFixed.mulContract, Proof.Rsa.MontMulFixed.sig, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, h0, h1⟩ := h
    exact ⟨hsp, h0, h1, List.singleton_inj.mp hw⟩
  sat := by
    obtain ⟨o, a, b⟩ := ix
    simp only [shared, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    sig_implies_sat [Proof.Rsa.MontMulFixed.mulContract, Proof.Rsa.MontMulFixed.sig, fnContract, abi, argRegs,
      Operand] [satState] using satState

theorem fn_correct (M : Mont) {o a b : Nat} (hix : (o, a, b) ∈ shared) (s : State)
    (h : (fnContract o a b).pre s) :
    ∃ tr t, Exec isa (M.mm o a b) s tr t ∧ abiPreserved s t ∧ (fnContract o a b).post s t := by
  obtain ⟨⟨ho8, ho2, ho3⟩, ⟨ha8, ha2, ha3⟩, ⟨hb8, hb2, hb3⟩, -⟩ := shared_ok hix
  obtain ⟨hg, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨_, _, hnw, _, hi, hB⟩ := h
  rw [numAt_eq, numAt_eq] at hB
  obtain ⟨tr, t, he, _, hlt, heq, har, hk⟩ := M.ok hg hZ hw hw' ho8 ha8 hb8 ho2 ho3 ha2 ha3 hb2 hb3 hi hB
  refine ⟨tr, t, he, ⟨fun r hr => hk.gpr r (by revert r; decide), hk.sp, hk.vcs⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [numAt_eq, numAt_eq]; exact hlt
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    exact har (s.gpr .x0 + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .x0) (s.gpr .x0 + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'

theorem fn_ct (M : Mont) {o a b : Nat} (hix : (o, a, b) ∈ shared) :
    ConstantTime isa (fnContract o a b).pre (fnContract o a b).pub (M.mm o a b) := by
  apply RelCT.constantTime ((M.ct (shared_ok hix).2.2.2).mono ?_ (fun _ _ h => h))
  rintro s t ⟨hs, ht, hsp, h0, h1, hw⟩
  obtain ⟨gs, zs, _⟩ := fn_good hs
  obtain ⟨gt, zt, _⟩ := fn_good ht
  refine ⟨⟨s.gpr .x0, (s.gpr .x1).toNat * 8, wOf s.mem (s.gpr .x0)⟩,
    ⟨_, gs, zs⟩, ?_, hsp⟩
  rw [hw, h0, h1]
  exact ⟨_, gt, zt⟩

theorem verified (M : Mont) (ix : Indices) (h : (ix.o, ix.a, ix.b) ∈ shared := by decide) :
    Verified target (M.mm ix.o ix.a ix.b) (Proof.Rsa.MontMulFixed.mulContract ix abi) :=
  Verified.of_correct (fn_correct M h) (fn_ct M h) (fn_implies ix h)

end VG.Proof.Bignum.AArch64.MulFixedHelper
