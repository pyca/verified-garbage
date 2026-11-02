module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rsa.MontSquareContract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Callable Montgomery squares against the reviewed fixed-slot contract. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareHelper
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Keeps arrAt aM minvWord)
open VG.Proof.Rsa.MontSquare (Slot)

/-- The shared ABI specialized to its two arguments. -/
def fnContract (o : Nat) : Contract isa where
  pre s :=
    let ws := s.gpr .x0
    let n := (s.gpr .x1).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ ws.toNat + n * 8 ≤ 2 ^ 64 ∧
      Layout s.mem ws n ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat *
        (wordAt s.mem ws minvWord).toNat + 1) % 2 ^ 64 = 0 ∧
      numAt s.mem ws w o < numAt s.mem ws w aM
  post s t :=
    let ws := s.gpr .x0
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt t.mem ws w o < M ∧
      numAt t.mem ws w o * 2 ^ (64 * w) % M = numAt s.mem ws w o * numAt s.mem ws w o % M ∧
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

theorem fn_implies (slot : Slot) :
    (fnContract slot.index).Implies (Proof.Rsa.MontSquare.squareContract slot abi) where
  pre := by sig_implies_pre [Proof.Rsa.MontSquare.squareContract, Proof.Rsa.MontSquare.sig, fnContract, abi, argRegs]
  post := by sig_implies_post [Proof.Rsa.MontSquare.squareContract, Proof.Rsa.MontSquare.sig, fnContract, abi, argRegs]
  pub := by
    rintro s t _ _ h
    sig_pub [Proof.Rsa.MontSquare.squareContract, Proof.Rsa.MontSquare.sig, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, h0, h1⟩ := h
    exact ⟨hsp, h0, h1, List.singleton_inj.mp hw⟩
  sat := by
    cases slot <;>
      sig_implies_sat [Proof.Rsa.MontSquare.squareContract, Proof.Rsa.MontSquare.sig, fnContract, abi, argRegs]
        [satState] using satState

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

theorem fn_good {o : Nat} {s : State} (h : (fnContract o).pre s) :
    Good s (s.gpr .x0) ((s.gpr .x1).toNat * 8) (wOf s.mem (s.gpr .x0))
      (wordAt s.mem (s.gpr .x0) minvWord) ∧
    slot (wOf s.mem (s.gpr .x0)) 8 ≤ (s.gpr .x1).toNat * 8 ∧
    2 ≤ wOf s.mem (s.gpr .x0) ∧ wOf s.mem (s.gpr .x0) < 2 ^ 31 := by
  obtain ⟨_, hwr, hnw, ⟨h2, h31, h8, harr⟩, _⟩ := h
  refine ⟨⟨Scr.of_mem (by rw [hwr]; simp) hnw, rfl, ⟨?_, rfl, fun j hj => harr j hj⟩⟩,
    ?_, h2, h31⟩
  · simp [word, wOf, wordAt, Proof.Rsa.Mont.wWord, sW, off]
  · simpa only [slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.mul_comm] using h8

theorem fn_correct (M : Mont) (o : Nat) (ho : o = 4 ∨ o = 6) (s : State)
    (h : (fnContract o).pre s) :
    ∃ tr t, Exec isa (M.mm o o o) s tr t ∧ abiPreserved s t ∧ (fnContract o).post s t := by
  obtain ⟨hg, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨_, _, hnw, _, hi, hb⟩ := h
  rw [numAt_eq, numAt_eq] at hb
  have h8 : o < 8 := by omega
  have h2 : o ≠ Public.aAcc := by rcases ho with rfl | rfl <;> decide
  have h3 : o ≠ Public.aTmp := by rcases ho with rfl | rfl <;> decide
  obtain ⟨tr, t, he, _, hlt, heq, har, hk⟩ := M.ok hg hZ hw hw' h8 h8 h8 h2 h3 h2 h3 h2 h3 hi hb
  refine ⟨tr, t, he, ⟨fun r hr => hk.gpr r (by revert r; decide), hk.sp, hk.vcs⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [numAt_eq, numAt_eq]; exact hlt
  · rw [numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    exact har (s.gpr .x0 + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .x0) (s.gpr .x0 + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'

theorem fn_ct (M : Mont) (o : Nat) (ho : o = 4 ∨ o = 6) :
    ConstantTime isa (fnContract o).pre (fnContract o).pub (M.mm o o o) := by
  have huse : MmUse o o o := by rcases ho with rfl | rfl <;> unfold MmUse <;> decide
  apply RelCT.constantTime ((M.ct huse).mono ?_ (fun _ _ h => h))
  rintro s t ⟨hs, ht, hsp, h0, h1, hw⟩
  obtain ⟨gs, zs, _⟩ := fn_good hs
  obtain ⟨gt, zt, _⟩ := fn_good ht
  refine ⟨⟨s.gpr .x0, (s.gpr .x1).toNat * 8, wOf s.mem (s.gpr .x0)⟩,
    ⟨_, gs, zs⟩, ?_, hsp⟩
  rw [hw, h0, h1]
  exact ⟨_, gt, zt⟩

theorem verified (M : Mont) (slot : Slot) :
    Verified target (M.mm slot.index slot.index slot.index)
      (Proof.Rsa.MontSquare.squareContract slot abi) :=
  Verified.of_correct (fn_correct M slot.index (by cases slot <;> simp [Slot.index]))
    (fn_ct M slot.index (by cases slot <;> simp [Slot.index])) (fn_implies slot)

end VG.Proof.Bignum.AArch64.SquareHelper
