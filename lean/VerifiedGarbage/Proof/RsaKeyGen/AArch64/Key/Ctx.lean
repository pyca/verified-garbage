module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Contract
public import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# An RSA key from its primes on AArch64: the precondition, as the code uses it

`keyIn s`: the inputs, from the state on entry; `KOuts`: the outputs
writable, outside the working space and apart; `KCtx s`: what the code uses
of `keyPre` (`keyCtx_of`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Spec.Rsa (bytesAt)

/-- The inputs, from the state on entry. -/
def keyIn (s : State) : KIn where
  B := arg s 8
  Z := (arg s 9).toNat * 8
  pl := (s.gpr .x5).toNat
  pN := s.gpr .x0
  pD := s.gpr .x2
  pP := s.gpr .x4
  pQ := s.gpr .x6
  pDp := arg s 0
  pDq := arg s 2
  pQi := arg s 4
  pE := arg s 6
  el := (arg s 7).toNat
  pb := bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  qb := bytesAt s.mem (s.gpr .x6) (s.gpr .x5).toNat
  eb := bytesAt s.mem (arg s 6) (arg s 7).toNat
  Wr := s.wr

/-- The outputs, in the order of the stores. -/
def outsL (I : KIn) : List (Addr × Nat) :=
  [(I.pN, 2 * I.pl), (I.pD, 2 * I.pl), (I.pP, I.pl), (I.pQ, I.pl), (I.pDp, I.pl), (I.pDq, I.pl), (I.pQi, I.pl)]

/-- The outputs: writable, outside the working space, apart. -/
structure KOuts (I : KIn) : Prop where
  wr : ∀ o ∈ outsL I, ∀ i < o.2, InRegions I.Wr (o.1 + BitVec.ofNat 64 i) 1
  sep : ∀ o ∈ outsL I, ∀ i < o.2, I.Z ≤ ofs I.B (o.1 + BitVec.ofNat 64 i)
  apart : (outsL I).Pairwise fun a b => Apart a.1 a.2 b.1 b.2

/-- What the code uses of `keyPre`. -/
structure KCtx (s : State) : Prop where
  L : KLens (keyIn s)
  x1 : (s.gpr .x1).toNat = 2 * (s.gpr .x5).toNat
  hs : Scr s (arg s 8) ((arg s 9).toNat * 8)
  hZ : 128 * (s.gpr .x1).toNat ≤ (arg s 9).toNat * 8
  ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 10, ∀ m', Outside (arg s 8) 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j
  p : Src s (arg s 8) ((arg s 9).toNat * 8) (s.gpr .x4) (keyIn s).pb
  q : Src s (arg s 8) ((arg s 9).toNat * 8) (s.gpr .x6) (keyIn s).qb
  e : Src s (arg s 8) ((arg s 9).toNat * 8) (arg s 6) (keyIn s).eb
  O : KOuts (keyIn s)

theorem kStk_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

theorem kStk_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [kStk_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem kApart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

theorem keyCtx_of {s : State} (h : keyPre s) : KCtx s := by
  simp only [keyPre] at h
  sig_split h
  rename_i hsp hrd hwr dnd dnp dnq dndp dndq dnqi dne dns dna ddp ddq dddp dddq ddqi dde dds dda dpq
    dpdp dpdq dpqi dpe dps dpa dqdp dqdq dqqi dqe dqs dqa dpdq' dpqi' dpe' dps' dpa' dqqi' dqe' dqs'
    dqa' dqie dqis dqia des dsa wn wd wp wq wdp wdq wqi we ws hpl hx1 hx3 hx7 hdpl hdql hqil hel1
    hel8
  have hsl := h
  obtain ⟨hpl1, hpl2, hpl8⟩ := hpl
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (arg s 8) ((arg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) ws
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  simp only [hx3, hx1] at dnd ddp ddq dddp dddq ddqi dde dds dda wd
  simp only [hx1] at dnp dnq dndp dndq dnqi dne dns dna wn
  simp only [hx7] at dnq ddq dpq dqdp dqdq dqqi dqe dqs dqa wq
  simp only [hdpl] at dndp dddp dpdp dqdp dpdq' dpqi' dpe' dps' dpa' wdp
  simp only [hdql] at dndq dddq dpdq dqdq dpdq' dqqi' dqe' dqs' dqa' wdq
  simp only [hqil] at dnqi ddqi dpqi dqqi dpqi' dqqi' dqie dqis dqia wqi
  have hwr' : ∀ (o : Addr) (l : Nat), (⟨o, l⟩ : Region) ∈ s.wr → l ≤ 2 ^ 64 → ∀ i < l,
      InRegions s.wr (o + BitVec.ofNat 64 i) 1 := fun o l hm hl i hi => ⟨_, hm, contains_byte o hi hl⟩
  refine ⟨⟨hpl1, hpl2, hpl8, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, hel1, hel8⟩, hx1, hs,
    by omega_using [hsl],
    fun j hj => ⟨_, hargs, by rw [kStk_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega_using [hj, hb]) (by omega_using []))
      rw [← kStk_add s j b] at this; omega_using [hsl, this])),
    src_of_region (by rw [hwr]; simp) (by omega_using []) dps,
    src_of_region (by rw [hwr]; simp [hx7]) (by omega_using []) dqs,
    src_of_region (by rw [hrd]; simp) (by omega_using []) des,
    ⟨fun o ho => ?_, fun o ho => ?_, ?_⟩⟩
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact hwr' _ _ (by rw [hwr, hx1]; simp) (by omega_using [wn])
    · exact hwr' _ _ (by rw [hwr, hx3, hx1]; simp) (by omega_using [wn])
    · exact hwr' _ _ (by rw [hwr]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hx7]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hdpl]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hdql]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hqil]; simp) (by omega_using [])
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> intro i hi
    · exact out_scr dns (contains_byte _ hi (by omega_using [wn]))
    · exact out_scr dds (contains_byte _ hi (by omega_using [wn]))
    · exact out_scr dps (contains_byte _ hi (by omega_using []))
    · exact out_scr dqs (contains_byte _ hi (by omega_using []))
    · exact out_scr dps' (contains_byte _ hi (by omega_using []))
    · exact out_scr dqs' (contains_byte _ hi (by omega_using []))
    · exact out_scr dqis (contains_byte _ hi (by omega_using []))
  · simp only [outsL, keyIn, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, forall_const, implies_true]
    exact ⟨⟨kApart_of dnd (by omega_using [wn]) (by omega_using [wn]), kApart_of dnp (by omega_using [wn]) (by omega_using []),
        kApart_of dnq (by omega_using [wn]) (by omega_using []), kApart_of dndp (by omega_using [wn]) (by omega_using []),
        kApart_of dndq (by omega_using [wn]) (by omega_using []), kApart_of dnqi (by omega_using [wn]) (by omega_using [])⟩,
      ⟨kApart_of ddp (by omega_using [wn]) (by omega_using []), kApart_of ddq (by omega_using [wn]) (by omega_using []),
        kApart_of dddp (by omega_using [wn]) (by omega_using []), kApart_of dddq (by omega_using [wn]) (by omega_using []),
        kApart_of ddqi (by omega_using [wn]) (by omega_using [])⟩,
      ⟨kApart_of dpq (by omega_using []) (by omega_using []), kApart_of dpdp (by omega_using []) (by omega_using []),
        kApart_of dpdq (by omega_using []) (by omega_using []), kApart_of dpqi (by omega_using []) (by omega_using [])⟩,
      ⟨kApart_of dqdp (by omega_using []) (by omega_using []), kApart_of dqdq (by omega_using []) (by omega_using []),
        kApart_of dqqi (by omega_using []) (by omega_using [])⟩,
      ⟨kApart_of dpdq' (by omega_using []) (by omega_using []), kApart_of dpqi' (by omega_using []) (by omega_using [])⟩,
      kApart_of dqqi' (by omega_using []) (by omega_using [])⟩

end VG.Proof.RsaKeyGen.AArch64.Key
