module

import VerifiedGarbage.Proof.Bignum.AArch64.MontFnBase
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.AArch64.MontFn
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontFnBase
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Bignum.AArch64.MontFn
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.Bignum.AArch64.MontFn
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Impl.Bignum
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.MontFn
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- The index in the low half of `r`. -/
abbrev idx (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_rsa_mont_mul(ws = x0, ws_len = x1, o = w2, a = w3, b = w4)`. -/
def fnContract : Contract isa where
  pre s :=
    let ws := s.gpr .x0
    let n := (s.gpr .x1).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧
      ws.toNat + n * 8 ≤ 2 ^ 64 ∧ Layout s.mem ws n ∧ Operand (idx s .x2) ∧ Operand (idx s .x3) ∧
      Operand (idx s .x4) ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat * (wordAt s.mem ws minvWord).toNat + 1) %
        2 ^ 64 = 0 ∧
      numAt s.mem ws w (idx s .x4) < numAt s.mem ws w aM
  post s s' :=
    let ws := s.gpr .x0
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt s'.mem ws w (idx s .x2) < M ∧
      numAt s'.mem ws w (idx s .x2) * 2 ^ (64 * w) % M = numAt s.mem ws w (idx s .x3) * numAt s.mem ws w (idx s .x4) % M ∧
      Keeps ws (s.gpr .x1).toNat w (idx s .x2) s.mem s'.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
      (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧ (s₁.gpr .x3).setWidth 32 = (s₂.gpr .x3).setWidth 32 ∧
      (s₁.gpr .x4).setWidth 32 = (s₂.gpr .x4).setWidth 32 ∧ wOf s₁.mem (s₁.gpr .x0) = wOf s₂.mem (s₂.gpr .x0)

/-- The words of a working space of `w = 2` at `0x1000`: the header, then the
modulus 1 in array 0 and zeros. -/
def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 512 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

/-- A state meeting `mulContract`: `w = 2`, the working space at `0x1000`, `o = a = b = 1`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 1 | .x3 => 1 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 512⟩]

theorem fn_implies : fnContract.Implies (Proof.Rsa.Mont.mulContract abi) where
  pre := by sig_implies_pre [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, fnContract, abi, argRegs]
  post := by sig_implies_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, fnContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hsp, hdi, hsi, hdx, hcx, h8, List.singleton_inj.mp hw⟩
  sat := by sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, fnContract, abi, argRegs] [satState] using satState

/-- The `k` words at offset `d` of `B` are the `8 k` bytes there. -/
theorem read_eq_wv (m : Mem) (B : Addr) (d : Nat) : ∀ k, (m.read (off B d) (8 * k)).toNat = wv m B d k
  | 0 => by simp [Mem.read, wv]
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Proof.Mont.read_toNat_add, read_eq_wv m B d k, wv,
      Offset.add_add, show 8 * (8 * k) = 64 * k by omega]
    congr 2

theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = wv m B (slot w j) w := by
  rw [← read_eq_wv]; rfl

theorem idx_eq (s : State) (r : Reg) : (s.gpr r).setWidth 32 = BitVec.ofNat 32 (idx s r) := by
  apply BitVec.eq_of_toNat_eq; simp [idx]

/-- What `fnContract.pre` gives the proofs: the working space, its header and the arguments. -/
theorem fn_good {s : State} (h : fnContract.pre s) :
    Scr s (s.gpr .x0) ((s.gpr .x1).toNat * 8) ∧
    Hdr s.mem (s.gpr .x0) (wOf s.mem (s.gpr .x0)) (wordAt s.mem (s.gpr .x0) minvWord) ∧
    slot (wOf s.mem (s.gpr .x0)) 8 ≤ (s.gpr .x1).toNat * 8 ∧ 2 ≤ wOf s.mem (s.gpr .x0) ∧
    wOf s.mem (s.gpr .x0) < 2 ^ 31 := by
  obtain ⟨-, hwr, hnw, ⟨h2, h31, h8, harr⟩, -⟩ := h
  refine ⟨Scr.of_mem (by rw [hwr]; simp) hnw, ⟨?_, rfl, fun j hj => harr j hj⟩, by
    simp only [slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at h8 ⊢; omega, h2, h31⟩
  simp [word, wOf, wordAt, Proof.Rsa.Mont.wWord, sW, off]


theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa mulBase s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨-, -, hnw, -, ⟨ho, ho2, ho3⟩, ⟨ha, ha2, ha3⟩, ⟨hb, hb2, hb3⟩, hinv, hB⟩ := h
  rw [numAt_eq, numAt_eq] at hB
  have hh := head_ok hs rfl hH hZ ho ha hb (idx_eq s .x2) (idx_eq s .x3) (idx_eq s .x4)
  have hp := montMul_from_bases_ok hs hZ hw hw' (by decide : 0 < 8) (by decide : 2 < 8)
    (by decide : 3 < 8) ho ha hb (by decide) (by decide) (Ne.symm ho2) (Ne.symm ha2)
    (Ne.symm hb2) (by decide) (Ne.symm ho3) hinv hB (.block basesR) hh
  obtain ⟨tr, t, he, hlt, heq, har, hk⟩ := hp
  refine ⟨tr, t, he, ⟨?_, hk.sp, hk.vcs⟩, ?_, ?_, ?_⟩
  · intro r hr
    exact hk.gpr r (by revert r; decide)
  · rw [numAt_eq, numAt_eq]; exact hlt
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    apply har
    intro j hj'
    rw [show ofs (s.gpr .x0) (s.gpr .x0 + BitVec.ofNat 64 i) = i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
    exact hj j hj'

structure FnData where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  a : Nat
  b : Nat

def FnPhi (d : FnData) (s : State) : Prop :=
  fnContract.pre s ∧ s.gpr .x0 = d.B ∧ (s.gpr .x1).toNat * 8 = d.Z ∧ wOf s.mem d.B = d.w ∧
    idx s .x2 = d.o ∧ idx s .x3 = d.a ∧ idx s .x4 = d.b

def FnBases (d : FnData) (t : State) : Prop :=
  BasesL 0 2 3 d.o d.a d.b ⟨d.B, d.Z, d.w⟩ t

theorem pins_fnBases : Pins FnBases [.x8, .x9, .x10, .x11, .x5, .x6, .x12, .x7] := by
  intro d s t hs ht
  exact pins_bases 0 2 3 d.o d.a d.b ⟨d.B, d.Z, d.w⟩ s t hs ht


theorem wp_conj {c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa c s P) (k : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨tr, t, he, hp⟩ := h
  obtain ⟨tr', t', he', hq⟩ := k
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact ⟨tr, t, he, hp, hq⟩

theorem zext_ok (s : State) :
    WP isa (.block zext) s fun t => t.gpr .x0 = s.gpr .x0 ∧
      t.gpr .x2 = ((s.gpr .x2).setWidth 32).setWidth 64 ∧
      t.gpr .x3 = ((s.gpr .x3).setWidth 32).setWidth 64 ∧
      t.gpr .x4 = ((s.gpr .x4).setWidth 32).setWidth 64 := by
  unfold zext
  brun [zext_exec]

def FnZext (d : FnData) (t : State) : Prop :=
  WP isa (.block basesTail) t (FnBases d) ∧ t.gpr .x0 = d.B ∧
    t.gpr .x2 = (BitVec.ofNat 32 d.o).setWidth 64 ∧
    t.gpr .x3 = (BitVec.ofNat 32 d.a).setWidth 64 ∧
    t.gpr .x4 = (BitVec.ofNat 32 d.b).setWidth 64

theorem pins_fnZext : Pins FnZext [.x0, .x2, .x3, .x4] := by
  rintro d s t ⟨_, h0, h2, h3, h4⟩ ⟨_, k0, k2, k3, k4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h0, k0]
  · rw [h2, k2]
  · rw [h3, k3]
  · rw [h4, k4]

theorem fn_rel : RelCT isa (Two FnPhi) mulBase fun _ _ => True := by
  unfold mulBase basesR
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := FnZext)
    (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)) fun d s h => ?_)
    (two_post (two_taint _ pins_fnZext (by taint_decide)) fun _ _ h => h.1)))
    (two_taint _ pins_fnBases (by taint_decide))
  obtain ⟨hp, h0, -, hw, ho, ha, hb⟩ := h
  obtain ⟨hs, hH, hZ, -, -⟩ := fn_good hp
  obtain ⟨-, -, -, -, ⟨ho8, -⟩, ⟨ha8, -⟩, ⟨hb8, -⟩, -⟩ := hp
  have hh := head_ok hs rfl hH hZ ho8 ha8 hb8 (idx_eq s .x2) (idx_eq s .x3) (idx_eq s .x4)
  rw [basesR, WP.block_append_iff] at hh
  refine WP.mono (wp_conj hh (zext_ok s)) fun t ⟨ht, k0, k2, k3, k4⟩ => ⟨WP.mono ht ?_, ?_, ?_, ?_, ?_⟩
  · rintro u ⟨⟨u8, u9, u10, u11, u5, u6, u12, -, u7, -⟩, -⟩
    obtain ⟨B, Z, w, o, a, b⟩ := d
    simp only at h0 hw ho ha hb ⊢
    subst h0 hw ho ha hb
    exact ⟨u8, u9, u10, u11, u5, u6, u12, u7⟩
  · rw [k0, h0]
  · rw [k2, idx_eq s .x2, ho]
  · rw [k3, idx_eq s .x3, ha]
  · rw [k4, idx_eq s .x4, hb]

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub mulBase :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h0, h1, h2, h3, h4, hw⟩ =>
    ⟨⟨s.gpr .x0, (s.gpr .x1).toNat * 8, wOf s.mem (s.gpr .x0), idx s .x2, idx s .x3, idx s .x4⟩,
      ⟨hs, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, by rw [h1], (congrArg (wOf t.mem) h0).trans hw.symm,
        by simp only [idx, h2], by simp only [idx, h3], by simp only [idx, h4]⟩, hsp⟩) fun _ _ h => h)

theorem fn_verified : Verified target mulBase (Proof.Rsa.Mont.mulContract abi) :=
  Verified.of_correct fn_correct fn_ct fn_implies

end VG.Proof.Bignum.AArch64.MontFn
