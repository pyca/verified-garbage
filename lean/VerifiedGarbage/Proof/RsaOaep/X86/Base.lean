module

public import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP on x86: what the proofs need of the hash functions

`OHash`: a hash function as RSAES-OAEP on x86 uses it, its streaming
functions verified (`Pbkdf2.Stream.X86.HashOK`), the hash function as RSA's
padding takes it, and the taint checks of the blocks whose immediates
depend on its digest's length (`OCerts`), evaluated once for each length
(at `dShape`, `OCerts.of_shape`); from the RSASSA-PSS one
(`OHash.ofPss`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86 VG.Impl.RsaOaep.X86
open VG.Impl.RsaPss.X86 (seqs)
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.RsaPss.X86 (TaintOk PssHash)

/-- A streaming hash function with digests of `D` bytes, and nothing else:
what the blocks `OCerts` checks read of one. -/
def dShape (D : Nat) : Hash := ⟨0, 0, D, 0, 0, "", .block [], "", .block [], "", .block []⟩

/-- The blocks whose immediates depend on the hash function: none writes
`esp` (`OCerts.sp`). -/
def spBlocks (H : Hash) : Prog isa :=
  seqs [.block (xorSet H), .block (mgfNext H), .block (dbArgs H 3), .block (dbArgs H 4), .block (seedArgs H 3),
    .block (seedArgs H 4), .block (encChk H), .block (seedSet H), .block (lhSet H), .block (decChk H),
    .block (cmpSet H), .block (scanSet H), .block (tSet H), .block (mlSet H)]

/-- The taint checks of the blocks whose immediates depend on the hash
function's digest length. -/
structure OCerts (H : Hash) : Prop where
  xorSet : TaintOk [.esp, .ebp] (.block (xorSet H))
  mgfNext : TaintOk [.esp, .ebp] (.block (mgfNext H))
  dbArgs3 : TaintOk [.esp, .ebp] (.block (dbArgs H 3))
  dbArgs4 : TaintOk [.esp, .ebp] (.block (dbArgs H 4))
  seedArgs3 : TaintOk [.esp, .ebp] (.block (seedArgs H 3))
  seedArgs4 : TaintOk [.esp, .ebp] (.block (seedArgs H 4))
  encChk : TaintOk [.esp] (.block (encChk H))
  seedSet : TaintOk [.esp, .ebp] (.block (seedSet H))
  lhSet : TaintOk [.esp, .ebp] (.block (lhSet H))
  decChk : TaintOk [.esp] (.block (decChk H))
  cmpSet : TaintOk [.esp, .ebp] (.block (cmpSet H))
  scanSet : TaintOk [.esp, .ebp] (.block (scanSet H))
  tSet : TaintOk [.esp, .ebp] (.block (tSet H))
  mlHead : TaintOk [.esp] (.block ((mlSet H).take 5))
  sp : NoSp (spBlocks H)

theorem OCerts.of_shape {H : Hash} (h : OCerts (dShape H.D)) : OCerts H :=
  ⟨h.xorSet, h.mgfNext, h.dbArgs3, h.dbArgs4, h.seedArgs3, h.seedArgs4, h.encChk, h.seedSet, h.lhSet, h.decChk,
    h.cmpSet, h.scanSet, h.tSet, h.mlHead, h.sp⟩

theorem noSp_seq_inv' {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp a ∧ NoSp b :=
  ⟨fun i hi => h i (List.mem_append_left _ hi), fun i hi => h i (List.mem_append_right _ hi)⟩

/-- The blocks `OCerts.sp` checks, one by one. -/
theorem OCerts.parts {H : Hash} (c : OCerts H) :
    NoSp (.block (VG.Impl.RsaOaep.X86.xorSet H) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.mgfNext H) : Prog isa) ∧
    NoSp (.block (VG.Impl.RsaOaep.X86.dbArgs H 3) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.dbArgs H 4) : Prog isa) ∧
    NoSp (.block (VG.Impl.RsaOaep.X86.seedArgs H 3) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.seedArgs H 4) : Prog isa) ∧
    NoSp (.block (VG.Impl.RsaOaep.X86.encChk H) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.seedSet H) : Prog isa) ∧
    NoSp (.block (VG.Impl.RsaOaep.X86.lhSet H) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.decChk H) : Prog isa) ∧
    NoSp (.block (VG.Impl.RsaOaep.X86.cmpSet H) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.scanSet H) : Prog isa) ∧
    NoSp (.block (VG.Impl.RsaOaep.X86.tSet H) : Prog isa) ∧ NoSp (.block (VG.Impl.RsaOaep.X86.mlSet H) : Prog isa) := by
  have s := c.sp
  simp only [spBlocks, seqs] at s
  obtain ⟨a1, s⟩ := noSp_seq_inv' s
  obtain ⟨a2, s⟩ := noSp_seq_inv' s
  obtain ⟨a3, s⟩ := noSp_seq_inv' s
  obtain ⟨a4, s⟩ := noSp_seq_inv' s
  obtain ⟨a5, s⟩ := noSp_seq_inv' s
  obtain ⟨a6, s⟩ := noSp_seq_inv' s
  obtain ⟨a7, s⟩ := noSp_seq_inv' s
  obtain ⟨a8, s⟩ := noSp_seq_inv' s
  obtain ⟨a9, s⟩ := noSp_seq_inv' s
  obtain ⟨a10, s⟩ := noSp_seq_inv' s
  obtain ⟨a11, s⟩ := noSp_seq_inv' s
  obtain ⟨a12, s⟩ := noSp_seq_inv' s
  obtain ⟨a13, a14⟩ := noSp_seq_inv' s
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

/-- A hash function, as RSAES-OAEP on x86 uses it. -/
structure OHash where
  H : Hash
  ok : Proof.Pbkdf2.Stream.X86.HashOK H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  glen : G.len = H.D
  valid : Proof.Mgf1.Valid G
  certs : OCerts H

namespace OHash

variable (g : OHash)

theorem D_pos : 0 < g.H.D := g.ok.hD0
theorem D_le : g.H.D ≤ 64 := by have := g.ok.hDF; have := g.ok.hF; omega
theorem DF : g.H.D ≤ g.H.F := g.ok.hDF
theorem F_le : g.H.F ≤ 64 := g.ok.hF
theorem S_le : g.H.S ≤ 256 := g.ok.hSB
theorem Wb_le : g.ok.Wb ≤ 512 := by have := g.ok.hWb; have := g.ok.hW; omega

/-- A byte of the mask, in the digest of `src ‖ C` for the counter `c`. -/
theorem mask_byte {seed : List Byte} {dl c i : Nat} (hi : i < dl) (h₁ : c * g.H.D ≤ i) (h₂ : i < c * g.H.D + g.H.D) :
    (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 = (g.ok.SH.H.hash (seed ++ Spec.Rsa.i2osp c 4)).getD (i - c * g.H.D) 0 := by
  have hD0 := g.D_pos
  rw [Proof.Mgf1.mgf1_getD g.valid _ hi, g.glen, ← g.hash]
  have e1 : i / g.H.D = c := Nat.div_eq_of_lt_le h₁ (by rw [Nat.succ_mul]; omega)
  have e2 : i % g.H.D = i - c * g.H.D := by
    have := Nat.mod_add_div i g.H.D
    rw [e1, Nat.mul_comm] at this
    omega
  rw [e1, e2]

end OHash

theorem offsO : Impl.RsaPss.X86.oCW = 0 ∧ Impl.RsaPss.X86.oSt = 512 ∧ oCtr = 768 ∧ Impl.RsaPss.X86.oDig = 832 ∧
    oLh = 896 ∧ Impl.RsaPss.X86.oEm = 1024 ∧ oBuf = 2048 ∧ Impl.RsaPss.X86.oRsa = 8192 ∧
    Impl.RsaPss.X86.frameBytes = 144 ∧ sSrc = 80 ∧ sSrcLen = 84 ∧ sDst = 88 ∧ sDstLen = 92 ∧ sRes = 96 ∧
    sOk = 100 ∧ Impl.RsaPss.X86.sCtr = 104 ∧ Impl.RsaPss.X86.sDone = 108 ∧ Impl.RsaPss.X86.sAcc = 112 ∧
    Impl.RsaPss.X86.sPos = 116 ∧ Impl.RsaPss.X86.sA = 120 ∧ Impl.RsaPss.X86.sD = 124 ∧
    Impl.RsaPss.X86.sPc = 128 ∧ Impl.RsaPss.X86.sVal = 140 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers. -/
macro "oomega" : tactic =>
  `(tactic| (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := offsO; omega))

end VG.Proof.RsaOaep.X86
