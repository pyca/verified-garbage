module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeSat
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Front
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.VettedPolicy

/-! # FFDH's context on x86-64: the arguments, the domain's recognition and the modulus check -/

@[expose] public section

/-! # FFDH's context on x86-64: the computation for a valid domain -/

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx)

/-- The precomputation's public data: the working space, the domain and the context. -/
structure PcP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  cp : Addr

abbrev PcP.w (p : PcP) : Nat := (p.k + 7) / 8
abbrev PcP.n (p : PcP) : Nat := 3 + 34 * p.w
abbrev PcP.a (p : PcP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom
abbrev PcP.bits (p : PcP) : Nat := Spec.Ffdh.generationScalarBits p.a
abbrev PcP.recog (p : PcP) : Nat := VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups p.k p.dom

/-- The outer header once the domain is checked: what `main` reads. -/
def PcP.headers (p : PcP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k),
    (sG, p.dp + BitVec.ofNat 64 p.k), (sQ, p.dp + BitVec.ofNat 64 (2 * p.k)), (sCtx, p.cp),
    (sRec, BitVec.ofNat 64 p.recog)]

structure MainPre (p : PcP) (s : State) : Prop where
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  doml : p.dom.length = p.dl
  hZ : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  rdi : s.gpr .rdi = p.B
  dom : Src s p.B p.Z p.dp p.dom
  ctx : CtxRegion s p.B p.Z p.cp p.n
  dsep : ∀ i < p.dl, 8 * p.n ≤ ofs p.cp (p.dp + BitVec.ofNat 64 i)
  hdr : VG.Proof.Ffdh.X86_64.Slots s.mem p.B p.headers
  valid : Spec.Ffdh.domainValid p.k p.dom = true

theorem PcP.headers_lt (p : PcP) : ∀ e ∈ p.headers, e.1 < 32 := by
  simp [PcP.headers, sDom, sDomLen, sK, sG, sQ, sCtx, sRec, sXe, sY, sFn]

/-- Memory outside the working space and the context is unchanged. -/
def PcP.Only (p : PcP) (m m' : Mem) : Prop := ∀ x, p.Z ≤ ofs p.B x → 8 * p.n ≤ ofs p.cp x → m' x = m x

theorem PcP.Only.trans {p : PcP} {m₁ m₂ m₃ : Mem} (h₁ : p.Only m₁ m₂) (h₂ : p.Only m₂ m₃) : p.Only m₁ m₃ :=
  fun x hx hc => (h₂ x hx hc).trans (h₁ x hx hc)

/-- What the width stage leaves. -/
structure FrontPost (p : PcP) (s t : State) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 p.bits
  w0 : word t.mem p.cp 0 = BitVec.ofNat 64 p.bits
  w1 : word t.mem p.cp 8 = BitVec.ofNat 64 ((p.bits + 7) / 8)
  w2 : word t.mem p.cp 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits)
  rowsH : word t.mem p.B (8 * sRows) = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits)
  rows : ∀ j, 3 + p.w * (j + 1) ≤ p.n → row t.mem p.cp p.w j = row s.mem p.cp p.w j
  hdr : VG.Proof.Ffdh.X86_64.Slots t.mem p.B p.headers
  saved : ∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)
  only : p.Only s.mem t.mem
  keep : Keep mmRegs s t

theorem MainPre.modValid {p : PcP} {s : State} (h : MainPre p s) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (p.dom.take p.k)) p.k = true :=
  VG.Proof.Ffdh.domainValid_mod h.valid

theorem bitLength_mono {a b : Nat} (h : a ≤ b) : Spec.RsaKeyGen.bitLength a ≤ Spec.RsaKeyGen.bitLength b := by
  unfold Spec.RsaKeyGen.bitLength
  by_cases ha : a = 0
  · simp only [ha, ite_true]; exact Nat.zero_le _
  · have hb : b ≠ 0 := by omega
    simp only [ha, hb, ite_false]
    have := (Nat.le_log2 hb).mpr (Nat.le_trans (Nat.log2_self_le ha) h)
    omega

/-- The scalar width is at most p's bit length. -/
theorem MainPre.bits_le {p : PcP} {s : State} (h : MainPre p s) : p.bits ≤ 8192 := by
  dsimp only [PcP.bits, PcP.a]
  have hv := (VG.Proof.Ffdh.domainValid_iff p.k p.dom).mp h.valid
  have hb := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (Spec.Ffdh.domainOf p.k p.dom)
  have hpv := h.valid
  unfold Spec.Ffdh.domainValid Spec.Ffdh.parametersValid at hpv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpv
  have hp8 : Spec.RsaKeyGen.bitLength (Spec.Ffdh.domainOf p.k p.dom).p ≤ 8192 := hpv.1.1.1.1.1.2
  have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) ≤ (Spec.Ffdh.domainOf p.k p.dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf p.k p.dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega
  have := bitLength_mono hle
  omega

theorem slots_of {p : PcP} {m : Mem} (h : VG.Proof.Ffdh.X86_64.Slots m p.B p.headers) :
    word m p.B (8 * sDom) = p.dp ∧ word m p.B (8 * sDomLen) = BitVec.ofNat 64 p.dl ∧
    word m p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ word m p.B (8 * sG) = p.dp + BitVec.ofNat 64 p.k ∧
    word m p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧ word m p.B (8 * sCtx) = p.cp ∧
    word m p.B (8 * sRec) = BitVec.ofNat 64 p.recog :=
  ⟨h (sDom, p.dp) (by simp [PcP.headers]), h (sDomLen, BitVec.ofNat 64 p.dl) (by simp [PcP.headers]),
    h (sK, BitVec.ofNat 64 p.k) (by simp [PcP.headers]),
    h (sG, p.dp + BitVec.ofNat 64 p.k) (by simp [PcP.headers]),
    h (sQ, p.dp + BitVec.ofNat 64 (2 * p.k)) (by simp [PcP.headers]),
    h (sCtx, p.cp) (by simp [PcP.headers]), h (sRec, BitVec.ofNat 64 p.recog) (by simp [PcP.headers])⟩

theorem MainPre.slots {p : PcP} {s : State} (h : MainPre p s) :
    word s.mem p.B (8 * sDom) = p.dp ∧ word s.mem p.B (8 * sDomLen) = BitVec.ofNat 64 p.dl ∧
    word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ word s.mem p.B (8 * sG) = p.dp + BitVec.ofNat 64 p.k ∧
    word s.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧ word s.mem p.B (8 * sCtx) = p.cp ∧
    word s.mem p.B (8 * sRec) = BitVec.ofNat 64 p.recog :=
  ⟨h.hdr (sDom, p.dp) (by simp [PcP.headers]), h.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [PcP.headers]),
    h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [PcP.headers]),
    h.hdr (sG, p.dp + BitVec.ofNat 64 p.k) (by simp [PcP.headers]),
    h.hdr (sQ, p.dp + BitVec.ofNat 64 (2 * p.k)) (by simp [PcP.headers]),
    h.hdr (sCtx, p.cp) (by simp [PcP.headers]), h.hdr (sRec, BitVec.ofNat 64 p.recog) (by simp [PcP.headers])⟩

theorem recognize_lt (k : Nat) (dom : List Byte) :
    VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom < 2 ^ 32 := by
  have aux : ∀ gs : List VG.Impl.Ffdh.VettedGroups.Group, (∀ g ∈ gs, g.bits < 2 ^ 32) →
      VG.Impl.Ffdh.VettedGroups.recognizeList gs k dom < 2 ^ 32 := by
    intro gs
    induction gs with
    | nil => intro _; simp [VG.Impl.Ffdh.VettedGroups.recognizeList]
    | cons g gs ih =>
      intro hg
      simp only [VG.Impl.Ffdh.VettedGroups.recognizeList]
      split
      · exact hg g (by simp)
      · exact ih (fun x hx => hg x (by simp [hx]))
  exact aux _ (by decide)

/-- Three words at the context's start. -/
theorem ctx3 (m : Mem) (cp : Addr) (a b c : BitVec 64) :
    let m' := ((m.writeW (off cp 0) a).writeW (off cp 8) b).writeW (off cp 16) c
    word m' cp 0 = a ∧ word m' cp 8 = b ∧ word m' cp 16 = c ∧ Outside cp 0 24 m m' := by
  intro m'
  have o1 := writeW_outside m cp (d := 0) a (by decide)
  have o2 := writeW_outside (m.writeW (off cp 0) a) cp (d := 8) b (by decide)
  have o3 := writeW_outside ((m.writeW (off cp 0) a).writeW (off cp 8) b) cp (d := 16) c (by decide)
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · rw [o3.word (by decide) (by decide), o2.word (by decide) (by decide)]; exact word_writeW_self _ _ _ _
  · rw [o3.word (by decide) (by decide)]; exact word_writeW_self _ _ _ _
  · exact ((o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))).trans
      (o3.mono (by decide) (by decide))

/-- A word of the working space is unchanged by a change of the context's first `n` bytes. -/
theorem scrWord_of_ctx {p : PcP} {s : State} (h : MainPre p s) {m m' : Mem} {n : Nat} (hm : Outside p.cp 0 n m m')
    (hn : n ≤ 8 * p.n) {d : Nat} (hd : d + 8 ≤ p.Z) : word m' p.B d = word m p.B d :=
  Mem.readW_congr fun i hi => hm _ (Or.inr (by
    have hn' := h.scr.nowrap
    have := h.ctx.apart (x := off p.B d + BitVec.ofNat 64 i) (by rw [ofs_off p.B (by omega)]; omega)
    omega))

/-- A row is unchanged by a change inside the working space. -/
theorem row_of_scr {p : PcP} {s : State} (h : MainPre p s) {m m' : Mem} (hm : InScr p.B p.Z m m') {j : Nat}
    (hj : 3 + p.w * (j + 1) ≤ p.n) : row m' p.cp p.w j = row m p.cp p.w j :=
  row_congr fun i hi => Mem.readW_congr fun b hb => hm _ (by
    have e : off p.cp (24 + 8 * p.w * j + 8 * i) + BitVec.ofNat 64 b = off p.cp (24 + 8 * p.w * j + 8 * i + b) := by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    have e8 : 8 * p.w * j = 8 * (p.w * j) := Nat.mul_assoc _ _ _
    exact h.ctx.out (by rw [Nat.mul_add] at hj; omega))

/-- The bound's first significant byte is not zero. -/
theorem MainPre.lead_ne {p : PcP} {s : State} (h : MainPre p s) (hne : VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom ≠ []) :
    (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'
      (VG.Proof.Ffdh.lead_lt hne) ≠ 0 := by
  have hk1 := h.k1
  have hl := h.doml
  have hmv := h.modValid
  obtain ⟨hodd, h1p, hnorm⟩ := valid_facts hmv hk1
  have size : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k := by rw [hl]; exact h.dl
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hld := VG.Proof.Ffdh.lead_lt hne
  rw [hbl] at hld
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := p.k) (dom := p.dom) (by omega) size
    (fun _ => ⟨hodd, h1p⟩)
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) := by
    have hv := (VG.Proof.Ffdh.domainValid_iff p.k p.dom).mp h.valid
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf p.k p.dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  show (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'
      (VG.Proof.Ffdh.lead_lt hne) ≠ 0
  intro hb0
  by_cases hlast : VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom) + 1 <
      (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom).length
  · exact VG.Proof.Ffdh.lead_nonzero hne hlast hb0
  · rw [hb0] at hbits
    have : Spec.RsaKeyGen.bitLength (0 : Byte).toNat = 0 := rfl
    rw [this] at hbits
    have hpos := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) ≠ 0 by omega)).2
    rw [hbits] at hpos
    rw [hbl] at hlast
    have : p.k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom) - 1 = 0 := by omega
    rw [this] at hpos
    omega

theorem front_ok {p : PcP} {s : State} (h : MainPre p s) :
    WP isa (seqs (GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata)])) s
      (FrontPost p s) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.hZ
  have hl := h.doml
  have hdl : p.dl < 2 ^ 32 := by rcases h.dl with e | e <;> omega
  have hmv := h.modValid
  obtain ⟨hodd, h1p, hnorm⟩ := valid_facts hmv hk1
  have size : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k := by rw [hl]; exact h.dl
  obtain ⟨hDom, hDl, hK, hG, hQ, hCtx, hRec⟩ := h.slots
  refine wp_seqs_append (a := GenerateKey.bound) (by simp [GenerateKey.bound]) (by simp)
    (WP.mono (VG.Proof.Ffdh.X86_64.GenerateKey.bound_ok h.scr h.rdi (by omega) (by omega) (by omega) h.dl hl
      hDom hQ hK hDl h.dom)
      fun s₁ ⟨hne, hEp₁, hEl₁, hax₁, hf₁, k₁⟩ => ?_)
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hld := VG.Proof.Ffdh.lead_lt hne
  rw [hbl] at hld
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := p.k) (dom := p.dom) (by omega) size
    (fun _ => ⟨hodd, h1p⟩)
  have hbz := h.lead_ne hne
  simp only [seqs]
  refine WP.seq (WP.mono (byteBits_ok hbz hax₁) fun s₂ ⟨hcx₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ : Scr s₂ p.B p.Z := h.scr.congr k12.2.2
  have hdi₂ : s₂.gpr .rdi = p.B := (k12.gpr (by decide)).trans h.rdi
  have hfw : ∀ i < 32, i ≠ sEp → i ≠ sEl → word s₂.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 => by
    rw [hm₂]; exact hf₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sEp sEl sFn at * <;> omega) (by omega)
  have hEl₂ : word s₂.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)) := by
    rw [hm₂]; exact hEl₁
  have hRec₂ : word s₂.mem p.B (8 * sRec) = BitVec.ofNat 64 p.recog := by
    rw [hfw _ (by decide) (by decide) (by decide)]; exact hRec
  have hc8 : Spec.RsaKeyGen.bitLength ((VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead
      (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'(VG.Proof.Ffdh.lead_lt hne)).toNat ≤ 8 := by
    have hb0 : ((VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead
        (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'(VG.Proof.Ffdh.lead_lt hne)).toNat ≠ 0 :=
      fun e => hbz (BitVec.eq_of_toNat_eq e)
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hb0).1
    have hlt := ((VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead
        (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'(VG.Proof.Ffdh.lead_lt hne)).isLt
    by_contra hc
    have : 2 ^ 8 ≤ 2 ^ (Spec.RsaKeyGen.bitLength ((VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead
        (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'(VG.Proof.Ffdh.lead_lt hne)).toNat - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpick : pick p.recog (8 * (p.k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)) - 8 +
      Spec.RsaKeyGen.bitLength ((VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead
        (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'(VG.Proof.Ffdh.lead_lt hne)).toNat) = p.bits := by
    show _ = Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)
    rw [← pick_spec (by omega) size hnorm, hbits]
    congr 1
    omega
  rw [WP.block_append_iff]
  refine WP.mono (width_only (cp := p.cp) hs₂ hdi₂ (by omega) hcx₂ hc8 hEl₂ (by omega) (by omega) hRec₂ (recognize_lt _ _)
    (by rw [hfw _ (by decide) (by decide) (by decide)]; exact hCtx))
    fun s₃ ⟨hax₃, hsi₃, hm₃, k₃⟩ => ?_
  rw [hpick] at hax₃
  have k13 := k12.trans k₃
  have hcw : ∀ i < 3, InRegions s₃.wr (off p.cp (8 * i)) 8 := fun i hi => by
    rw [k13.2.2]; exact h.ctx.wr i (by unfold PcP.n; omega)
  refine WP.mono (metadata_ok (hs₂.congr k₃.2.2) ((k₃.gpr (by decide)).trans hdi₂) (by omega) hax₃ h.bits_le
    hsi₃ hcw) fun t ⟨hmt, kt⟩ => ?_
  have hn := h.scr.nowrap
  obtain ⟨c0, c1, c2, co⟩ := ctx3 ((s₃.mem.writeW (off p.B (8 * sBits)) (BitVec.ofNat 64 p.bits)).writeW
    (off p.B (8 * sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits))) p.cp (BitVec.ofNat 64 p.bits)
    (BitVec.ofNat 64 ((p.bits + 7) / 8)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits))
  rw [← hmt] at c0 c1 c2 co
  have oB := writeW_outside s₃.mem p.B (d := 8 * sBits) (BitVec.ofNat 64 p.bits) (by decide)
  have oR := writeW_outside (s₃.mem.writeW (off p.B (8 * sBits)) (BitVec.ofNat 64 p.bits)) p.B (d := 8 * sRows)
    (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits)) (by decide)
  have hn24 : 24 ≤ 8 * p.n := by unfold PcP.n; omega
  -- The words of the working space but the four slots.
  have hw : ∀ i < 32, i ≠ sEp → i ≠ sEl → i ≠ sBits → i ≠ sRows → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi h1 h2 h3 h4 => by
      rw [scrWord_of_ctx h co hn24 (by omega), oR.word (by unfold sRows VG.Impl.Ffdh.X86_64.Domain.sOut sFn at *; omega) (by omega),
        oB.word (by unfold sBits VG.Impl.Ffdh.X86_64.Domain.sXl sFn at *; omega) (by omega), hm₃, hfw i hi h1 h2]
  have hin : InScr p.B p.Z s.mem ((s₃.mem.writeW (off p.B (8 * sBits)) (BitVec.ofNat 64 p.bits)).writeW
      (off p.B (8 * sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits))) := fun x hx => by
    rw [oR x (Or.inr (by unfold sRows VG.Impl.Ffdh.X86_64.Domain.sOut sFn; omega)), oB x (Or.inr (by unfold sBits VG.Impl.Ffdh.X86_64.Domain.sXl sFn; omega)),
      hm₃, hm₂, hf₁ x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> unfold sEp sEl sFn at * <;> omega)]
  refine ⟨(kt.gpr (by decide)).trans hax₃, c0, c1, c2, ?_, fun j hj => ?_, fun e he => ?_, fun i hi => ?_,
    fun x hx hc => ?_, (k13.trans kt).mono (by decide)⟩
  · rw [scrWord_of_ctx h co hn24 (by unfold sRows VG.Impl.Ffdh.X86_64.Domain.sOut sFn; omega)]; exact word_writeW_self _ _ _ _
  · rw [row_outside co (Or.inr (by omega)) (by
      have := h.ctx.nowrap; unfold PcP.n at hj this; have e8 : 8 * p.w * (j + 1) = 8 * (p.w * (j + 1)) := Nat.mul_assoc _ _ _
      omega)]
    exact row_of_scr h hin hj
  · rw [hw e.1 (p.headers_lt e he) ?_ ?_ ?_ ?_]
    · exact h.hdr e he
    all_goals simp only [PcP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    all_goals rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · exact hw i (by omega) (by unfold sEp sFn; omega) (by unfold sEl sFn; omega)
      (by unfold sBits VG.Impl.Ffdh.X86_64.Domain.sXl sFn; omega) (by unfold sRows VG.Impl.Ffdh.X86_64.Domain.sOut sFn; omega)
  · rw [co x (Or.inr (by omega))]
    exact hin x hx

/-- The context's pointer and row count into the inner header. -/
theorem envBlock_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} {cp : Addr} {rows : Nat}
    (hc : ModCtx s B Z o w mi P) (hCtx : word s.mem B (8 * sCtx) = cp)
    (hRows : word s.mem B (8 * sRows) = BitVec.ofNat 64 rows) :
    WP isa (.block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)) s fun t => ModCtx t B Z o w mi P ∧
      word t.mem (off B o) (8 * iCtx) = cp ∧ word t.mem (off B o) (8 * iRows) = BitVec.ofNat 64 rows ∧
      Frm (off B o) [(8 * iCtx, 8), (8 * iRows, 8)] s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  have hg := hc.sub.good
  have hn := hc.sub.scr.nowrap
  have hL := hdr_lt_slot w 8 (show Crt.sLink < 32 by decide)
  have hC := hdr_lt_slot w 8 (show iCtx < 32 by decide)
  have hR := hdr_lt_slot w 8 (show iRows < 32 by decide)
  have hoC : 8 * sCtx + 8 ≤ Z := by have := hc.sub.lo; have := hc.sub.hi; unfold sCtx sXe sFn; unfold slot hdrBytes at *; omega
  have hoR : 8 * sRows + 8 ≤ Z := by
    have := hc.sub.lo; have := hc.sub.hi; unfold sRows VG.Impl.Ffdh.X86_64.Domain.sOut sFn; unfold slot hdrBytes at *; omega
  have hlo := hc.sub.lo
  have hhi := hc.sub.hi
  have o1 := writeW_outside s.mem (off B o) (d := 8 * iCtx) cp (by decide)
  have f1 : Frm (off B o) [(8 * iCtx, 8)] s.mem (s.mem.writeW (off (off B o) (8 * iCtx)) cp) :=
    Frm.of_outside o1 (by simp)
  have hRows' : (s.mem.writeW (off (off B o) (8 * iCtx)) cp).readW (off B (8 * sRows)) 64 = BitVec.ofNat 64 rows := by
    change word _ B (8 * sRows) = _
    rw [f1.word_below (L := slot w 8) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hC) (by omega) (by omega)
      (by have := hdr_lt_slot w 0 (show sRows < 32 by decide); unfold slot hdrBytes at *; omega)]
    exact hRows
  have hLink' : (s.mem.writeW (off (off B o) (8 * iCtx)) cp).readW (off (off B o) (8 * Crt.sLink)) 64 = B := by
    change word _ (off B o) (8 * Crt.sLink) = _
    rw [o1.word (by decide) (by omega)]; exact hc.sub.link
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.mem = (s.mem.writeW (off (off B o) (8 * iCtx)) cp).writeW (off (off B o) (8 * iRows)) (BitVec.ofNat 64 rows)) (by
    unfold fromOuter
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hg.scr.ld (d := 8 * Crt.sLink) hL, hc.sub.link,
      hc.sub.scr.ld (d := 8 * sCtx) hoC, hCtx, hg.scr.st (d := 8 * iCtx) hC, hLink',
      hc.sub.scr.ld (d := 8 * sRows) hoR, hRows', hg.scr.st (d := 8 * iRows) hR]) rfl) fun t ⟨hm, k⟩ => ?_
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * iCtx)) cp) (off B o) (d := 8 * iRows)
    (BitVec.ofNat 64 rows) (by decide)
  rw [← hm] at o2
  have f : Frm (off B o) [(8 * iCtx, 8), (8 * iRows, 8)] s.mem t.mem :=
    (f1.mono (by simp)).trans (Frm.of_outside o2 (by simp))
  refine ⟨hc.of_inner (Frm.cover f (fun r hr => ⟨(8 * 17, 8 * 15), by simp [innerR], by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide⟩))
    k.2.2 (k.gpr (by decide)), ?_, by rw [hm]; exact word_writeW_self _ _ _ _, f, k⟩
  rw [hm, (writeW_outside (s.mem.writeW (off (off B o) (8 * iCtx)) cp) (off B o) (d := 8 * iRows)
    (BitVec.ofNat 64 rows) (by decide)).word (by decide) (by omega)]
  exact word_writeW_self _ _ _ _

theorem MainPre.bound_two {p : PcP} {s : State} (h : MainPre p s) :
    2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) := by
  have hv := (VG.Proof.Ffdh.domainValid_iff p.k p.dom).mp h.valid
  unfold Spec.Ffdh.scalarBound
  cases hq : (Spec.Ffdh.domainOf p.k p.dom).q with
  | none => simp only [Option.getD_none]; omega
  | some q => have := (hv.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega

theorem MainPre.bits_pos {p : PcP} {s : State} (h : MainPre p s) : 1 ≤ p.bits := by
  have hbnd := h.bound_two
  have hbl : 1 ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom)) := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) ≠ 0 by omega)).2
    by_contra hc
    have e : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom)) = 0 := by omega
    rw [e] at this; omega
  dsimp only [PcP.bits, PcP.a]
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) with
  | none => simpa using hbl
  | some b => have := recognized_nonzero he; simp only; omega

/-- Bytes outside the working space and the context keep their values. -/
theorem Src.of_pcOnly {p : PcP} {s t : State} {q : Addr} {bs : List Byte} (h : Src s p.B p.Z q bs)
    (hm : p.Only s.mem t.mem) (hsep : ∀ i < bs.length, 8 * p.n ≤ ofs p.cp (q + BitVec.ofNat 64 i))
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t p.B p.Z q bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi,
    fun i hi => by rw [hm _ (h.out i hi) (hsep i hi)]; exact h.val i hi, h.out⟩

/-- The table stage's parameters. -/
abbrev PcP.T (p : PcP) (mi : BitVec 64) : TabP :=
  ⟨p.B, p.Z, VG.Proof.Ffdh.X86_64.inner p.w, p.w, mi, p.cp, Spec.Rsa.os2ip (p.dom.take p.k),
    Spec.Rsa.os2ip ((p.dom.drop p.k).take p.k), p.bits⟩

/-- The workspace for p, `R² mod p`, the context's prefix and table, and 1 returned. -/
theorem inner_ok (Mo : Mont) (R : R2Impl Mo) {p : PcP} {s₀ s : State} (h : MainPre p s₀)
    (hf : FrontPost p s₀ s) :
    WP isa (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
      (([.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] : List (Prog isa)) ++
        (Precompute.storePrefix ++ (Precompute.table Mo.mm ++ ([.block [Crt.leave, .mov32 .rax (.imm 1)]] : List (Prog isa))))))) s
      fun t => t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rdi = p.B ∧
        Spec.Rsa.wordsAt t.mem p.cp p.n = VG.Proof.Ffdh.generationValues p.k p.dom ∧
        (∀ i < 6, word t.mem p.B (8 * i) = word s₀.mem p.B (8 * i)) ∧ p.Only s₀.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.hZ
  have hn := h.scr.nowrap
  have hmv := h.modValid
  obtain ⟨hodd, h1p, hnorm⟩ := valid_facts hmv hk1
  have hroom := VG.Proof.Ffdh.X86_64.room_k hk1 hZ
  obtain ⟨hDom, hDl, hK, hG, hQ, hCtx, hRec⟩ := slots_of hf.hdr
  have hsrc : Src s p.B p.Z p.dp p.dom := Src.of_pcOnly h.dom hf.only
    (fun i hi => h.dsep i (by rw [← h.doml]; exact hi)) hf.keep.2.1 hf.keep.2.2
  have hs : Scr s p.B p.Z := h.scr.congr hf.keep.2.2
  have h0 : s.gpr .rdi = p.B := (hf.keep.gpr (by decide)).trans h.rdi
  have hpl : (p.dom.take p.k).length = p.k := by
    simp only [List.length_take, h.doml]; rcases h.dl with e | e <;> omega
  refine wp_seqs_append (by simp [pSetup]) (by simp) (WP.mono (VG.Proof.Ffdh.X86_64.setup_ok hs h0 hk1 hk2 hZ
    hDom hK (hsrc.take p.k) hpl hodd)
    fun s₁ ⟨mi, hc₁, hv₁, hWs₁, hf₁, k₁⟩ => ?_)
  have hsR : ∀ r ∈ VG.Proof.Ffdh.X86_64.setupR p.w, r.1 + r.2 ≤ p.Z := by
    intro r hr
    simp only [VG.Proof.Ffdh.X86_64.setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · show 8 * 6 + 8 ≤ p.Z; omega
    · show 8 * 8 + 64 ≤ p.Z; omega
    · show 8 * 29 + 8 ≤ p.Z; omega
    · show VG.Proof.Ffdh.X86_64.inner ((p.k + 7) / 8) + slot ((p.k + 7) / 8) 8 ≤ p.Z
      have := Nat.le_add_right (VG.Proof.Ffdh.X86_64.inner ((p.k + 7) / 8) + slot ((p.k + 7) / 8) 8)
        (tabBytes ((p.k + 7) / 8) 32)
      omega
  have hin₁ : InScr p.B p.Z s.mem s₁.mem := InScr.of_frm hf₁ hsR
  have hb₁ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₁.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 =>
    hf₁.word_eq (fun r hr => by
      simp only [VG.Proof.Ffdh.X86_64.setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;>
        unfold sW sWs sArr sFn VG.Proof.Ffdh.X86_64.inner slot hdrBytes at * <;> omega) (by omega)
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (VG.Proof.Ffdh.X86_64.r2_ctx Mo R hc₁ hv₁ hmv hk1 hk2 hZ)
    fun s₂ ⟨hm₂, hf₂, k₂⟩ => ?_)
  obtain ⟨hb₂, hin₂⟩ := VG.Proof.Ffdh.X86_64.child_frm hc₁ hm₂.wide hf₂
    (fun r hr => Nat.le_trans (r2Ranges_le p.w r hr) (Nat.le_add_right _ _))
  have hCtx₂ : word s₂.mem p.B (8 * sCtx) = p.cp := by
    rw [hb₂ _ (by decide), hb₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hCtx
  have hRows₂ : word s₂.mem p.B (8 * sRows) = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits) := by
    rw [hb₂ _ (by decide), hb₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hf.rowsH
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp [Precompute.storePrefix]) (WP.mono (envBlock_ok hm₂ hCtx₂ hRows₂)
    fun s₃ ⟨hm₃, hC₃, hR₃, hf₃, k₃⟩ => ?_)
  obtain ⟨hb₃, hin₃⟩ := VG.Proof.Ffdh.X86_64.child_frm hm₂.sub hm₂.wide hf₃
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Nat.le_trans (hdr_lt_slot p.w 8 (show iCtx < 32 by decide)) (Nat.le_add_right _ _)
      · exact Nat.le_trans (hdr_lt_slot p.w 8 (show iRows < 32 by decide)) (Nat.le_add_right _ _))
  have k13 := (k₁.trans k₂).trans k₃
  have he₃ : Env (p.T mi) s₃ := ⟨hm₃, hC₃, hR₃, h.ctx.congr (by rw [k13.2.1, hf.keep.2.1]) (by rw [k13.2.2, hf.keep.2.2])⟩
  have hin₁₃ : InScr p.B p.Z s.mem s₃.mem := (hin₁.trans hin₂).trans hin₃
  have hout₁₃ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 => by
    rw [hb₃ i hi, hb₂ i hi, hb₁ i hi h1 h2 h3]
  -- `p` and `R² mod p` to rows 0 and 1.
  unfold Precompute.storePrefix
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 0 ∧
      t.mem = s₃.mem) (by xrun [show BitVec.setWidth 64 (0 : BitVec 32) = BitVec.ofNat 64 0 from rfl]) rfl)
    fun s₄ ⟨⟨hax₄, hm₄⟩, k₄⟩ => ?_)
  have he₄ := he₃.of_outScr (by intro x _; rw [hm₄]) k₄.2.1 k₄.2.2 (k₄.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (store_env he₄ hax₄ (show aN < 8 by decide) (by decide))
    fun s₅ ⟨he₅, hrow₅, hr₅, hos₅, kp₅, k₅⟩ => ?_)
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 1 ∧
      t.mem = s₅.mem) (by xrun [show BitVec.setWidth 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl]) rfl)
    fun s₆ ⟨⟨hax₆, hm₆⟩, k₆⟩ => ?_)
  have he₆ := he₅.of_outScr (by intro x _; rw [hm₆]) k₆.2.1 k₆.2.2 (k₆.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (store_env he₆ hax₆ (show aR2 < 8 by decide) (by decide))
    fun s₇ ⟨he₇, hrow₇, hr₇, hos₇, kp₇, k₇⟩ => ?_)
  have kp₃₇ : Kept (p.T mi) s₃ s₇ := ((Kept.of_eq hm₄).trans kp₅).trans ((Kept.of_eq hm₆).trans kp₇)
  have hgl : ((p.dom.drop p.k).take p.k).length = p.k := by
    simp only [List.length_take, List.length_drop, h.doml]; rcases h.dl with e | e <;> omega
  have honly : p.Only s.mem s₇.mem := fun x hx hc => (kp₃₇.only x hx hc).trans (hin₁₃ x hx)
  have hsrcG : Src s₇ p.B p.Z (p.dp + BitVec.ofNat 64 p.k) ((p.dom.drop p.k).take p.k) :=
    Src.of_pcOnly ((hsrc.drop p.k).take p.k) honly (fun i hi => by
      rw [hgl] at hi
      have := h.dsep (p.k + i) (by rcases h.dl with e | e <;> omega)
      rwa [BitVec.add_assoc, BitVec.ofNat_add_ofNat])
      (by rw [k₇.2.1, k₆.2.1, k₅.2.1, k₄.2.1, k13.2.1]) (by rw [k₇.2.2, k₆.2.2, k₅.2.2, k₄.2.2, k13.2.2])
  have hrows1 : 1 ≤ (p.T mi).rows := by
    have := h.bits_pos
    show 1 ≤ Spec.Rsa.FixedBaseComb.rows p.bits
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth; omega
  have hrows2 : (p.T mi).rows < 2 ^ 63 := by
    have := h.bits_le
    show Spec.Rsa.FixedBaseComb.rows p.bits < 2 ^ 63
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth; omega
  refine wp_seqs_append (a := Precompute.table Mo.mm) (by simp [Precompute.table, Precompute.initial]) (by simp)
    (WP.mono (table_ok Mo he₇ hrows1 hrows2 rfl
      ((kp₃₇.outer sG (by decide)).trans ((hout₁₃ _ (by decide) (by decide) (by decide) (by decide)).trans hG))
      ((kp₃₇.outer sK (by decide)).trans ((hout₁₃ _ (by decide) (by decide) (by decide) (by decide)).trans
        (by rw [hgl]; exact hK)))
      hsrcG (fun i hi => by
        rw [hgl] at hi
        have := h.dsep (p.k + i) (by rcases h.dl with e | e <;> omega)
        rwa [BitVec.add_assoc, BitVec.ofNat_add_ofNat]) (by omega) (by rw [hgl]))
    fun s₈ ⟨he₈, hE₈, hp₈, kp₈, k₈⟩ => ?_)
  have hs₈ := he₈.mc.sub
  change WP isa (.block [Crt.leave, .mov32 .rax (.imm 1)]) s₈ _
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = BitVec.ofNat 64 1 ∧
      t.mem = s₈.mem) (by
    xrun [State.ea, hdr, Crt.leave, hs₈.rdi, hdrOff, hs₈.good.scr.ld (d := 8 * Crt.sLink)
      (hdr_lt_slot _ 8 (by decide)), hs₈.link, show BitVec.setWidth 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl])
    rfl) fun t ⟨⟨hdt, hat, hmt⟩, kt⟩ => ?_
  have hc3 : ∀ i < 3, word s₃.mem p.cp (8 * i) = word s.mem p.cp (8 * i) := fun i hi =>
    Mem.readW_congr fun b hb => hin₁₃ _ (by
      have e : off p.cp (8 * i) + BitVec.ofNat 64 b = off p.cp (8 * i + b) := by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [e]; exact h.ctx.out (by unfold PcP.n; omega))
  have hcw : ∀ i < 3, word t.mem p.cp (8 * i) = word s.mem p.cp (8 * i) := fun i hi => by
    rw [hmt]; exact (kp₈.hdr i hi).trans ((kp₃₇.hdr i hi).trans (hc3 i hi))
  have hR2 : wv s₆.mem (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (slot p.w aR2) p.w =
      2 ^ (128 * p.w) % Spec.Rsa.os2ip (p.dom.take p.k) := by
    have l := he₆.mc.r2l
    have r := he₆.mc.r2
    rw [← Nat.mod_eq_of_lt l, r, ← Nat.pow_add, show 64 * p.w + 64 * p.w = 128 * p.w by omega]
  refine ⟨hat, hdt, ?_, fun i hi => ?_, fun x hx hc => ?_, ?_⟩
  · rw [ctx_words (h₀ := BitVec.ofNat 64 p.bits) (h₁ := BitVec.ofNat 64 ((p.bits + 7) / 8))
      (h₂ := BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits))
      (r₀ := Spec.Rsa.toWords (Spec.Rsa.os2ip (p.dom.take p.k)) p.w)
      (r₁ := Spec.Rsa.toWords (2 ^ (128 * p.w) % Spec.Rsa.os2ip (p.dom.take p.k)) p.w)
      (ent := fun a => Spec.Rsa.toWords ((p.T mi).entry a) p.w)
      ((hcw 0 (by decide)).trans hf.w0) ((hcw 1 (by decide)).trans hf.w1) ((hcw 2 (by decide)).trans hf.w2)
      ?_ ?_ ?_]
    · unfold VG.Proof.Ffdh.generationValues Spec.Rsa.FixedBaseComb.table
      rfl
    · rw [hmt, hp₈ 0 (by decide), hr₇ 0 (by decide) (rowFits_of (by decide)), hm₆, hrow₅, hm₄]
      congr 1; exact he₃.mc.xv.n
    · rw [hmt, hp₈ 1 (by decide), hrow₇]; congr 1
    · intro a ha; rw [hmt]; exact hE₈ a ha
  · rw [hmt, (kp₈.outer i (by omega)).trans ((kp₃₇.outer i (by omega)).trans
      (hout₁₃ i (by omega) (by unfold sW; omega) (by unfold sWs sFn; omega) (by unfold sArr; omega)))]
    exact hf.saved i hi
  · rw [hmt, kp₈.only x hx hc, honly x hx hc]; exact hf.only x hx hc
  · exact (((k13.trans ((k₄.trans k₅).trans (k₆.trans k₇))).trans (k₈.trans kt))).mono (by decide)

end VG.Proof.Ffdh.X86_64.Cached

/-! # FFDH's reusable key-generation context on x86-64: the internal contract -/

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Impl.Ffdh.X86_64.VettedValidation

/-- `(ctx, ctx_len, domain, domain_len, p_len, scratch, scratch_len)`. -/
def pcPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
  let dom : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let scr : Region := ⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ s.rd = [dom, args] ∧ s.wr = [ctx, scr] ∧
    ctx.Disjoint dom ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ dom.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ctx ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (s.gpr .r8).toNat ∧ domainLenValid (s.gpr .r8).toNat (s.gpr .rcx).toNat ∧
    (s.gpr .rsi).toNat = generationPrecomputedWords (s.gpr .r8).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 0).toNat ∧
    domainValid (s.gpr .r8).toNat (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)

/-- The domain on entry. -/
abbrev pcDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat

def pcPost (s s' : State) : Prop :=
  (s'.gpr .rax).setWidth 32 = 1 ∧
    generationPrecompute (s.gpr .r8).toNat (pcDom s) = some (wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat)

def pcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ (pcDom s₁).map (·.toNat) = (pcDom s₂).map (·.toNat) ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0

/-- With the vetted groups' table: the precondition holds without its region. -/
def pcContract : Contract isa where
  pre s := pcPre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 0 s
  post := pcPost
  pub s₁ s₂ := pcPub s₁ s₂ ∧ s₁.syms tableSym = s₂.syms tableSym

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem pc_pre0 {s : State} (h : (generationPrecomputeContract abi).pre s) : pcPre s := by
  sig_pre [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq, pLenValid, domainLenValid] at h
  sig_pre [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq, pLenValid, domainLenValid] at h
  sig_split h
  sig_reduce [pcPre, pLenValid, domainLenValid]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem pc_post0 {s t : State} (h : pcPost s t) : (generationPrecomputeContract abi 8).post s t := by
  sig_post [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq]
  sig_reduce [pcPost, pcDom] at h
  exact h

theorem pc_pub0 {s₁ s₂ : State} (h : (generationPrecomputeContract abi 8).pub s₁ s₂) : pcPub s₁ s₂ := by
  sig_pub [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq, pLenValid, domainLenValid] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  exact h

theorem pc_implies : pcContract.Implies (generationPrecomputeContract (abi.withConsts tableConsts) 8) where
  pre s h := by
    obtain ⟨hp, hc⟩ := pre_consts.mp (Sig.pre_stack0 h)
    exact ⟨pc_pre0 hp, hc⟩
  post _ _ _ h := post_consts.mpr (pc_post0 h)
  pub _ _ _ _ h := ⟨pc_pub0 (pub_consts.mp h).1, (pub_consts.mp h).2 _ List.mem_cons_self⟩
  sat := precompute_sat

end VG.Proof.Ffdh.X86_64.Cached

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The precomputation's data, from the registers on entry. -/
def pcOf (s : State) : PcP :=
  ⟨s.gpr .r9, (stackArg s 0).toNat * 8, (s.gpr .r8).toNat, (s.gpr .rcx).toNat, s.gpr .rdx, pcDom s, s.gpr .rdi⟩

/-- What the precondition gives. -/
structure PcG (s : State) : Prop where
  k1 : 64 ≤ (pcOf s).k
  k2 : (pcOf s).k ≤ 1024
  dl : (pcOf s).dl = 2 * (pcOf s).k ∨ (pcOf s).dl = 3 * (pcOf s).k
  n : (s.gpr .rsi).toNat = (pcOf s).n
  hZ : 128 * (pcOf s).k + 256 ≤ (pcOf s).Z
  scr : Scr s (pcOf s).B (pcOf s).Z
  dom : Src s (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom
  domRd : InRegions (s.rd ++ s.wr) (pcOf s).dp (pcOf s).dl
  ctx : CtxRegion s (pcOf s).B (pcOf s).Z (pcOf s).cp (pcOf s).n
  dsep : ∀ i < (pcOf s).dl, 8 * (pcOf s).n ≤ ofs (pcOf s).cp ((pcOf s).dp + BitVec.ofNat 64 i)
  valid : Spec.Ffdh.domainValid (pcOf s).k (pcOf s).dom = true
  consts : ConstsOk tableConsts 0 s
  scrWr : (⟨(pcOf s).B, (pcOf s).Z⟩ : Region) ∈ s.wr
  retCtx : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨(pcOf s).cp, 8 * (pcOf s).n⟩
  retScr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨(pcOf s).B, (pcOf s).Z⟩

theorem precomputedWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth,
    Spec.Rsa.modulusWords]
  omega

theorem pcG_of {s : State} (h : pcContract.pre s) : PcG s := by
  obtain ⟨hp, hc⟩ := h
  obtain ⟨_, hrd, hwr, dcd, dcs, _, dds, _, nc, nd, ns, rc, _, rs, _, ⟨k1, k2⟩, hdl, hn, hsw, hv⟩ := hp
  have sa : stackArg (stripConsts tableConsts s) 0 = stackArg s 0 := rfl
  simp only [stripConsts_gpr, stripConsts_mem, stripConsts_wr, sa] at *
  have hn' : (s.gpr .rsi).toNat = 3 + 34 * (((s.gpr .r8).toNat + 7) / 8) := by
    rw [hn, precomputedWords_eq]
  have memRd : ∀ r ∈ (stripConsts tableConsts s).rd, r ∈ s.rd := fun r hr => List.mem_of_mem_take hr
  have hdom : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region) ∈ s.rd ++ s.wr :=
    List.mem_append_left _ (memRd _ (by rw [hrd]; simp))
  have hctx : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hscr : (⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  unfold Spec.Rsa.scratchWords at hsw
  have hrl : (s.gpr .rcx).toNat ≤ 2 ^ 64 := Nat.le_of_lt (s.gpr .rcx).isLt
  refine ⟨k1, k2, hdl, hn', by dsimp only [pcOf]; omega, Scr.of_mem hscr ns,
    src_of_region hdom hrl dds, ⟨_, hdom, Region.contains_self _ _⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, hv, hc, hscr,
    ?_, rs⟩
  · intro i hi
    exact ⟨_, hctx, by
      rw [show ((pcOf s).n) = (s.gpr .rsi).toNat from hn'.symm] at hi
      exact Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    exact ⟨_, List.mem_append_right _ hctx, by
      rw [show ((pcOf s).n) = (s.gpr .rsi).toNat from hn'.symm] at hi
      exact Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    rw [show ((pcOf s).n) = (s.gpr .rsi).toNat from hn'.symm] at hi
    exact out_scr dcs (contains_byte _ (by omega) (by omega))
  · dsimp only [pcOf, PcP.n, PcP.w]; omega
  · intro i hi
    have d : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rdi, 8 * (pcOf s).n⟩ := by
      rw [show 8 * (pcOf s).n = (s.gpr .rsi).toNat * 8 by dsimp only [pcOf, PcP.n, PcP.w]; omega]
      exact Region.Disjoint.symm dcd
    exact out_scr d (contains_byte _ hi hrl)
  · rw [show 8 * (pcOf s).n = (s.gpr .rsi).toNat * 8 by dsimp only [pcOf, PcP.n, PcP.w]; omega]
    exact rc

/-! ## The entry -/

/-- The header after the entry: the six saved registers, the context and
the scan's two arguments, in `sDom` and `sDomLen`. -/
def pcEntryMem (s : State) : Mem :=
  ((((((((s.mem.writeW (off (s.gpr .r9) (8 * 0)) (s.gpr .rbx)).writeW (off (s.gpr .r9) (8 * 1)) (s.gpr .rbp)).writeW
    (off (s.gpr .r9) (8 * 2)) (s.gpr .r12)).writeW (off (s.gpr .r9) (8 * 3)) (s.gpr .r13)).writeW
    (off (s.gpr .r9) (8 * 4)) (s.gpr .r14)).writeW (off (s.gpr .r9) (8 * 5)) (s.gpr .r15)).writeW
    (off (s.gpr .r9) (8 * sCtx)) (s.gpr .rdi)).writeW (off (s.gpr .r9) (8 * sDom)) (s.gpr .rcx)).writeW
    (off (s.gpr .r9) (8 * sDomLen)) (s.gpr .r8)

theorem pcEntryMem_facts (s : State) :
    let m := pcEntryMem s
    word m (s.gpr .r9) (8 * 0) = s.gpr .rbx ∧ word m (s.gpr .r9) (8 * 1) = s.gpr .rbp ∧
    word m (s.gpr .r9) (8 * 2) = s.gpr .r12 ∧ word m (s.gpr .r9) (8 * 3) = s.gpr .r13 ∧
    word m (s.gpr .r9) (8 * 4) = s.gpr .r14 ∧ word m (s.gpr .r9) (8 * 5) = s.gpr .r15 ∧
    word m (s.gpr .r9) (8 * sCtx) = s.gpr .rdi ∧ word m (s.gpr .r9) (8 * sDom) = s.gpr .rcx ∧
    word m (s.gpr .r9) (8 * sDomLen) = s.gpr .r8 ∧ Outside (s.gpr .r9) 0 (8 * 32) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m pcEntryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem pcEntry_ok {s : State} (g : PcG s) :
    WP isa (.block Precompute.entry) s fun t =>
      t.gpr .rdi = s.gpr .rdx ∧ t.mem = pcEntryMem s ∧ Keep [.rdi] s t := by
  have hZ := g.hZ
  have hk := g.k1
  have hw : ∀ i < 32, InRegions s.wr (off (s.gpr .r9) (8 * i)) 8 := fun i hi =>
    g.scr.st (by dsimp only [pcOf] at hZ ⊢; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = s.gpr .rdx ∧ t.mem = pcEntryMem s) ?_ rfl)
    fun t ⟨⟨hd, hm⟩, k⟩ => ⟨hd, hm, k⟩
  have e128 : BitVec.ofInt 64 ((128 : Nat) : Int) = BitVec.ofNat 64 (8 * sDom) := rfl
  have e136 : BitVec.ofInt 64 ((136 : Nat) : Int) = BitVec.ofNat 64 (8 * sDomLen) := rfl
  have w128 : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (8 * sDom)) 8 := hw sDom (by decide)
  have w136 : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (8 * sDomLen)) 8 := hw sDomLen (by decide)
  unfold Precompute.entry save
  simp only [saved, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, at_, hdrOff, hw 0 (by decide), hw 1 (by decide),
    hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sCtx (by decide),
    e128, e136, w128, w136]
  rfl

theorem frame_of_inScr {B : Addr} {Z : Nat} {m m' : Mem} (h : InScr B Z m m') : Frame [⟨B, Z⟩] m m' :=
  fun x hx => h x (by
    rcases Nat.lt_or_ge (ofs B x) Z with hl | hl
    · exact absurd (contains_scr hl) (hx _ List.mem_cons_self)
    · exact hl)

theorem Src.bytes {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) :
    Spec.Rsa.bytesAt s.mem p bs.length = bs := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.val i h₂

theorem pcDom_length (s : State) : (pcOf s).dom.length = (pcOf s).dl := by
  simp only [pcOf, pcDom, Spec.Rsa.bytesAt, List.length_map, List.length_range]

/-! ## The recognition and the modulus check -/

/-- The header once the scan's result and `Domain`'s arguments are stored. -/
def afterMem (m : Mem) (B : Addr) (r d L k : BitVec 64) : Mem :=
  (((m.writeW (off B (8 * sRec)) r).writeW (off B (8 * sDom)) d).writeW (off B (8 * sDomLen)) L).writeW
    (off B (8 * sK)) k

theorem afterMem_facts (m : Mem) (B : Addr) (r d L k : BitVec 64) :
    let m' := afterMem m B r d L k
    word m' B (8 * sRec) = r ∧ word m' B (8 * sDom) = d ∧ word m' B (8 * sDomLen) = L ∧
      word m' B (8 * sK) = k ∧ Outside B 0 (8 * 32) m m' ∧
      ∀ i < 32, i ≠ sRec → i ≠ sDom → i ≠ sDomLen → i ≠ sK → word m' B (8 * i) = word m B (8 * i) := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi h₁ h₂ h₃ h₄ => ?_⟩ <;> unfold m' afterMem
  · repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) | exact word_writeW_self _ _ _ _)
  · repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) | exact word_writeW_self _ _ _ _)
  · repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) | exact word_writeW_self _ _ _ _)
  · exact word_writeW_self _ _ _ _
  · repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)
  · refine word_skip (word_skip (word_skip (word_skip rfl ?_ (by decide) hi) ?_ (by decide) hi) ?_ (by decide) hi)
      ?_ (by decide) hi <;> intro e <;> subst e <;> contradiction

theorem afterScan_ok {t : State} {B : Addr} {Z : Nat} (hs : Scr t B Z) (hZ : 256 ≤ Z)
    (hb : t.gpr .r9 = B) {L : BitVec 64} (hl : word t.mem B (8 * sDom) = L) :
    WP isa (.block Precompute.afterScan) t fun u => u.gpr .rdi = B ∧
      u.mem = afterMem t.mem B (t.gpr .rax) (t.gpr .rdi) L (t.gpr .r8) ∧ Keep [.rcx, .rdi] t u := by
  have hw : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi => hs.st (by omega)
  have e128 : BitVec.ofInt 64 ((128 : Nat) : Int) = BitVec.ofNat 64 (8 * sDom) := rfl
  have hr : ∀ v : BitVec 64, (t.mem.writeW (off B (8 * sRec)) v).readW (B + BitVec.ofNat 64 (8 * sDom)) 64 = L :=
    fun v => word_skip hl (by decide) (by decide) (by decide)
  have r128 : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (8 * sDom)) 8 := hs.ld (by unfold sDom sFn; omega)
  refine WP.mono (WP.keep [.rcx, .rdi] (Q := fun u => u.gpr .rdi = B ∧
    u.mem = afterMem t.mem B (t.gpr .rax) (t.gpr .rdi) L (t.gpr .r8)) ?_ rfl)
    fun u ⟨⟨hd, hm⟩, k⟩ => ⟨hd, hm, k⟩
  unfold Precompute.afterScan
  xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, at_, hdrOff, hb, e128, hr, r128, hw sRec (by decide),
    hw sDom (by decide), hw sDomLen (by decide), hw sK (by decide)]
  rfl

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the modulus check leaves for `main`. -/
structure StartPost (s v : State) : Prop where
  zf : v.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip ((pcOf s).dom.take (pcOf s).k)) (pcOf s).k)
  main : MainPre (pcOf s) v
  saved : ∀ i < 6, word v.mem (pcOf s).B (8 * i) = s.gpr (saved.getD i .rax)
  scr : InScr (pcOf s).B (pcOf s).Z s.mem v.mem
  keep : Keep (.rdi :: mmRegs) s v

/-- What the entry leaves. -/
def EntryDone (s u : State) : Prop :=
  u.gpr .rdi = s.gpr .rdx ∧ u.mem = pcEntryMem s ∧ Keep [.rdi] s u ∧ u.syms = s.syms

theorem entry_done {s : State} (g : PcG s) : WP isa (.block Precompute.entry) s (EntryDone s) :=
  WP.mono_syms (pcEntry_ok g) fun _ ⟨hd, hm, k⟩ sy => ⟨hd, hm, k, sy⟩

/-- The scan's arguments and table after the entry. -/
theorem EntryDone.scan {s u : State} (g : PcG s) (hu : EntryDone s u) :
    VG.Proof.Ffdh.X86_64.VettedValidation.Context (pcOf s).B (pcOf s).dp (pcOf s).k (pcOf s).dom u ∧
    VG.Proof.Ffdh.X86_64.VettedValidation.TableAt (u.syms VG.Impl.Ffdh.X86_64.VettedValidation.tableSym +
      BitVec.ofNat 64 0) VG.Impl.Ffdh.VettedGroups.groups u := by
  have hZ := g.hZ
  have hk := g.k1
  have hk2 := g.k2
  have hdl := g.dl
  obtain ⟨hdU, hmU, kU, symU⟩ := hu
  obtain ⟨e0, e1, e2, e3, e4, e5, eC, eD, eL, eO⟩ := pcEntryMem_facts s
  rw [← hmU] at e0 e1 e2 e3 e4 e5 eC eD eL eO
  have iU : InScr (pcOf s).B (pcOf s).Z s.mem u.mem := InScr.of_outside eO (by dsimp only [pcOf] at hZ ⊢; omega)
  have bU : u.gpr .r9 = (pcOf s).B := kU.gpr (by decide)
  have scrU : Scr u (pcOf s).B (pcOf s).Z := g.scr.congr kU.2.2
  have domU : Src u (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom := g.dom.congrK iU kU
  have ctxU : VG.Proof.Ffdh.X86_64.VettedValidation.Context (pcOf s).B (pcOf s).dp (pcOf s).k (pcOf s).dom u :=
    ⟨bU, hdU, by rw [pcDom_length]; exact eD.trans (ofNat_toNat' _).symm,
      eL.trans (ofNat_toNat' _).symm, scrU.ld (d := 8 * sDom) (by unfold sDom sFn; dsimp only [pcOf] at hZ ⊢; omega),
      scrU.ld (d := 8 * sDomLen) (by unfold sDomLen sFn; dsimp only [pcOf] at hZ ⊢; omega),
      by rw [kU.2.1, kU.2.2, pcDom_length]; exact g.domRd, Src.bytes domU,
      by rw [pcDom_length]; exact hdl, hk, hk2⟩
  have tableU := VG.Proof.Ffdh.X86_64.VettedValidation.consts_table_after g.consts (frame_of_inScr iU) kU g.scrWr
  rw [← symU, ← BitVec.add_zero (u.syms _)] at tableU
  exact ⟨ctxU, tableU⟩

/-- What the scan leaves. -/
def ScanDone (s u t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (pcOf s).recog ∧ t.mem = u.mem ∧ Keep VG.Proof.Ffdh.X86_64.VettedValidation.clobbers u t

theorem scan_done {s u : State} (g : PcG s) (hu : EntryDone s u) :
    WP isa (VG.Impl.Ffdh.X86_64.VettedValidation.scan VG.Impl.Ffdh.VettedGroups.groups 0) u (ScanDone s u) :=
  WP.mono (VG.Proof.Ffdh.X86_64.VettedValidation.scan_ok (k := (pcOf s).k) (dom := (pcOf s).dom) _ 0 u
    (hu.scan g).1 rfl (hu.scan g).2
    (by simpa only [Nat.zero_add, VG.Impl.Ffdh.VettedGroups.tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length))) fun _ h => h

theorem after_done {s u t : State} (g : PcG s) (hu : EntryDone s u) (ht : ScanDone s u t) :
    WP isa (.block (Precompute.afterScan ++ domHead)) t (StartPost s) := by
  have hZ := g.hZ
  have hk := g.k1
  have hk2 := g.k2
  have hdl := g.dl
  obtain ⟨hdU, hmU, kU, _⟩ := hu
  obtain ⟨vT, mT, kT⟩ := ht
  obtain ⟨e0, e1, e2, e3, e4, e5, eC, eD, eL, eO⟩ := pcEntryMem_facts s
  rw [← hmU] at e0 e1 e2 e3 e4 e5 eC eD eL eO
  have iU : InScr (pcOf s).B (pcOf s).Z s.mem u.mem := InScr.of_outside eO (by dsimp only [pcOf] at hZ ⊢; omega)
  have bU : u.gpr .r9 = (pcOf s).B := kU.gpr (by decide)
  have scrU : Scr u (pcOf s).B (pcOf s).Z := g.scr.congr kU.2.2
  have domU : Src u (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom := g.dom.congrK iU kU
  have ctxU : VG.Proof.Ffdh.X86_64.VettedValidation.Context (pcOf s).B (pcOf s).dp (pcOf s).k (pcOf s).dom u :=
    ⟨bU, hdU, by rw [pcDom_length]; exact eD.trans (ofNat_toNat' _).symm,
      eL.trans (ofNat_toNat' _).symm, scrU.ld (d := 8 * sDom) (by unfold sDom sFn; dsimp only [pcOf] at hZ ⊢; omega),
      scrU.ld (d := 8 * sDomLen) (by unfold sDomLen sFn; dsimp only [pcOf] at hZ ⊢; omega),
      by rw [kU.2.1, kU.2.2, pcDom_length]; exact g.domRd, Src.bytes domU,
      by rw [pcDom_length]; exact hdl, hk, hk2⟩
  have bT : t.gpr .r9 = (pcOf s).B := (kT.gpr (by decide)).trans bU
  have dT : t.gpr .rdi = s.gpr .rdx := (kT.gpr (by decide)).trans hdU
  have r8T : t.gpr .r8 = s.gpr .r8 := (kT.gpr (by decide)).trans (kU.gpr (by decide))
  have scrT : Scr t (pcOf s).B (pcOf s).Z := scrU.congr kT.2.2
  rw [WP.block_append_iff]
  refine WP.mono (afterScan_ok scrT (by dsimp only [pcOf] at hZ ⊢; omega) bT (L := s.gpr .rcx)
    (by rw [mT]; exact eD)) fun w ⟨dW, mW, kW⟩ => ?_
  obtain ⟨aR, aD, aL, aK, aO, aE⟩ := afterMem_facts t.mem (pcOf s).B (t.gpr .rax) (t.gpr .rdi) (s.gpr .rcx) (t.gpr .r8)
  rw [← mW] at aR aD aL aK aO aE
  have iW : InScr (pcOf s).B (pcOf s).Z t.mem w.mem := InScr.of_outside aO (by dsimp only [pcOf] at hZ ⊢; omega)
  have domW : Src w (pcOf s).B (pcOf s).Z (pcOf s).dp (pcOf s).dom :=
    (domU.congrK (by rw [mT]; exact InScr.refl _ _ _) kT).congrK iW kW
  have plen : ((pcOf s).dom.take (pcOf s).k).length = (pcOf s).k := by
    rw [List.length_take, pcDom_length]; omega
  refine WP.mono (domHead_ok (scrT.congr kW.2.2) dW (by dsimp only [pcOf] at hZ ⊢; omega) hk hk2
    (aD.trans dT) (aK.trans (r8T.trans (ofNat_toNat' _).symm)) (domW.take _) plen)
    fun v ⟨zV, gV, qV, fV, dV, kV⟩ => ?_
  have other : ∀ i < 32, i ≠ sG → i ≠ sQ → word v.mem (pcOf s).B (8 * i) = word w.mem (pcOf s).B (8 * i) :=
    fun i hi hg hq => fV.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega) (by omega)
  have iV : InScr (pcOf s).B (pcOf s).Z w.mem v.mem := InScr.of_frm fV (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> dsimp only [sG, sQ, sFn, pcOf] at hZ ⊢ <;> omega)
  have keep : Keep (.rdi :: mmRegs) s v := (((kU.trans kT).trans kW).trans kV).mono (by decide)
  refine ⟨zV, ⟨hk, hk2, hdl, pcDom_length s, hZ, g.scr.congr keep.2.2, dV, domW.congrK iV kV,
    g.ctx.congr keep.2.1 keep.2.2, g.dsep, ?_, g.valid⟩, ?_, ?_, keep⟩
  · intro e he
    simp only [PcP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aD.trans dT
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aL.trans (ofNat_toNat' _).symm
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aK.trans (r8T.trans (ofNat_toNat' _).symm)
    · exact gV
    · exact qV
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide), aE _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
        (by dsimp only; decide), mT]
      exact eC
    · rw [other _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)]; exact aR.trans vT
  · intro i hi
    rw [other i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega),
      aE i (by omega) (by unfold sRec sY sFn; omega) (by unfold sDom sFn; omega)
        (by unfold sDomLen sFn; omega) (by unfold sK sFn; omega), mT]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [e0, e1, e2, e3, e4, e5]
  · exact (iU.trans (by rw [mT]; exact InScr.refl _ _ _)).trans (iW.trans iV)

/-- After `afterScan`: the modulus check's hypotheses. -/
theorem afterScan_dhp {s u t : State} (g : PcG s) (hu : EntryDone s u) (ht : ScanDone s u t) :
    WP isa (.block Precompute.afterScan) t
      (VG.Proof.Ffdh.X86_64.DHP ⟨(pcOf s).B, (pcOf s).Z, (pcOf s).k, (pcOf s).dp⟩) := by
  have hZ := g.hZ
  obtain ⟨hdU, hmU, kU, _⟩ := hu
  obtain ⟨_, mT, kT⟩ := ht
  obtain ⟨_, _, _, _, _, _, _, eD, _, _⟩ := pcEntryMem_facts s
  rw [← hmU] at eD
  have bT : t.gpr .r9 = (pcOf s).B := (kT.gpr (by decide)).trans (kU.gpr (by decide))
  have dT : t.gpr .rdi = s.gpr .rdx := (kT.gpr (by decide)).trans hdU
  have r8T : t.gpr .r8 = s.gpr .r8 := (kT.gpr (by decide)).trans (kU.gpr (by decide))
  have scrT : Scr t (pcOf s).B (pcOf s).Z := (g.scr.congr kU.2.2).congr kT.2.2
  refine WP.mono (afterScan_ok scrT (by dsimp only [pcOf] at hZ ⊢; omega) bT (L := s.gpr .rcx)
    (by rw [mT]; exact eD)) fun w ⟨dW, mW, kW⟩ => ?_
  obtain ⟨_, aD, _, aK, _, _⟩ := afterMem_facts t.mem (pcOf s).B (t.gpr .rax) (t.gpr .rdi) (s.gpr .rcx) (t.gpr .r8)
  rw [← mW] at aD aK
  exact ⟨scrT.congr kW.2.2, dW, by dsimp only [pcOf] at hZ ⊢; omega, aD.trans dT,
    aK.trans (r8T.trans (ofNat_toNat' _).symm)⟩

theorem start_then {s : State} (g : PcG s) {c : Prog isa} {Q : State → Prop}
    (h : ∀ v, StartPost s v → WP isa c v Q) :
    WP isa (.seq (.block Precompute.entry) (.seq (VG.Impl.Ffdh.X86_64.VettedValidation.scan
      VG.Impl.Ffdh.VettedGroups.groups 0) (.seq (.block (Precompute.afterScan ++ domHead)) c))) s Q :=
  WP.seq (WP.mono (entry_done g) fun _ hu => WP.seq (WP.mono (scan_done g hu) fun _ ht =>
    WP.seq (WP.mono (after_done g hu ht) h)))

/-! ## The computation, the branch and the exit -/

theorem main_ok (Mo : Mont) (R : R2Impl Mo) {p : PcP} {s : State} (h : MainPre p s) :
    WP isa (Precompute.main Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rdi = p.B ∧
        Spec.Rsa.wordsAt t.mem p.cp p.n = VG.Proof.Ffdh.generationValues p.k p.dom ∧
        (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ p.Only s.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  unfold Precompute.main
  rw [show GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata),
      .block VG.Impl.Rsa.X86_64.head] ++ pSetup ++
      [.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++
      Precompute.storePrefix ++ Precompute.table Mo.mm ++ [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]] =
    (GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata)]) ++
      (([.block VG.Impl.Rsa.X86_64.head] ++ pSetup) ++
        ([.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++
          (Precompute.storePrefix ++ (Precompute.table Mo.mm ++ [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]]))))
    by simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_seqs_append (by simp [GenerateKey.bound]) (by simp) (WP.mono (front_ok h) fun u hf => ?_)
  refine WP.mono (inner_ok Mo R h hf) fun t ⟨hr, hd, hw, hs, ho, k⟩ =>
    ⟨hr, hd, hw, hs, ho, (hf.keep.trans k).mono (by decide)⟩

theorem _root_.VG.Proof.Ffdh.X86_64.Cached.PcP.Only.of_inScr {p : PcP} {m m' : Mem} (h : InScr p.B p.Z m m') :
    p.Only m m' := fun x hx _ => h x hx

theorem body_ok (Mo : Mont) (R : R2Impl Mo) {s : State} (g : PcG s) :
    WP isa (Precompute.body Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rdi = (pcOf s).B ∧
        Spec.Rsa.wordsAt t.mem (pcOf s).cp (pcOf s).n = VG.Proof.Ffdh.generationValues (pcOf s).k (pcOf s).dom ∧
        (∀ i < 6, word t.mem (pcOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ (pcOf s).Only s.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  unfold Precompute.body
  refine start_then g fun v hv => ?_
  have mv := hv.main.modValid
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip ((pcOf s).dom.take (pcOf s).k)) (pcOf s).k)
    (by simp [eval, hv.zf]) (fun hf => ?_) (fun _ => ?_)
  · rw [mv] at hf
    contradiction
  · refine WP.mono (main_ok Mo R hv.main) fun t ⟨hr, hd, hw, hs, ho, k⟩ =>
      ⟨hr, hd, hw, fun i hi => (hs i hi).trans (hv.saved i hi), (PcP.Only.of_inScr hv.scr).trans ho,
        (hv.keep.trans k).mono (by decide)⟩

theorem pc_correct (Mo : Mont) (R : R2Impl Mo)
    (hmx : (Precompute.code Mo.mm (.seq (.block r2Head) R.code)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (Precompute.code Mo.mm (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ pcContract.post s t := by
  have g := pcG_of h
  have hZ := g.hZ
  have hk := g.k1
  suffices hw : WP isa (Precompute.code Mo.mm (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ pcContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Precompute.code
  refine WP.seq (WP.mono (body_ok Mo R g) fun u ⟨hr, hd, hw, hs, ho, k⟩ => ?_)
  refine WP.mono (exit_ok (g.scr.congr k.2.2) hd (by dsimp only [pcOf] at hZ ⊢; omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    exact ho _ (out_scr g.retScr hbyte) (out_scr g.retCtx hbyte)
  · change ((t.gpr .rax).setWidth 32) = 1
    rw [kk.gpr (show .rax ∉ saved by decide), hr]
    rfl
  · change Spec.Ffdh.generationPrecompute (s.gpr .r8).toNat (pcDom s) =
      some (Spec.Rsa.wordsAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    rw [hm, g.n]
    change _ = some (Spec.Rsa.wordsAt u.mem (pcOf s).cp (pcOf s).n)
    rw [hw]
    apply VG.Proof.Ffdh.generationPrecompute_eq
    · have := pcDom_length s
      have := g.dl
      change (pcOf s).k ≤ (pcOf s).dom.length
      omega
    · exact VG.Proof.Ffdh.domainValid_mod g.valid

end VG.Proof.Ffdh.X86_64.Cached
