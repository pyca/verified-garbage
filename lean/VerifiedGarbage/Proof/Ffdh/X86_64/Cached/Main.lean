module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Front
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH's context on x86-64: the computation for a valid domain -/

@[expose] public section

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
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf p.k p.dom) := by
    have hv := (VG.Proof.Ffdh.domainValid_iff p.k p.dom).mp h.valid
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf p.k p.dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  have hbz : (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'
      (VG.Proof.Ffdh.lead_lt hne) ≠ 0 := by
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
  refine WP.mono (width_only hs₂ hdi₂ (by omega) hcx₂ hc8 hEl₂ (by omega) (by omega) hRec₂ (recognize_lt _ _))
    fun s₃ ⟨hax₃, hm₃, k₃⟩ => ?_
  rw [hpick] at hax₃
  have k13 := k12.trans k₃
  have hcw : ∀ i < 3, InRegions s₃.wr (off p.cp (8 * i)) 8 := fun i hi => by
    rw [k13.2.2]; exact h.ctx.wr i (by unfold PcP.n; omega)
  refine WP.mono (metadata_ok (hs₂.congr k₃.2.2) ((k₃.gpr (by decide)).trans hdi₂) (by omega) hax₃ h.bits_le
    (by rw [hm₃, hfw _ (by decide) (by decide) (by decide)]; exact hCtx) hcw) fun t ⟨hmt, kt⟩ => ?_
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

end VG.Proof.Ffdh.X86_64.Cached
