module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Entry
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A candidate on x86-64: correctness

The front of `codeWith`, from a state `candContract` allows: what it uses
of its precondition (`KCtx`), and the zeros to `out` and the length check
(`front_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `codeWith` uses of its precondition, for the scratch space `B`
(`arg 3`) of `Z` bytes and the prime's length `L`. -/
structure KCtx (s : State) : Prop where
  k1 : 32 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 512
  k8 : (s.gpr .rsi).toNat % 8 = 0
  el1 : 1 ≤ (s.gpr .r8).toNat
  el8 : (s.gpr .r8).toNat ≤ 8
  pl : (arg s 0).toNat = 0 ∨ (arg s 0).toNat = (s.gpr .rsi).toNat
  hZ : 128 * (s.gpr .rsi).toNat ≤ (arg s 4).toNat * 8
  hs : Scr s (arg s 3) ((arg s 4).toNat * 8)
  ha : ∀ i < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  hsep : ∀ m', Outside (arg s 3) 0 (8 * 32) s.mem m' → ∀ i < 3, m'.readW (stackArgAddr s i) 64 = stackArg s i
  esrc : Src s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rcx) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  psrc : Src s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .r9) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
  rsrc : Src s (arg s 3) ((arg s 4).toNat * 8) (arg s 1) (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat)
  ou : OutUp s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat
  doe : ∀ i < (s.gpr .r8).toNat, ∀ j < (s.gpr .rsi).toNat,
    s.gpr .rcx + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  dop : ∀ i < (arg s 0).toNat, ∀ j < (s.gpr .rsi).toNat,
    s.gpr .r9 + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  dor : ∀ i < (arg s 2).toNat, ∀ j < (s.gpr .rsi).toNat,
    arg s 1 + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  hret : ∀ b < 8, (arg s 4).toNat * 8 ≤ ofs (arg s 3) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    (∀ c < 8, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdx + BitVec.ofNat 64 c) ∧
    ∀ j < (s.gpr .rsi).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem stackArgAddr_add (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  simp only [stackArgAddr]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []

theorem kctx_of {s : State} (h : candPre s) : KCtx s := by
  simp only [candPre] at h
  obtain ⟨hsp, hrd, hwr, dOu, dOe, dOp, dOr, dOs, dOa, dUe, dUp, dUr, dUs, dUa, des, dps, drs, dsa,
    dRo, dRu, dRe, dRp, dRr, dRs, dRa, wO, wU, wE, wP, wR, wS, hk, hl1, hl8, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2, hk8⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (arg s 3) ((arg s 4).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have ha : ∀ i < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := fun i hi =>
    ⟨⟨stackArgAddr s 0, 40⟩, by rw [hrd]; simp,
      by rw [stackArgAddr_add s i]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have hsep : ∀ m', Outside (arg s 3) 0 (8 * 32) s.mem m' → ∀ i < 3, m'.readW (stackArgAddr s i) 64 = stackArg s i :=
    fun m' ho i hi => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * i + b) (by omega_using [hi, hb]) (by omega_using []))
      rw [stackArgAddr_add s i, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega_using [hsl, this]))
  have he := src_of_region (s := s) (B := arg s 3) (Z := (arg s 4).toNat * 8) (by rw [hrd]; simp) (by omega_using []) des
  have hp := src_of_region (s := s) (B := arg s 3) (Z := (arg s 4).toNat * 8) (by rw [hrd]; simp) (by omega_using []) dps
  have hr := src_of_region (s := s) (B := arg s 3) (Z := (arg s 4).toNat * 8) (by rw [hrd]; simp) (by omega_using []) drs
  have ho : OutUp s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat := by
    refine ⟨⟨⟨s.gpr .rdx, 8⟩, by rw [hwr]; simp, ?_⟩, fun b hb => out_scr dUs (contains_byte _ (by omega_using [hb]) (by omega_using [])),
      fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega_using [hj]) (by omega_using [])⟩,
      fun j hj => out_scr dOs (contains_byte _ (by omega_using [hj]) (by omega_using [])), fun j hj b hb he => ?_⟩
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []
    · exact dOu _ (contains_byte _ (by omega_using [hj]) (by omega_using [])) (by rw [he]; exact contains_byte _ (by omega_using [hb]) (by omega_using []))
  refine ⟨hk1, hk2, hk8, hl1, hl8, hpl, by omega_using [hsl], hs, ha, hsep, he, hp, hr, ho,
    fun i hi j hj hh => dOe _ (contains_byte (s.gpr .rdi) (i := j) (by omega_using [hj]) (by omega_using []))
      (by rw [← hh]; exact contains_byte _ (by omega_using [hi]) (by omega_using [])),
    fun i hi j hj hh => dOp _ (contains_byte (s.gpr .rdi) (i := j) (by omega_using [hj]) (by omega_using []))
      (by rw [← hh]; exact contains_byte _ (by omega_using [hi]) (by omega_using [])),
    fun i hi j hj hh => dOr _ (contains_byte (s.gpr .rdi) (i := j) (by omega_using [hj]) (by omega_using []))
      (by rw [← hh]; exact contains_byte _ (by omega_using [hi]) (by omega_using [])), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega_using [hb]) (by omega_using [])
  exact ⟨out_scr dRs hc, fun c hc' he => dRu _ hc (by rw [he]; exact contains_byte _ (by omega_using [hc']) (by omega_using [])),
    fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega_using [hj]) (by omega_using []))⟩

/-- A buffer whose octets did not change. -/
theorem Src.congr' {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : ∀ i < bs.length, t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i)) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm i hi]; exact h.val i hi, h.out⟩

/-- After the zeros to `out` and the length check, from the state `t₁` after
the entry. -/
structure Front (s t₁ t₃ : State) : Prop where
  cf : t₃.cf = some (decide ((arg s 2).toNat < (s.gpr .rsi).toNat))
  zero : ∀ i < (s.gpr .rsi).toNat, t₃.mem (s.gpr .rdi + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ j < (s.gpr .rsi).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) → t₃.mem x = t₁.mem x
  keep : Keep [.rsi, .rcx, .rax] t₁ t₃

/-- `zeroOut` and the length check. -/
theorem front_ok {s t₁ : State} (c : KCtx s) (he : EntryPost s t₁ (arg s 3)) :
    WP isa (.seq zeroOut (.block [.mov .rax (.mem (hdr kRandLen)), .mov .rcx (.mem (hdr kLen)),
      .alu .cmp .rax (.reg .rcx)])) t₁ (Front s t₁) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hs₁ := hs.congr he.keep.2.2
  refine WP.seq (WP.mono (zeroOut_ok (k := (s.gpr .rsi).toNat) hs₁ he.rdi (by omega_using [hZ, hk1]) (by omega_using [hk1]) (by omega_using [hk2]) he.out
    (by rw [he.len, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (fun j hj => by rw [he.keep.2.2]; exact c.ou.outw j hj))
    fun t₂ ⟨hz₂, hf₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hw₂ : ∀ i < 32, word t₂.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := fun i hi =>
    Mem.readW_congr fun b hb => hf₂ _ fun j hj he' => by
      have := c.ou.outZ j hj; rw [← he', ofs_off _ (by omega_using [hi, hb])] at this; omega_using [hZ, hk1, hi, hb, this]
  have hdi₂ : t₂.gpr .rdi = arg s 3 := (k₂.gpr (by decide)).trans he.rdi
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (arg s 3) (8 * i)) 8 := fun i hi => hs₂.ld (by omega_using [hZ, hk1, hi])
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.cf = some (decide ((arg s 2).toNat < (s.gpr .rsi).toNat)) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ kRandLen (by decide), hl₂ kLen (by decide), hw₂ kRandLen (by decide),
      hw₂ kLen (by decide), he.rlen, he.len]) rfl) fun t₃ ⟨⟨hcf, hm₃⟩, k₃⟩ =>
    ⟨hcf, fun i hi => by rw [hm₃]; exact hz₂ i hi, fun x hx => by rw [hm₃]; exact hf₂ x hx, (k₂.trans k₃).mono (by decide)⟩

/-- The header words survive the zeros to `out`. -/
theorem Front.word {s t₁ t₃ : State} (c : KCtx s) (h : Front s t₁ t₃) {i : Nat} (hi : i < 32) :
    word t₃.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  exact Mem.readW_congr fun b hb => h.frame _ fun j hj he' => by
    have := c.ou.outZ j hj; rw [← he', ofs_off _ (by omega_using [hi, hb])] at this; omega_using [hi, hZ, hk1, hb, this]

/-- What `kMainWith` needs, after the entry, the zeros and the length check. -/
theorem mainCtx_of {s t₁ t₃ : State} {w : Nat} (c : KCtx s) (he : EntryPost s t₁ (arg s 3)) (h : Front s t₁ t₃)
    (hw : (s.gpr .rsi).toNat = 8 * w) (hlt : (s.gpr .rsi).toNat ≤ (arg s 2).toNat) :
    MainCtx t₃ (arg s 3) ((arg s 4).toNat * 8) (8 * w) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9)
      (arg s 1) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat) (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hk8 := c.k8
  have k13 : Keep [.r11, .rax, .rdi, .rsi, .rcx] s t₃ := (he.keep.trans h.keep).mono (by decide)
  have hs₃ := hs.congr k13.2.2
  have hdi₃ : t₃.gpr .rdi = arg s 3 := (h.keep.gpr (by decide)).trans he.rdi
  have hrs : ∀ i < 32, word t₃.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := fun i hi => h.word c hi
  have hhi : ∀ x, 8 * 32 ≤ ofs (arg s 3) x → (∀ j < (s.gpr .rsi).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      t₃.mem x = s.mem x := fun x hx hx' => by
    rw [h.frame x hx', he.frame x (Or.inr (by omega_using [hx]))]
  have ho₃ : OutUp t₃ (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat :=
    c.ou.congr k13.2.2
  have hsrc : ∀ {p : Addr} {bs : List Byte}, Src s (arg s 3) ((arg s 4).toNat * 8) p bs →
      (∀ i < bs.length, ∀ j < (s.gpr .rsi).toNat, p + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      Src t₃ (arg s 3) ((arg s 4).toNat * 8) p bs := fun {p bs} h hd =>
    VG.Proof.RsaKeyGen.X86_64.Src.congr' h (fun i hi => hhi _ (by have := h.out i hi; omega_using [hZ, hk1, this]) (hd i hi)) k13.2.1 k13.2.2
  refine ⟨hs₃, hdi₃, by rw [show 8 * w / 8 = w by omega_using []]; unfold slot aTab hdrBytes; omega_using [hw, hZ, hk1],
    by rw [show 8 * w / 8 = w by omega_using []]; unfold slot aRm1 hdrBytes; omega_using [hw, hZ, hk1], by omega_using [hw, hk1],
    by omega_using [hw, hk2], by omega_using [], by rw [hrs _ (by decide)]; exact he.out, ?_, by rw [hrs _ (by decide)]; exact he.usedP,
    by rw [hrs _ (by decide)]; exact he.e, ?_, by rw [hrs _ (by decide)]; exact he.p, ?_,
    by rw [hrs _ (by decide)]; exact he.rand, ?_, hsrc c.esrc (fun i hi => c.doe i (by rwa [bytesAt_length] at hi)),
    hsrc c.psrc (fun i hi => c.dop i (by rwa [bytesAt_length] at hi)),
    hsrc c.rsrc (fun i hi => c.dor i (by rwa [bytesAt_length] at hi)), by rw [bytesAt_length]; exact c.el1,
    by rw [bytesAt_length]; exact c.el8, by rw [bytesAt_length, ← hw]; exact c.pl,
    by rw [bytesAt_length]; exact (arg s 2).isLt, by rw [bytesAt_length, ← hw]; exact hlt, by rw [← hw]; exact ho₃⟩
  · rw [hrs _ (by decide), he.len, ← hw, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hrs _ (by decide), he.elen, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hrs _ (by decide), he.plen, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hrs _ (by decide), he.rlen, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.RsaKeyGen.X86_64
