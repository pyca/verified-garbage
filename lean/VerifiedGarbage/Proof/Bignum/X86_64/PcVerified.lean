import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Bignum.X86_64.CrtP
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaGlue
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaVecR
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaRegion
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubCode`. -/
section

/-!
# `vg_rsa_public` on x86-64: correctness

`code`, from a state its contract allows, writes `publicOp` of its inputs
(`code_correct`), against `pubContract`, which states the shared contract's
precondition on the registers and the stack.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-! ## Regions -/

theorem contains_scr {B a : Addr} {Z : Nat} (h : VG.Proof.Bignum.X86_64.ofs B a < Z) : (⟨B, Z⟩ : Region).Contains a 1 := by
  simp only [Region.Contains, VG.Proof.Bignum.X86_64.ofs] at *; omega

/-- A byte of a region disjoint from the working space is outside it. -/
theorem out_scr {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr} (ha : r.Contains a 1) :
    Z ≤ VG.Proof.Bignum.X86_64.ofs B a := by
  rcases Nat.lt_or_ge (VG.Proof.Bignum.X86_64.ofs B a) Z with h | h
  · exact absurd (VG.Proof.Bignum.X86_64.contains_scr h) (hd a ha)
  · exact h

theorem contains_byte (p : Addr) {i len : Nat} (hi : i < len) (hlen : len ≤ 2 ^ 64) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
  Offset.contains_base p (by omega) (by omega)

/-- A buffer disjoint from the working space, as a byte string. -/
theorem src_of_region {s : State} {B : Addr} {Z : Nat} {p : Addr} {len : Nat}
    (hr : (⟨p, len⟩ : Region) ∈ s.rd ++ s.wr) (hlen : len ≤ 2 ^ 64)
    (hd : (⟨p, len⟩ : Region).Disjoint ⟨B, Z⟩) : Src s B Z p (Spec.Rsa.bytesAt s.mem p len) := by
  have hl : (Spec.Rsa.bytesAt s.mem p len).length = len := by simp [Spec.Rsa.bytesAt]
  refine ⟨fun i hi => ⟨_, hr, VG.Proof.Bignum.X86_64.contains_byte p (by omega) hlen⟩, fun i hi => ?_,
    fun i hi => VG.Proof.Bignum.X86_64.out_scr hd (VG.Proof.Bignum.X86_64.contains_byte p (by omega) hlen)⟩
  simp [Spec.Rsa.bytesAt]

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_public(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8,
e_len = r9, input = [rsp + 8], input_len = [rsp + 16], scratch = [rsp + 24],
scratch_len = [rsp + 32])`. -/
def pubContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let inp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [n, e, inp, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint inp ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧
      (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧ Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOp (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-! ## Correctness -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem i2osp_zero' (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  rw [i2osp_zero]; simp

theorem setWidth_flag (c : Bool) : (BitVec.ofNat 64 c.toNat).setWidth 32 = if c then 1 else 0 := by
  cases c <;> rfl

/-- What `code` leaves: the result `r` and flag `c` of `fail` or `main`. -/
theorem written_of {m : Mem} {out : Addr} {k : Nat} {rax : BitVec 64} {nb eb xb : List Byte}
    (hnl : nb.length = k) {r : Nat} {c : Bool}
    (hb : Spec.Rsa.bytesAt m out k = Spec.Rsa.i2osp r k) (hr : rax = BitVec.ofNat 64 c.toNat)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true →
      c = decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb) ∧
      r = if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
        Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % Spec.Rsa.os2ip nb else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = false → c = false ∧ r = 0) :
    Spec.Rsa.written m out k (rax.setWidth 32) (Spec.Rsa.publicOp nb eb xb) := by
  unfold Spec.Rsa.publicOp
  rw [hnl, hr, VG.Proof.Bignum.X86_64.setWidth_flag]
  cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k
  · obtain ⟨rfl, rfl⟩ := hf hv
    simp only [hv, Bool.false_eq_true, ite_false, Spec.Rsa.written]
    exact ⟨trivial, by rw [hb, VG.Proof.Bignum.X86_64.i2osp_zero']⟩
  · obtain ⟨rfl, rfl⟩ := hc hv
    by_cases hx : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb
    · simp only [hv, hx, ite_true, decide_true, Spec.Rsa.encrypt, Option.map_some, Spec.Rsa.written]
      simp only [hx, ite_true] at hb
      exact ⟨trivial, by rw [hb, VG.Proof.Bignum.powMod_eq]⟩
    · simp only [hv, hx, ite_true, ite_false, decide_false, Spec.Rsa.encrypt, Option.map_none,
        Spec.Rsa.written, Bool.false_eq_true]
      simp only [hx, ite_false] at hb
      exact ⟨trivial, by rw [hb, VG.Proof.Bignum.X86_64.i2osp_zero']⟩

theorem bytesAt_eq (m : Mem) (p : Addr) (k : Nat) :
    Spec.Rsa.bytesAt m p k = (List.range k).map fun i => m (p + BitVec.ofNat 64 i) := rfl

theorem stackArgAddr_two (s : State) : stackArgAddr s 2 = stackArgAddr s 0 + BitVec.ofNat 64 16 := by
  simp only [stackArgAddr]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What `code` uses of its contract's precondition, for the working space
`B` (the third stack argument) of `Z` bytes and `m`'s length `k`. -/
structure CodeCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hL1 : 1 ≤ (s.gpr .r9).toNat
  hL2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hZ : 128 * (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat * 8
  hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8
  hsep : ∀ m', VG.Proof.Bignum.X86_64.Outside (stackArg s 2) 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0
  hnb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  heb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  hxb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
  hout : ∀ j < (s.gpr .rcx).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rcx).toNat, (stackArg s 3).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rcx).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem codeCtx_of {s : State} (h : pubContract.pre s) : VG.Proof.Bignum.X86_64.CodeCtx s := by
  simp only [VG.Proof.Bignum.X86_64.pubContract] at h
  obtain ⟨hsp, hrd, hwr, dOn, dOe, dOi, dOs, dOa, dns, des, dis, dsa, dRo, dRn, dRe, dRi, dRs, dRa,
    wO, wN, wE, wI, wS, hk, hol, hil, hL1, hL2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  refine ⟨hk1, hk2, hL1, hL2, by omega, hs,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp,
      by rw [VG.Proof.Bignum.X86_64.stackArgAddr_two]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := VG.Proof.Bignum.X86_64.out_scr dsa.symm (VG.Proof.Bignum.X86_64.contains_byte (stackArgAddr s 0) (i := b) (by omega) (by omega)); omega)),
    VG.Proof.Bignum.X86_64.src_of_region (by rw [hrd]; simp) (by omega) dns, VG.Proof.Bignum.X86_64.src_of_region (by rw [hrd]; simp) (by omega) des,
    VG.Proof.Bignum.X86_64.src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., VG.Proof.Bignum.X86_64.contains_byte _ (by omega) (by omega)⟩,
    fun j hj => VG.Proof.Bignum.X86_64.out_scr dOs (VG.Proof.Bignum.X86_64.contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := VG.Proof.Bignum.X86_64.contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨VG.Proof.Bignum.X86_64.out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact VG.Proof.Bignum.X86_64.contains_byte _ (by omega) (by omega))⟩

/-- After `entry` and the reloads of `m` and `k`, from `s`. -/
structure HeadPost (s t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t (stackArg s 2) ((stackArg s 3).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 2
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat
  saved : ∀ i < 6, VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * i) = s.gpr (saved.getD i .rax)
  hO : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi
  hN : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx
  hK : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rcx).toNat
  hE : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sE) = s.gpr .r8
  hL : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sElen) = BitVec.ofNat 64 (s.gpr .r9).toNat
  hIn : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 2) (8 * sIn) = stackArg s 0
  inScr : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `entry`, and `m` and `k` into `rdx` and `rcx`. -/
theorem head_ok {s : State} (c : VG.Proof.Bignum.X86_64.CodeCtx s) :
    WP isa (.block (VG.Impl.Bignum.X86_64.Public.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr))) s (VG.Proof.Bignum.X86_64.HeadPost s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 22, InRegions s.wr (VG.Proof.Bignum.X86_64.off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok rfl hw c.ha0 c.ha2 c.hsep) fun t₀ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK, hE, hL,
    hIn, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₀.ld (d := 8 * sK) (by unfold sK sFn; omega), hN, hK]) rfl) fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  refine ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, VG.Proof.Bignum.X86_64.ofNat_toNat64], fun i hi => ?_,
    by rw [hm]; exact hO, by rw [hm]; exact hN, by rw [hm, hK, VG.Proof.Bignum.X86_64.ofNat_toNat64], by rw [hm]; exact hE,
    by rw [hm, hL, VG.Proof.Bignum.X86_64.ofNat_toNat64], by rw [hm]; exact hIn, by rw [hm]; exact InScr.of_outside ho₀ (by omega),
    (k₀.trans k₁).mono (by decide)⟩
  rw [hm]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem mainPre_of {s t₁ t : State} (c : VG.Proof.Bignum.X86_64.CodeCtx s) (h : VG.Proof.Bignum.X86_64.HeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t) :
    MainPre t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8)
      (stackArg s 0) (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hdi : t.gpr .rdi = stackArg s 2 := (k.gpr (by decide)).trans h.rdi
  have hz : VG.Proof.Bignum.X86_64.slot (((s.gpr .rcx).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact
    { scr := h.scr.congr k.2.2, rdi := hdi, z := hz, k1 := hk1, k2 := hk2, hO := (by rw [hm]; exact h.hO),
      hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK), hE := (by rw [hm]; exact h.hE),
      hL := (by rw [hm]; exact h.hL), hIn := (by rw [hm]; exact h.hIn), n := c.hnb.congrK hi kk,
      x := c.hxb.congrK hi kk, e := c.heb.congrK hi kk, nl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, xl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      el := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, L1 := c.hL1, L2 := c.hL2,
      out := (fun j hj => by rw [kk.2.2]; exact c.hout j hj), outSep := c.houts }

/-- What `code` leaves, from what `fail` or `main` leaves. -/
theorem code_fin {s t₁ t₂ t : State} (c : VG.Proof.Bignum.X86_64.CodeCtx s) (h : VG.Proof.Bignum.X86_64.HeadPost s t₁) (hm : t₂.mem = t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t₂) {r : Nat} {cb : Bool}
    (hp : MainPost t₂ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) r cb)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true →
      cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) ∧
      r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) then
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false → cb = false ∧ r = 0) :
    gprPreserved s t ∧ pubContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩,
    VG.Proof.Bignum.X86_64.written_of (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) hp.bytes hp.rax hc hf⟩
  · have kk := h.keep.trans k
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.saved 0 (by decide)).trans (by rw [hm]; exact h.saved 0 (by decide))
    · exact (hp.saved 1 (by decide)).trans (by rw [hm]; exact h.saved 1 (by decide))
    · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
    · exact (hp.saved 2 (by decide)).trans (by rw [hm]; exact h.saved 2 (by decide))
    · exact (hp.saved 3 (by decide)).trans (by rw [hm]; exact h.saved 3 (by decide))
    · exact (hp.saved 4 (by decide)).trans (by rw [hm]; exact h.saved 4 (by decide))
    · exact (hp.saved 5 (by decide)).trans (by rw [hm]; exact h.saved 5 (by decide))
  · obtain ⟨hZx, hne⟩ := c.hret b hb
    rw [hp.frame _ hZx hne, hm, h.inScr _ hZx]

theorem code_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa VG.Impl.Bignum.X86_64.Public.code s t s' ∧ abiPreserved s s' ∧ pubContract.post s s' := by
  have c := VG.Proof.Bignum.X86_64.codeCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa VG.Impl.Bignum.X86_64.Public.code s fun s' => gprPreserved s s' ∧ pubContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  unfold VG.Impl.Bignum.X86_64.Public.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.head_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by
    rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [VG.X86_64.eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    have hpre := VG.Proof.Bignum.X86_64.mainPre_of c h₁ hm₂ k₂
    exact WP.mono (fail_ok hpre.scr hpre.rdi (by have := hpre.z; unfold VG.Proof.Bignum.X86_64.slot hdrBytes at this; omega)
      (by omega) (by omega) hpre.hO hpre.hK hpre.out hpre.outSep)
      fun t hp => VG.Proof.Bignum.X86_64.code_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (main_ok (VG.Proof.Bignum.X86_64.mainPre_of c h₁ hm₂ k₂) hv) fun t hp => VG.Proof.Bignum.X86_64.code_fin c h₁ hm₂ k₂ hp
      (fun _ => ⟨rfl, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CTExp`. -/
section

/-!
# `vg_rsa_public` on x86-64: the exponentiation is constant time but for `e`

`expBit` branches on a bit of `e`, which the header holds (`sV`): the runs
agree on it because they agree on `e` (`expBit_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem bitTest_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : VG.Proof.Bignum.X86_64.Good t B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {V : Nat} (hV : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) :
    WP isa (.block bitTest) t fun t' => t'.zf = some (decide (V / 128 % 2 = 0)) ∧ t'.mem = t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] t t' :=
  WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (V / 128 % 2 = 0)) ∧ t'.mem = t.mem) (by
    unfold bitTest
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * VG.Impl.Bignum.X86_64.Public.sV)
      (by have := hdr_lt_slot w 8 (show VG.Impl.Bignum.X86_64.Public.sV < 32 by decide); omega), hV, bit7 V hV']) rfl)
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

/-- The public data of a bit: the working space, the bit's byte (shifted) `V`. -/
structure BitPub where
  L : Lay
  V : Nat

/-- Before `expBit`: what its branch and its multiplications need. -/
def BitPre (p : VG.Proof.Bignum.X86_64.BitPub) (t : State) : Prop :=
  GoodL p.L t ∧ VG.Proof.Bignum.X86_64.word t.mem p.L.B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 p.V ∧ p.V < 2 ^ 62 ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧
    ((VG.Proof.Bignum.X86_64.word t.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aY) p.L.w < wv t.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) p.L.w ∧
    wv t.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aXm) p.L.w < wv t.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) p.L.w

/-- After the bit test. -/
def BitTested (p : VG.Proof.Bignum.X86_64.BitPub) (t : State) : Prop := VG.Proof.Bignum.X86_64.BitPre p t ∧ t.zf = some (decide (p.V / 128 % 2 = 0))

theorem pins_bitPre : Pins VG.Proof.Bignum.X86_64.BitPre [.rdi] := fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1

theorem mm_mid (M : Mont) {L : Lay} {t : State} {o a b : Nat} (hg : GoodL L t) (hw : 2 ≤ L.w) (hw' : L.w < 2 ^ 31)
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc)
    (d5 : o ≠ aN)
    (hinv : ((VG.Proof.Bignum.X86_64.word t.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv t.mem L.B (VG.Proof.Bignum.X86_64.slot L.w b) L.w < wv t.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN) L.w) (d6 : a ≠ aTmp := by decide)
    (d7 : b ≠ aTmp := by decide) :
    WP isa (M.mm o a b) t fun t' => GoodL L t' ∧
      wv t'.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN) L.w = wv t.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN) L.w ∧
      ((VG.Proof.Bignum.X86_64.word t'.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem L.B (VG.Proof.Bignum.X86_64.slot L.w o) L.w < wv t.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN) L.w ∧
      Arrays L.B L.w [aAcc, aTmp, o] t.mem t'.mem :=
  WP.mono (mmN_ok M hg.1 hg.2 hw hw' ho ha hb d1 d2 d3 d4 d5 rfl hinv hB d6 d7)
    fun _ ⟨g, n, i, lt, _, ar, _⟩ => ⟨⟨g, hg.2⟩, n, i, lt, ar⟩

/-- `expBit` leaks the same in two runs that agree on the bit. -/
theorem expBit_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.BitPre) VG.Impl.Bignum.X86_64.Public.expBit fun _ _ => True := by
  have hn : ∀ {L : Lay} {t : State}, GoodL L t → L.B.toNat + VG.Proof.Bignum.X86_64.slot L.w 8 ≤ 2 ^ 64 := fun hg => by
    have := hg.1.scr.nowrap; have := hg.2; omega
  unfold VG.Impl.Bignum.X86_64.Public.expBit
  -- The squaring.
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.BitPre) (two_map (·.L) (fun _ _ h => h.1)
    (montMul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)))
    fun p t h => WP.mono (VG.Proof.Bignum.X86_64.mm_mid Mont.base h.1 h.2.2.2.1 h.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) h.2.2.2.2.2.1 h.2.2.2.2.2.2.1)
      fun t' ⟨g, n, i, lt, ar⟩ => ⟨g, by rw [ar.hslot (by decide)]; exact h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, i, by rw [n]; exact lt,
        by rw [n, ar.wv_of_not_mem (by decide) (by decide) (hn h.1)]; exact h.2.2.2.2.2.2.2⟩) ?_
  -- The bit.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.BitTested) _ VG.Proof.Bignum.X86_64.pins_bitPre (by taint_decide) fun p t h =>
    WP.mono (VG.Proof.Bignum.X86_64.bitTest_ok h.1.1 h.1.2 h.2.1 (by have := h.2.2.1; omega)) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨⟨⟨h.1.1.scr.congr k.2.2, (k.gpr (by decide)).trans h.1.1.rdi, hm ▸ h.1.1.hdr⟩, h.1.2⟩,
        hm ▸ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hm ▸ h.2.2.2.2.2.1, hm ▸ h.2.2.2.2.2.2.1,
        hm ▸ h.2.2.2.2.2.2.2⟩, hz⟩) ?_
  -- The multiplication, if the bit is set.
  refine RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.BitPub) t => GoodL p.L t) (two_ite (fun p s₁ s₂ h₁ h₂ => by
    simp only [VG.X86_64.eval, h₁.2, h₂.2]) ?_ ?_) ?_
  · refine two_post (Ψ := fun (p : VG.Proof.Bignum.X86_64.BitPub) t => GoodL p.L t) (two_map (·.L) (fun _ _ h => h.1.1.1)
      (montMul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)))
      fun p t h => WP.mono (VG.Proof.Bignum.X86_64.mm_mid Mont.base h.1.1.1 h.1.1.2.2.2.1 h.1.1.2.2.2.2.1 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) h.1.1.2.2.2.2.2.1
        h.1.1.2.2.2.2.2.2.2) fun _ h' => h'.1
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun _ _ h => h.1.1.1) hp
  -- The next bit.
  exact two_taint _ (fun (p : VG.Proof.Bignum.X86_64.BitPub) s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁ h₂) (by taint_decide)

/-- The `ne` condition after a count that sets ZF when `j + 1 = n`. -/
theorem eval_ne_count {s : State} {j n : Nat} (hj : j < n) (hz : s.zf = some (decide (j + 1 = n))) :
    isa.eval .ne s = some (decide (j + 1 < n)) := by
  simp only [VG.X86_64.eval, hz, Option.map_some, Option.some.injEq]
  by_cases h : j + 1 = n
  · simp [h]
  · simp only [h, decide_false, Bool.not_false]; exact (decide_eq_true (by omega)).symm

/-! ## The bits of a byte -/

/-- The public data of the bits of a byte: the working space, `m`, the
exponent so far `E` and the byte `v`. -/
structure BitsPub where
  L : Lay
  N : Nat
  E : Nat
  v : Nat

/-- After `j` bits of a byte. -/
def BitsInv (p : VG.Proof.Bignum.X86_64.BitsPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), BitInv t₀ p.L.B p.L.Z p.L.w p.L.minv p.N X x p.E p.v j s ∧
    VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * p.L.w)) p.N ∧ X < p.N ∧
    X % p.N = x * 2 ^ (64 * p.L.w) % p.N ∧ p.v < 256

theorem bitsInv_pre {p : VG.Proof.Bignum.X86_64.BitsPub} {j : Nat} {s : State} (hj : j < 8) (h : VG.Proof.Bignum.X86_64.BitsInv p j s) :
    VG.Proof.Bignum.X86_64.BitPre ⟨p.L, p.v * 2 ^ j⟩ s := by
  obtain ⟨t₀, X, x, hI, hZ, hw, hw', -, hXN, -, hv⟩ := h
  obtain ⟨Y, hY, hYN, -⟩ := hI.y
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨⟨hI.ctx.good, hZ⟩, hI.v, show p.v * 2 ^ j < 2 ^ 62 by have := Nat.mul_le_mul_left p.v hp; omega, hw, hw', hI.ctx.inv,
    by rw [hY, hI.ctx.n]; exact hYN, by rw [hI.ctx.x, hI.ctx.n]; exact hXN⟩

/-- The eight bits of a byte leak the same in runs that agree on it. -/
theorem bits_ct : RelCT isa (Two fun p s => 0 < 8 ∧ VG.Proof.Bignum.X86_64.BitsInv p 0 s) (.loop VG.Impl.Bignum.X86_64.Public.expBit .ne)
    (Two fun p s => VG.Proof.Bignum.X86_64.BitsInv p 8 s) :=
  two_loop (Φ := VG.Proof.Bignum.X86_64.BitsInv) (fun _ => 8)
    (two_map (fun q : VG.Proof.Bignum.X86_64.BitsPub × Nat => (⟨q.1.L, q.1.v * 2 ^ q.2⟩ : VG.Proof.Bignum.X86_64.BitPub))
      (fun _ _ h => VG.Proof.Bignum.X86_64.bitsInv_pre h.1 h.2) VG.Proof.Bignum.X86_64.expBit_ct)
    fun _ _ _ hj ⟨t₀, X, x, hI, hZ, hw, hw', hR, hXN, hXc, hv⟩ =>
      WP.mono (bitStep_ok hZ hw hw' hR hXN hXc hv hj hI) fun _ ⟨hz, hI'⟩ =>
        ⟨VG.Proof.Bignum.X86_64.eval_ne_count hj hz, fun _ => ⟨t₀, X, x, hI', hZ, hw, hw', hR, hXN, hXc, hv⟩,
          fun h => h ▸ ⟨t₀, X, x, hI', hZ, hw, hw', hR, hXN, hXc, hv⟩⟩

/-! ## The bytes of `e` -/

/-- The public data of the exponentiation: the working space, `m`, and the
`len` bytes `eb` of `e` at `ep`. -/
structure EPub where
  L : Lay
  N : Nat
  ep : Addr
  len : Nat
  eb : List Byte

/-- What the exponentiation's steps need of the bytes of `e`, from `t₀`. -/
def ESrc (a : VG.Proof.Bignum.X86_64.EPub) (t₀ : State) : Prop :=
  a.eb.length = a.len ∧ a.len < 2 ^ 31 ∧
    (∀ i < a.len, InRegions (t₀.rd ++ t₀.wr) (a.ep + BitVec.ofNat 64 i) 1) ∧
    (∀ i (_ : i < a.len), t₀.mem (a.ep + BitVec.ofNat 64 i) = a.eb.getD i 0) ∧
    (∀ i < a.len, a.L.Z ≤ VG.Proof.Bignum.X86_64.ofs a.L.B (a.ep + BitVec.ofNat 64 i))

/-- The working space's and `m`'s facts every step needs. -/
def EFacts (a : VG.Proof.Bignum.X86_64.EPub) (X x : Nat) : Prop :=
  VG.Proof.Bignum.X86_64.slot a.L.w 8 ≤ a.L.Z ∧ 2 ≤ a.L.w ∧ a.L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * a.L.w)) a.N ∧ X < a.N ∧
    X % a.N = x * 2 ^ (64 * a.L.w) % a.N

/-- After `i` bytes of `e`. -/
def BytesInv (a : VG.Proof.Bignum.X86_64.EPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), VG.Proof.Bignum.X86_64.ByteInv t₀ a.L.B a.L.Z a.L.w a.L.minv a.N X x a.ep a.len a.eb i s ∧
    VG.Proof.Bignum.X86_64.EFacts a X x ∧ VG.Proof.Bignum.X86_64.ESrc a t₀

theorem ESrc.bytes {a : VG.Proof.Bignum.X86_64.EPub} {t₀ : State} (h : VG.Proof.Bignum.X86_64.ESrc a t₀) :
    ∀ i (hi : i < a.len), t₀.mem (a.ep + BitVec.ofNat 64 i) = a.eb[i]'(by have := h.1; omega) :=
  fun i hi => by rw [h.2.2.2.1 i hi]; simp [List.getD_eq_getElem?_getD, show i < a.eb.length by have := h.1; omega]

/-- After `byteHead`'s loads. -/
def HeadMid (q : VG.Proof.Bignum.X86_64.EPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.BytesInv q.1 q.2 s ∧ s.gpr .rax = q.1.ep ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

/-- The bits of byte `i`. -/
def bitsPub (q : VG.Proof.Bignum.X86_64.EPub × Nat) : VG.Proof.Bignum.X86_64.BitsPub := ⟨q.1.L, q.1.N, VG.Proof.Bignum.X86_64.pre q.1.eb q.2, (q.1.eb.getD q.2 0).toNat⟩

theorem pins_bytes : Pins (fun (q : VG.Proof.Bignum.X86_64.EPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.BytesInv q.1 q.2 s) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]

theorem pins_headMid : Pins VG.Proof.Bignum.X86_64.HeadMid [.rdi, .rax, .rcx] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, ⟨_, _, _, i₁, _⟩, a₁, c₁⟩ := h₁
  obtain ⟨-, ⟨_, _, _, i₂, _⟩, a₂, c₂⟩ := h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of `e` leaks the same in runs that agree on `e`. -/
theorem byteBody_ct : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.EPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.BytesInv q.1 q.2 s)
    (.seq (.block byteHead) (.seq (.loop VG.Impl.Bignum.X86_64.Public.expBit .ne) (.block byteNext))) fun _ _ => True := by
  rw [byteHead_eq]
  have w₁ : ∀ (q : VG.Proof.Bignum.X86_64.EPub × Nat) s, q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.BytesInv q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))]) s (VG.Proof.Bignum.X86_64.HeadMid q) := by
    rintro q s ⟨hi, t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (byteHead1_ok hf.1 hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, X, x, h3, hf, hsrc⟩, h1, h2⟩
  have w₂ : ∀ (q : VG.Proof.Bignum.X86_64.EPub × Nat) s, VG.Proof.Bignum.X86_64.HeadMid q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax,
        .mov32 .rax (.imm 8), .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax]) s fun t => 0 < 8 ∧ VG.Proof.Bignum.X86_64.BitsInv (VG.Proof.Bignum.X86_64.bitsPub q) 0 t := by
    rintro q s ⟨hi, ⟨t₀, X, x, hI, hf, hsrc⟩, hax, hcx⟩
    refine WP.mono (byteHead2_ok hf.1 hsrc.1 hi hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI hax hcx)
      fun t ⟨_, _, hB⟩ => ⟨by decide, t, X, x, ?_, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
        hf.2.2.2.2.2, ?_⟩
    · simp only [VG.Proof.Bignum.X86_64.bitsPub, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show q.2 < q.1.eb.length by have := hsrc.1; omega), Option.getD_some]
      exact hB
    · simp only [VG.Proof.Bignum.X86_64.bitsPub]; exact (List.getD q.1.eb q.2 0).isLt
  have h₁ : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.EPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.BytesInv q.1 q.2 s)
      (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))]) (Two VG.Proof.Bignum.X86_64.HeadMid) :=
    two_piece _ VG.Proof.Bignum.X86_64.pins_bytes (by taint_decide) w₁
  have h₂ : RelCT isa (Two VG.Proof.Bignum.X86_64.HeadMid) (.block [.movzx8 .rax { base := .rax, index := some .rcx },
      .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax, .mov32 .rax (.imm 8), .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax])
      (Two fun q s => 0 < 8 ∧ VG.Proof.Bignum.X86_64.BitsInv (VG.Proof.Bignum.X86_64.bitsPub q) 0 s) :=
    two_piece _ VG.Proof.Bignum.X86_64.pins_headMid (by taint_decide) w₂
  have h₃ : RelCT isa (Two fun (p : VG.Proof.Bignum.X86_64.BitsPub) s => VG.Proof.Bignum.X86_64.BitsInv p 8 s) (.block byteNext) fun _ _ => True :=
    two_taint [.rdi] (fun (_ : VG.Proof.Bignum.X86_64.BitsPub) s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq h₁ h₂))
    (RelCT.seq (two_map VG.Proof.Bignum.X86_64.bitsPub (fun _ _ h => h) VG.Proof.Bignum.X86_64.bits_ct) h₃)

/-- Before `expLoop`. -/
def ExpPre (a : VG.Proof.Bignum.X86_64.EPub) (s : State) : Prop :=
  ∃ X x Y : Nat, ExpCtx s a.L.B a.L.Z a.L.w a.L.minv a.N X ∧ VG.Proof.Bignum.X86_64.EFacts a X x ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aY) a.L.w = Y ∧ Y < a.N ∧ Y % a.N = 2 ^ (64 * a.L.w) % a.N ∧
    VG.Proof.Bignum.X86_64.word s.mem a.L.B (8 * sE) = a.ep ∧ VG.Proof.Bignum.X86_64.word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    1 ≤ a.len ∧ VG.Proof.Bignum.X86_64.ESrc a s

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem expLoop_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.ExpPre) VG.Impl.Bignum.X86_64.Public.expLoop (Two fun a s => VG.Proof.Bignum.X86_64.BytesInv a a.len s) := by
  unfold VG.Impl.Bignum.X86_64.Public.expLoop
  refine RelCT.seq (two_piece (Ψ := fun a s => 0 < a.len ∧ VG.Proof.Bignum.X86_64.BytesInv a 0 s) [.rdi]
    (fun _ _ _ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]) (by taint_decide) ?_) ?_
  · rintro a s ⟨X, x, Y, hc, hf, hY, hYN, hYc, he, hlen, hL1, hsrc⟩
    exact WP.mono (expInit_ok (x := x) (eb := a.eb) hc hf.1 hY hYN hYc he hlen) fun t h =>
      ⟨hL1, s, X, x, h, hf, hsrc⟩
  · refine two_loop (Φ := VG.Proof.Bignum.X86_64.BytesInv) (fun a => a.len) VG.Proof.Bignum.X86_64.byteBody_ct ?_
    rintro a i s hi ⟨t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (byte_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hsrc.1 hsrc.2.1 hi
      hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI) fun s' ⟨hz, hI'⟩ =>
        ⟨VG.Proof.Bignum.X86_64.eval_ne_count hi hz, fun _ => ⟨t₀, X, x, hI', hf, hsrc⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hsrc⟩⟩

/-! ## The exponentiation phase -/

/-- Before the exponentiation phase (`expPhase_ok`'s hypotheses). -/
def EPhasePre (a : VG.Proof.Bignum.X86_64.EPub) (s : State) : Prop :=
  ∃ X : Nat, VG.Proof.Bignum.X86_64.Good s a.L.B a.L.Z a.L.w a.L.minv ∧ VG.Proof.Bignum.X86_64.slot a.L.w 8 ≤ a.L.Z ∧ 2 ≤ a.L.w ∧ a.L.w < 2 ^ 31 ∧
    a.N % 2 = 1 ∧ 1 < a.N ∧ wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aN) a.L.w = a.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aN)).toNat * a.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aX) a.L.w = X ∧ wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aOne) a.L.w = 1 ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aR2) a.L.w < a.N ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aR2) a.L.w % a.N = 2 ^ (64 * a.L.w) * 2 ^ (64 * a.L.w) % a.N ∧
    VG.Proof.Bignum.X86_64.word s.mem a.L.B (8 * sE) = a.ep ∧ VG.Proof.Bignum.X86_64.word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    a.eb.length = a.len ∧ 1 ≤ a.len ∧ a.len < 2 ^ 31 ∧ Src s a.L.B a.L.Z a.ep a.eb

/-- After `Y := R`. -/
def EPhase1 (a : VG.Proof.Bignum.X86_64.EPub) (s : State) : Prop :=
  ∃ (X : Nat) (σ : State), VG.Proof.Bignum.X86_64.EPhasePre a σ ∧ VG.Proof.Bignum.X86_64.Good s a.L.B a.L.Z a.L.w a.L.minv ∧
    wv σ.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aX) a.L.w = X ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aN) a.L.w = a.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aN)).toNat * a.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aY) a.L.w < a.N ∧
    wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aY) a.L.w % a.N = 2 ^ (64 * a.L.w) % a.N ∧
    Frm a.L.B (expPhaseRanges a.L.w) σ.mem s.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs σ s

theorem src_esrc {a : VG.Proof.Bignum.X86_64.EPub} {s : State} (h : Src s a.L.B a.L.Z a.ep a.eb) (hl : a.eb.length = a.len)
    (hl' : a.len < 2 ^ 31) : VG.Proof.Bignum.X86_64.ESrc a s :=
  ⟨hl, hl', fun i hi => h.rd i (by omega), fun i hi => by
    rw [h.val i (by omega)]; simp [List.getD_eq_getElem?_getD, show i < a.eb.length by omega],
    fun i hi => h.out i (by omega)⟩

/-- The exponentiation phase leaks the same in runs that agree on `e`. -/
theorem expPhase_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.EPhasePre) (seqs expSteps) fun _ _ => True := by
  unfold expSteps
  have mmct : ∀ {o a b : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}, o < 8 → a < 8 → b < 8 →
      (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc).isSome = true →
      RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.EPub) s => GoodL q.L s) (mm o a b) fun _ _ => True :=
    fun ho ha hb h => two_map (·.L) (fun _ _ h => h) (montMul_ct (by decide) (by decide) (by decide) ho ha hb h)
  -- `Y := R`.
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.EPhase1) (two_map id (fun a s ⟨_, hg, hZ, _⟩ => ⟨hg, hZ⟩)
    (mmct (by decide) (by decide) (by decide) (by taint_decide))) ?_) ?_
  · rintro a s ⟨X, hg, hZ, hw, hw', hodd, hN1, hn, hinv, hX, hone, hlt2, hr2, he, hlen, hL, hL1, hL', heb⟩
    have hR : Nat.Coprime (2 ^ (64 * a.L.w)) a.N := VG.Proof.Bignum.coprime_pow2 hodd _
    refine WP.mono (mmN_ok Mont.base (o := aY) (a := aR2) (b := aOne) hg hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn hinv (by rw [hone]; exact hN1))
      fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ⟨X, s, ⟨X, hg, hZ, hw, hw', hodd, hN1, hn, hinv, hX, hone,
        hlt2, hr2, he, hlen, hL, hL1, hL', heb⟩, hg₁, hX, hn₁, hinv₁, hlt₁, ?_, Frm.ep_of_arrays ha₁ (by simp), k₁⟩
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₁, hone, Nat.mul_one, hr2]
  -- `X := x R`.
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.ExpPre) (two_map id (fun a s ⟨_, σ, hσ, hg, _⟩ =>
      ⟨hg, hσ.choose_spec.2.1⟩) (mmct (by decide) (by decide) (by decide) (by taint_decide))) ?_) ?_
  · rintro a s ⟨X, σ, ⟨X', hg, hZ, hw, hw', hodd, hN1, hn, hinv, hX', hone, hlt2, hr2, he, hlen, hL, hL1, hL',
      heb⟩, hg₁, hX, hn₁, hinv₁, hlt₁, hY₁, f₁, k₁⟩
    have hn' : a.L.B.toNat + VG.Proof.Bignum.X86_64.slot a.L.w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
    have hR : Nat.Coprime (2 ^ (64 * a.L.w)) a.N := VG.Proof.Bignum.coprime_pow2 hodd _
    refine WP.mono (mmN_ok Mont.base (o := aXm) (a := aX) (b := aR2) hg₁ hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn₁ hinv₁
      (by rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlt2))
      fun t₂ ⟨hg₂, hn₂, hinv₂, hlt₂, hm₂, ha₂, k₂⟩ => ?_
    rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide),
      f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide), hX] at hm₂
    have hX₂ : wv t₂.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aXm) a.L.w % a.N = X * 2 ^ (64 * a.L.w) % a.N := by
      apply VG.Proof.Bignum.mont_cancel hR
      rw [hm₂, Nat.mul_mod, hr2, ← Nat.mul_mod, Nat.mul_assoc]
    have hY₂ : wv t₂.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aY) a.L.w = wv s.mem a.L.B (VG.Proof.Bignum.X86_64.slot a.L.w aY) a.L.w :=
      ha₂.wv_of_not_mem (by decide) (by decide) hn'
    have f₁₂ := f₁.trans (Frm.ep_of_arrays ha₂ (by simp))
    have hin : InScr a.L.B a.L.Z σ.mem t₂.mem :=
      InScr.of_frm f₁₂ fun r hr => (expPhaseRanges_le _ r hr).trans hZ
    have heb₂ := heb.congrK hin (k₁.trans k₂)
    exact ⟨_, X, _, ⟨hg₂, hn₂, hinv₂, rfl⟩, ⟨hZ, hw, hw', hR, hlt₂, hX₂⟩, hY₂, hlt₁, hY₁,
      by rw [f₁₂.ep_hdr (by decide) (by decide) (by decide) (by decide)]; exact he,
      by rw [f₁₂.ep_hdr (by decide) (by decide) (by decide) (by decide)]; exact hlen, hL1,
      VG.Proof.Bignum.X86_64.src_esrc heb₂ hL hL'⟩
  -- The exponentiation, and `Y R⁻¹`.
  exact RelCT.seq VG.Proof.Bignum.X86_64.expLoop_ct (two_map id (fun a s ⟨_, _, _, hI, hf, _⟩ => ⟨hI.ctx.good, hf.1⟩)
    (mmct (by decide) (by decide) (by decide) (by taint_decide)))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CTR2`. -/
section

/-!
# `vg_rsa_public` on x86-64: `R² mod m` is constant time but for `m`

`double` and `doubles` (`doubles_ct`), whose count is public, and the
computation of `R² mod m` (`r2_ct`), which branches on the top word of the
public modulus.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- `double`'s loads. -/
def dblHead (mo acc tmp o : Nat) : List Instr :=
  [.mov .rbx (.mem (hdr (sArr o))), .mov .r10 (.mem (hdr (sArr mo))), .mov .r8 (.mem (hdr (sArr acc))),
    .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr tmp))), .mov32 .rbp (.imm 0)]

/-- After `double`'s loads. -/
def DblHeadL (mo acc tmp o : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w mo) ∧
    t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w acc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w tmp)

theorem dblHead_ok {L : Lay} {t : State} (hg : GoodL L t) {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8)
    (htmp : tmp < 8) (ho : o < 8) : WP isa (.block (VG.Proof.Bignum.X86_64.dblHead mo acc tmp o)) t (VG.Proof.Bignum.X86_64.DblHeadL mo acc tmp o L) := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega)
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rsi, .rbp] (Q := VG.Proof.Bignum.X86_64.DblHeadL mo acc tmp o L) ?_ rfl)
    fun t' h => h.1
  unfold VG.Proof.Bignum.X86_64.dblHead VG.Proof.Bignum.X86_64.DblHeadL
  xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr o) (by unfold sArr; omega),
    hl (sArr mo) (by unfold sArr; omega), hl (sArr acc) (by unfold sArr; omega), hl sW (by decide),
    hl (sArr tmp) (by unfold sArr; omega), hg.1.hdr.harr o ho, hg.1.hdr.harr mo hmo, hg.1.hdr.harr acc hacc,
    hg.1.hdr.harr tmp htmp, hg.1.hdr.hw]

theorem pins_dblHead (mo acc tmp o : Nat) : Pins (VG.Proof.Bignum.X86_64.DblHeadL mo acc tmp o) [.rbx, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

/-- `double` leaks the same in runs with the same working space. -/
theorem double_ct {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Proof.Bignum.X86_64.dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodL) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece _ pins_good h fun _ _ hg => VG.Proof.Bignum.X86_64.dblHead_ok hg hmo hacc htmp ho)
    (two_taint _ (VG.Proof.Bignum.X86_64.pins_dblHead mo acc tmp o) (by taint_decide))

/-- The public data of `doubles`: the working space and the count. -/
structure DblPub where
  L : Lay
  c : Nat

/-- What `doubles` keeps, after `j` doublings. -/
def DblsAt (mo acc tmp o sl : Nat) (p : VG.Proof.Bignum.X86_64.DblPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (O N : Nat), DblsInv σ p.L.B p.L.Z p.L.w p.L.minv mo acc tmp o sl p.c O N j t ∧
    VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ p.c < 2 ^ 31 ∧ 0 < N

theorem dblsAt_good {mo acc tmp o sl : Nat} {p : VG.Proof.Bignum.X86_64.DblPub} {j : Nat} {t : State}
    (h : VG.Proof.Bignum.X86_64.DblsAt mo acc tmp o sl p j t) : GoodL p.L t :=
  let ⟨_, _, _, hI, hZ, _⟩ := h; ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doubles_ct {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Proof.Bignum.X86_64.dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : VG.Proof.Bignum.X86_64.DblPub) s => GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧
      p.c < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w o) p.L.w < wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) (Two fun p s => VG.Proof.Bignum.X86_64.DblsAt mo acc tmp o sl p p.c s) := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ VG.Proof.Bignum.X86_64.DblsAt mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) h' ?_) ?_
  · rintro p s ⟨hg, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.rdi hg.1.hdr hg.2 hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, _, _, hI, hg.2, hw, hw', hc', by omega⟩
  refine two_loop (Φ := VG.Proof.Bignum.X86_64.DblsAt mo acc tmp o sl) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : VG.Proof.Bignum.X86_64.DblPub × Nat) s => GoodL q.1.L s)
      (two_map (·.1.L) (fun _ _ h => VG.Proof.Bignum.X86_64.dblsAt_good h.2) (VG.Proof.Bignum.X86_64.double_ct hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) h'')
    rintro ⟨p, j⟩ s ⟨hj, σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨VG.Proof.Bignum.X86_64.eval_ne_count hj hz, fun _ => ⟨σ, O, N, hI', hZ, hw, hw', hc', hN0⟩,
        fun e => e ▸ ⟨σ, O, N, hI', hZ, hw, hw', hc', hN0⟩⟩

/-! ## Squarings -/

/-- What a squaring of `[aR2]` needs. -/
def SqPre (L : Lay) (s : State) : Prop :=
  GoodL L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧
    ((VG.Proof.Bignum.X86_64.word s.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aR2) L.w < wv s.mem L.B (VG.Proof.Bignum.X86_64.slot L.w aN) L.w

theorem sqs_ct (M : Mont) (n : Nat) : RelCT isa (Two VG.Proof.Bignum.X86_64.SqPre) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))
    fun _ _ => True := by
  have one : RelCT isa (Two VG.Proof.Bignum.X86_64.SqPre) (M.mm aR2 aR2 aR2) fun _ _ => True :=
    two_map id (fun _ _ h => h.1) (M.ctL (.inl ⟨rfl, rfl, rfl⟩))
  induction n with
  | zero => exact one
  | succ n ih =>
    show RelCT isa (Two VG.Proof.Bignum.X86_64.SqPre) (.seq (M.mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))) _
    refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.SqPre) one fun L s ⟨hg, hw, hw', hinv, hlt⟩ =>
      WP.mono (VG.Proof.Bignum.X86_64.mm_mid M hg hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hinv hlt) fun t ⟨g, n, i, lt, _⟩ => ⟨g, hw, hw', i, by rw [n]; exact lt⟩) ih

/-! ## `R² mod m` -/

/-- The public data of `R² mod m`: the working space and `m`. -/
structure R2Pub where
  L : Lay
  N : Nat

/-- The top word of `m`. -/
def R2Pub.top (p : VG.Proof.Bignum.X86_64.R2Pub) : Nat := p.N / 2 ^ (64 * (p.L.w - 1))

/-- The doublings' count, `64 - j + w` for the top bit `j` of the top word. -/
def R2Pub.cnt (p : VG.Proof.Bignum.X86_64.R2Pub) : Nat := 64 - p.top.log2 + p.L.w

/-- `r2_ok`'s hypotheses. -/
def R2Pre (p : VG.Proof.Bignum.X86_64.R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) p.L.w = p.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ s.gpr .r10 = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N

/-- What the top word of `m` gives. -/
theorem r2top {p : VG.Proof.Bignum.X86_64.R2Pub} {s : State} (hw : 2 ≤ p.L.w) (hn : wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) p.L.w = p.N)
    (hodd : p.N % 2 = 1) (hlo : 2 ^ (64 * (p.L.w - 1)) ≤ p.N) :
    (VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top ∧ 0 < p.top ∧ p.top < 2 ^ 64 ∧
      p.top.log2 < 64 ∧ 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1)) < p.N := by
  have hsplit : p.N = p.N % 2 ^ (64 * (p.L.w - 1)) +
      2 ^ (64 * (p.L.w - 1)) * (VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
    have e : wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) (p.L.w - 1 + 1) = p.N := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p.L.w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) (p.L.w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hT : (VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top := by
    unfold R2Pub.top
    have hP := Nat.two_pow_pos (64 * (p.L.w - 1))
    have := Nat.mod_lt p.N hP
    rw [Nat.div_eq_of_lt_le (k := (VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN + 8 * (p.L.w - 1))).toNat) ?_ ?_]
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  rw [hT] at hsplit
  have hT0 : 0 < p.top := by
    rcases Nat.eq_zero_or_pos p.top with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsplit
      have := Nat.mod_lt p.N (Nat.two_pow_pos (64 * (p.L.w - 1))); omega
    · exact h
  have hT1 : p.top < 2 ^ 64 := hT ▸ BitVec.isLt _
  exact ⟨hT, hT0, hT1, (Nat.log2_lt (by omega)).mpr hT1,
    start_lt hw hodd hsplit (Nat.log2_self_le (n := p.top) (by omega))⟩

theorem R2Pre.top {p : VG.Proof.Bignum.X86_64.R2Pub} {s : State} (h : VG.Proof.Bignum.X86_64.R2Pre p s) :
    (VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top ∧ 0 < p.top ∧ p.top < 2 ^ 64 ∧
      p.top.log2 < 64 ∧ 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1)) < p.N :=
  VG.Proof.Bignum.X86_64.r2top h.2.1 h.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

theorem pins_r2Pre : Pins VG.Proof.Bignum.X86_64.R2Pre [.r10, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]

/-- After the top word's load. -/
def R2a (p : VG.Proof.Bignum.X86_64.R2Pub) (s : State) : Prop := VG.Proof.Bignum.X86_64.R2Pre p s ∧ s.gpr .rax = BitVec.ofNat 64 p.top

/-- After `topBit`. -/
def R2b (p : VG.Proof.Bignum.X86_64.R2Pub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.R2Pre p s ∧ s.gpr .rdx = BitVec.ofNat 64 (2 ^ p.top.log2) ∧ s.gpr .rcx = BitVec.ofNat 64 (64 - p.top.log2)

/-- Before and after `setWord`'s load. -/
def R2c (p : VG.Proof.Bignum.X86_64.R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) p.L.w = p.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ s.gpr .rcx = BitVec.ofNat 64 (p.L.w - 1) ∧
    s.gpr .rdx = BitVec.ofNat 64 (2 ^ p.top.log2) ∧
    VG.Proof.Bignum.X86_64.word s.mem p.L.B (8 * sCnt) = BitVec.ofNat 64 (64 - p.top.log2) ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N

/-- After the start, `2^(b - 1)`. -/
def R2d (p : VG.Proof.Bignum.X86_64.R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN) p.L.w = p.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    VG.Proof.Bignum.X86_64.word s.mem p.L.B (8 * sCnt) = BitVec.ofNat 64 (64 - p.top.log2) ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N ∧
    wv s.mem p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aR2) p.L.w = 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1))

/-- Before the doublings. -/
def R2e (p : VG.Proof.Bignum.X86_64.R2Pub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.R2d p s ∧ s.gpr .rcx = BitVec.ofNat 64 p.cnt

theorem pins_rdi_of {α : Type} {Φ : α → State → Prop} (L : α → Lay) (h : ∀ a s, Φ a s → GoodL (L a) s) :
    Pins Φ [.rdi] := fun a s₁ s₂ h₁ h₂ => pins_good (L a) s₁ s₂ (h a s₁ h₁) (h a s₂ h₂)

theorem setWord_eq (o : Nat) (i : Reg) : setWord o i =
    .seq (.block [.mov .r8 (.mem (hdr (sArr o)))]) (.seq zeroAccLoop (.block [.store (ix .r8 i) .rdx])) := rfl

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem r2_ct (M : Mont) : RelCT isa (Two VG.Proof.Bignum.X86_64.R2Pre) (seqs (r2Steps M)) fun _ _ => True := by
  unfold r2Steps
  -- The top word.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.R2a) _ VG.Proof.Bignum.X86_64.pins_r2Pre (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 p.top ∧ t.mem = s.mem) (by
      xrun [State.ea, ix, addrm8 h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 (by have := h.2.1; omega),
        h.1.1.scr.ld (show VG.Proof.Bignum.X86_64.slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega)]
      rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl) fun t ⟨⟨hax, hm⟩, k⟩ => ⟨?_, hax⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  -- Its top bit.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.R2b) [.rax] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, hax⟩
    obtain ⟨-, hT0, hT1, -⟩ := h.top
    refine WP.mono (topBit_ok hax hT0 hT1) fun t ⟨hdx, hcx, hm, k⟩ => ⟨?_, hdx, hcx⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  -- The count into the header, and the start's word index.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.R2c) _ (VG.Proof.Bignum.X86_64.pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s ⟨⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩, hdx, hcx⟩
    have hn := hg.1.scr.nowrap
    have hn' : p.L.B.toNat + VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.2; omega
    have h0 := hdr_lt_slot p.L.w 0 (show sCnt < 32 by decide)
    have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (p.L.w - 1) ∧
        t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off p.L.B (8 * sCnt)) (BitVec.ofNat 64 (64 - p.top.log2))) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.scr.st (d := 8 * sCnt) (by have := hg.2; omega),
        hcx, h12, ofNat64_pred (show 1 ≤ p.L.w by omega) (by omega)]) rfl) fun t ⟨⟨hcx', hm⟩, k⟩ => ?_
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi,
      by rw [hm]; exact Hdr.store hg.1.hdr (by decide) (by decide) _⟩, hg.2⟩, hw, hw',
      by rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) hn']; exact hN,
      by rw [hm, hdrStore_word _ _ _ (by decide) (by decide) hn']; exact hinv,
      (k.gpr (by decide)).trans h12, hcx', (k.gpr (by decide)).trans hdx, by rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self],
      hodd, hlo⟩
  -- The start.
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.R2d) ?_ ?_) ?_
  · rw [VG.Proof.Bignum.X86_64.setWord_eq]
    refine RelCT.seq (two_piece (Ψ := fun p s => VG.Proof.Bignum.X86_64.R2c p s ∧ s.gpr .r8 = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aR2)) _
      (VG.Proof.Bignum.X86_64.pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) fun p s h => ?_) (two_taint [.r8, .r12, .rcx]
        (fun p s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [h₁.2, h₂.2]
          · rw [h₁.1.2.2.2.2.2.1, h₂.1.2.2.2.2.2.1]
          · rw [h₁.1.2.2.2.2.2.2.1, h₂.1.2.2.2.2.2.2.1]) (by taint_decide))
    have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.L.B (8 * sArr aR2)) 8 :=
      h.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aR2 < 32 by decide); have := h.1.2; omega)
    refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aR2) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.1.1.rdi, hdrOff, hl, h.1.1.hdr.harr aR2 (by decide)]) rfl)
      fun t ⟨⟨h8, hm⟩, k⟩ => ⟨?_, h8⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, hcx, hdx, hcnt, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx,
      (k.gpr (by decide)).trans hdx, hm ▸ hcnt, hodd, hlo⟩
  · intro p s ⟨hg, hw, hw', hN, hinv, h12, hcx, hdx, hcnt, hodd, hlo⟩
    obtain ⟨-, -, -, hL, -⟩ := VG.Proof.Bignum.X86_64.r2top (s := s) hw hN hodd hlo
    have hn' : p.L.B.toNat + VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
    refine WP.mono (setWord_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 h12 (by omega) (by omega) (o := aR2) (by decide)
      (ri := .rcx) (by decide) (i := p.L.w - 1) (by omega) hcx) fun t ⟨hv, ho, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (Nat.le_refl _)
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hL)] at hv
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hg.2⟩, hw, hw',
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv,
      by rw [ha.hslot (by decide)]; exact hcnt, hodd, hlo, hv⟩
  -- The count of doublings.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.R2e) _ (VG.Proof.Bignum.X86_64.pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hg, hw, hw', hN, hinv, hcnt, hodd, hlo, hv⟩ := h
    have h0 := hdr_lt_slot p.L.w 0 (show 31 < 32 by decide)
    have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
    have := hg.2
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 p.cnt ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.scr.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega),
        hg.1.scr.ld (d := 8 * sW) (by unfold sW; omega), hcnt, hg.1.hdr.hw, ← BitVec.ofNat_add]
      rfl) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨?_, hcx⟩
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, hm ▸ hcnt, hodd, hlo, hm ▸ hv⟩
  -- The doublings.
  refine RelCT.seq (two_post (Ψ := fun p s => VG.Proof.Bignum.X86_64.SqPre p.L s) ((two_map (fun p => (⟨p.L, p.cnt⟩ : VG.Proof.Bignum.X86_64.DblPub))
    (fun p s h => ?_) (VG.Proof.Bignum.X86_64.doubles_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide))).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_) ?_
  · obtain ⟨⟨hg, hw, hw', hN, -, -, hodd, hlo, hv⟩, hcx⟩ := h
    obtain ⟨-, -, -, hL, hv0⟩ := VG.Proof.Bignum.X86_64.r2top (s := s) hw hN hodd hlo
    exact ⟨hg, hw, show p.L.w < 2 ^ 31 by omega, show 1 ≤ p.cnt by unfold R2Pub.cnt; omega,
      show p.cnt < 2 ^ 31 by unfold R2Pub.cnt; omega, hcx, by rw [hv, hN]; exact hv0⟩
  · intro p s h
    obtain ⟨⟨hg, hw, hw', hN, hinv, -, hodd, hlo, hv⟩, hcx⟩ := h
    obtain ⟨-, -, -, hL, hv0⟩ := VG.Proof.Bignum.X86_64.r2top (s := s) hw hN hodd hlo
    have hn' : p.L.B.toNat + VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
    refine WP.mono (doubles_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hw (by omega) (mo := aN) (acc := aAcc)
      (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (sl := sCnt) (by decide) (by decide)
      (c := p.cnt) (by unfold R2Pub.cnt; omega) (by unfold R2Pub.cnt; omega) hcx (by rw [hv, hN]; exact hv0))
      fun t ⟨hv', hf, hH, k⟩ => ?_
    have hf' : Frm p.L.B (r2Ranges p.L.w) s.mem t.mem := hf
    have hN0 : 0 < p.N := by omega
    refine ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hH⟩, hg.2⟩, hw, by omega,
      by rw [hf'.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact hinv, ?_⟩
    rw [hv', hf'.r2_wv hn' (by decide) (by decide) (by decide) (by decide), hN]
    exact Nat.mod_lt _ hN0
  -- The squarings.
  exact two_map (·.L) (fun _ _ h => h) (VG.Proof.Bignum.X86_64.sqs_ct M 5)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CTSetup`. -/
section

/-!
# `vg_rsa_public` on x86-64: the setup is constant time but for `m`

The loads of `m` and the input, the comparison, `-m⁻¹` and the number 1
(`setup_ct`). `-m⁻¹ mod 2⁶⁴` is the same in two runs that agree on `m`
(`minv_unique`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- `-n⁻¹ mod 2⁶⁴` is unique. -/
theorem minv_unique {n : Nat} {a b : BitVec 64} (hn : n % 2 = 1) (ha : (n * a.toNat + 1) % 2 ^ 64 = 0)
    (hb : (n * b.toNat + 1) % 2 ^ 64 = 0) : a = b := by
  have hc : Nat.Coprime (2 ^ 64) n := VG.Proof.Bignum.coprime_pow2 hn 64
  have h : n * a.toNat ≡ n * b.toNat [MOD 2 ^ 64] := by
    have e1 : (n * a.toNat + 1) % 2 ^ 64 = (n * b.toNat + 1) % 2 ^ 64 := by rw [ha, hb]
    exact Nat.ModEq.add_right_cancel' 1 e1
  have := Nat.ModEq.cancel_left_of_coprime (hc : Nat.gcd (2 ^ 64) n = 1) h
  apply BitVec.eq_of_toNat_eq
  rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
  exact this

/-! ## The loads -/

/-- The public data of the setup: the working space, the length `k` of `m`,
`m` (its bytes `nb` at `np`) and the input's pointer `ip`. -/
structure SPub where
  B : Addr
  Z : Nat
  k : Nat
  np : Addr
  ip : Addr
  nb : List Byte

/-- `w` for `p.k` bytes. -/
abbrev SPub.w (p : VG.Proof.Bignum.X86_64.SPub) : Nat := (p.k + 7) / 8

/-- What the setup keeps: the working space, the header's arguments and the
byte strings. -/
def SH (p : VG.Proof.Bignum.X86_64.SPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧ 9 ≤ p.k ∧ p.k < 2 ^ 31 ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sN) = p.np ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sIn) = p.ip ∧ Src s p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    Spec.Rsa.os2ip p.nb % 2 = 1 ∧ ∃ xb : List Byte, Src s p.B p.Z p.ip xb ∧ xb.length = p.k

/-- `SH` after code that changes only memory in the working space outside the
header's arguments, and not `rdi`. -/
theorem SH.congr {p : VG.Proof.Bignum.X86_64.SPub} {s t : State} (h : VG.Proof.Bignum.X86_64.SH p s) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.SH p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk, hK, hN, hIn, hn, hnl, hodd, xb, hx', hxl⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, (hfx sIn (by decide)).trans hIn, hn.congrK hi k, hnl, hodd, xb,
    hx'.congrK hi k, hxl⟩

theorem pins_SH : Pins VG.Proof.Bignum.X86_64.SH [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the first block: the bases and `w`, and the registers for `m`'s load. -/
def S1 (p : VG.Proof.Bignum.X86_64.SPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.SH p s ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j)) ∧
    s.gpr .rsi = p.np ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN)

/-- After `m`'s load. -/
def S2 (p : VG.Proof.Bignum.X86_64.SPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.SH p s ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j)) ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aN) p.w = Spec.Rsa.os2ip p.nb

/-- Before the input's load. -/
def S3 (p : VG.Proof.Bignum.X86_64.SPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.S2 p s ∧ s.gpr .rsi = p.ip ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aX)

theorem pins_S1 : Pins VG.Proof.Bignum.X86_64.S1 [.rsi, .rcx, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem pins_S3 : Pins VG.Proof.Bignum.X86_64.S3 [.rsi, .rcx, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem hdr_fixed {i : Nat} (hi : 8 * i + 8 ≤ 8 * 16 ∧ 6 ≤ i ∨ 22 ≤ i ∧ i < 32) :
    8 * 22 ≤ 8 * i ∨ (8 * 6 ≤ 8 * i ∧ 8 * i + 8 ≤ 8 * 16) := by omega

theorem arr_fixed (w : Nat) {j : Nat} : 8 * 22 ≤ VG.Proof.Bignum.X86_64.slot w j ∨ (8 * 6 ≤ VG.Proof.Bignum.X86_64.slot w j ∧ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ 8 * 16) :=
  Or.inl (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega)

theorem slot0_ge (w : Nat) : 8 * 31 + 8 ≤ VG.Proof.Bignum.X86_64.slot w 0 ∧ VG.Proof.Bignum.X86_64.slot w 0 + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w 8 :=
  ⟨hdr_lt_slot w 0 (by decide), slot_le (by decide)⟩

/-- The loads of `m` and the input leak the same in runs that agree on `m`. -/
theorem setupLoad_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.SH) (seqs loadSteps) (Two VG.Proof.Bignum.X86_64.S2) := by
  unfold loadSteps
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.S1) _ VG.Proof.Bignum.X86_64.pins_SH (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge p.w
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t ⟨h12, hcx, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), hW, hb, hsi, hcx, hbx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.S2) _ VG.Proof.Bignum.X86_64.pins_S1 (by taint_decide) ?_) ?_
  · intro p s ⟨h, hW, hb, hsi, hcx, hbx⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk1, hk, -, -, -, hn, hnl, -⟩ := h'
    have := slot_le (w := p.w) (show aN < 8 by decide)
    refine WP.mono (loadArr_ok hs (by decide) hZ hn hnl (by omega) hk hsi hcx hbx) fun t ⟨hv, ha, k⟩ =>
      ⟨h.congr (Frm.of_arrays1 ha (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k (by decide),
        by rw [ha.hslot (by decide)]; exact hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact hb j hj,
        hv⟩
    · rw [List.mem_singleton.mp hr]; exact this.trans hZ
    · rw [List.mem_singleton.mp hr]; exact VG.Proof.Bignum.X86_64.arr_fixed _
  -- The input's registers.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.S3) _ (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_SH p s₁ s₂ h₁.1 h₂.1) (by taint_decide)
    ?_) ?_
  · intro p s ⟨h, hW, hb, hv⟩
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk, hK, -, hIn, -⟩ := h'
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge p.w
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ip ∧
        t.gpr .rcx = BitVec.ofNat 64 p.k ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aX) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sIn) (by unfold sIn sFn; omega),
        hs.ld (d := 8 * sK) (by unfold sK sFn; omega), hs.ld (d := 8 * sArr aX) (by unfold sArr aX; omega), hIn,
        hK, hb aX (by decide)]) rfl) fun t ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ =>
      ⟨⟨h.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k (by decide), hm ▸ hW,
        hm ▸ hb, hm ▸ hv⟩, hsi, hcx, hbx⟩
  -- The input.
  refine two_piece (Ψ := VG.Proof.Bignum.X86_64.S2) _ VG.Proof.Bignum.X86_64.pins_S3 (by taint_decide) ?_
  rintro p s ⟨⟨h, hW, hb, hv⟩, hsi, hcx, hbx⟩
  have h' : VG.Proof.Bignum.X86_64.SH p s := h
  obtain ⟨hs, -, hZ, hk1, hk, -, -, -, -, -, -, xb, hx, hxl⟩ := h'
  have hn' := slot_le (w := p.w) (show aN < 8 by decide)
  have hx8 := slot_le (w := p.w) (show aX < 8 by decide)
  have hsep := VG.Proof.Bignum.X86_64.slot_sep (w := p.w) (show aN ≠ aX by decide)
  have hnw : p.B.toNat + VG.Proof.Bignum.X86_64.slot p.w 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega
  refine WP.mono (loadArr_ok hs (by decide) hZ hx hxl (by omega) hk hsi hcx hbx) fun t ⟨_, ha, k⟩ =>
    ⟨h.congr (Frm.of_arrays1 ha (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k (by decide),
      by rw [ha.hslot (by decide)]; exact hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact hb j hj,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hnw]; exact hv⟩
  · rw [List.mem_singleton.mp hr]; exact hx8.trans hZ
  · rw [List.mem_singleton.mp hr]; exact VG.Proof.Bignum.X86_64.arr_fixed _

/-! ## The comparison, `-m⁻¹` and the number 1 -/

/-- The mask's store, and `-m⁻¹` into the header: the header is whole. -/
theorem blk7_ok {t : State} {B : Addr} {Z w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hdi : t.gpr .rdi = B)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hW : VG.Proof.Bignum.X86_64.word t.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hb : ∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))
    (h10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)) (hodd : (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) :
    WP isa (.block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
        ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr))) t fun t' =>
      ∃ mi : BitVec 64, Hdr t'.mem B w mi ∧ VG.Proof.Bignum.X86_64.Scr t' B Z ∧ t'.gpr .rdi = B ∧
        t'.gpr .rcx = BitVec.ofNat 64 0 ∧ VG.Proof.MlKem.X86_64.Keep [.rbx, .rax, .rcx, .rdx, .rsi, .r15] t t' := by
  have hn := hs.nowrap
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hsN : ∀ v : BitVec 64, (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) v).readW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)) 64 =
      VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN) := fun v =>
    (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by unfold sMask sFn; omega)).word
      (by have := hdr_lt_slot w aN (show sMask < 32 by decide); omega)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx] (Q := fun t₁ => t₁.gpr .rbx = VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN) ∧
      t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (t.gpr .rbp)) (by
    xrun [State.ea, hdr, at0, hdi, hdrOff, hs.st (d := 8 * sMask) (by unfold sMask sFn; omega), h10, hsN,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs.ld (d := VG.Proof.Bignum.X86_64.slot w aN) (by have := slot_le (w := w) (show aN < 8 by decide); omega)]) rfl)
    fun t₃ ⟨⟨hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd)) fun t₄ ⟨_, k₄, hm₄⟩ => ?_
  have hs₄ := (hs.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 0 ∧
      t'.mem = t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by unfold sMinv; omega)]) rfl)
    fun t₅ ⟨⟨hcx₅, hm₅⟩, k₅⟩ => ⟨t₄.gpr .r15, ?_, hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄, hcx₅,
      ((k₃.trans k₄).trans k₅).mono (by decide)⟩
  have hm₅' : t₅.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (t.gpr .rbp)).writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv))
      (t₄.gpr .r15) := by rw [hm₅, hm₄, hm₃]
  have hhd : ∀ i < 32, i ≠ sMask → i ≠ sMinv → VG.Proof.Bignum.X86_64.word t₅.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t.mem B (8 * i) :=
    fun i hi h1 h2 => by
      rw [hm₅', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  exact ⟨by rw [hhd sW (by decide) (by decide) (by decide)]; exact hW, by rw [hm₅', VG.Proof.Bignum.X86_64.word_writeW_self],
    fun j hj => by rw [hhd (sArr j) (by unfold sArr; omega) (by unfold sArr sMask sFn; omega)
      (by unfold sArr sMinv; omega)]; exact hb j hj⟩

/-- The public data of the comparison, `-m⁻¹` and the number 1: the working
space and `w`. -/
structure RPub where
  B : Addr
  Z : Nat
  w : Nat

/-- What the comparison, `-m⁻¹` and the number 1 need: the working space, the
header's `w` and bases, and `m` odd. -/
def SR (p : VG.Proof.Bignum.X86_64.RPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 31 ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧ (∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j)) ∧
    (VG.Proof.Bignum.X86_64.word s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aN)).toNat % 2 = 1

/-- `SR` with the same memory, and `rdi` kept. -/
theorem SR.mem {p : VG.Proof.Bignum.X86_64.RPub} {s t : State} (h : VG.Proof.Bignum.X86_64.SR p s) (hm : t.mem = s.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.SR p t :=
  let ⟨hs, hdi, hZ, hw, hw', hW, hb, hodd⟩ := h
  ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hw, hw', hm ▸ hW, hm ▸ hb, hm ▸ hodd⟩

/-- After the comparison's registers. -/
def S5 (p : VG.Proof.Bignum.X86_64.RPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.SR p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aX) ∧
    s.gpr .r10 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN) ∧ s.gpr .rbp = VG.Proof.Bignum.X86_64.mask false

/-- After the comparison. -/
def S6 (p : VG.Proof.Bignum.X86_64.RPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.SR p s ∧ s.gpr .r10 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.w

/-- After `-m⁻¹`. -/
def S7 (p : VG.Proof.Bignum.X86_64.RPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, Hdr s.mem p.B p.w mi ∧ VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧
    s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rcx = BitVec.ofNat 64 0

theorem SH.k1 {p : VG.Proof.Bignum.X86_64.SPub} {s : State} (h : VG.Proof.Bignum.X86_64.SH p s) : 2 ≤ p.w := by have := h.2.2.2.1; unfold SPub.w; omega

/-- `S2` gives what the comparison, `-m⁻¹` and the number 1 need. -/
theorem S2.sr {p : VG.Proof.Bignum.X86_64.SPub} {s : State} (h : VG.Proof.Bignum.X86_64.S2 p s) : VG.Proof.Bignum.X86_64.SR ⟨p.B, p.Z, p.w⟩ s := by
  obtain ⟨h, hW, hb, hv⟩ := h
  have hk := h.k1
  obtain ⟨hs, hdi, hZ, -, hk', -, -, -, -, -, hodd, -⟩ := h
  refine ⟨hs, hdi, hZ, hk, show p.w < 2 ^ 31 by unfold SPub.w; omega, hW, hb, ?_⟩
  rw [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), Nat.mod_mod_of_dvd _ (by decide), hv, hodd]

/-- The comparison, `-m⁻¹` and the number 1 leak the same in runs that agree
on `m`. -/
theorem setupRest_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.SR) (seqs restSteps) fun _ _ => True := by
  unfold restSteps
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.S5) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, -, -, hW, hb, -⟩ := h'
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge p.w
    refine WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aX) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sW) (by unfold sW; omega),
        hs.ld (d := 8 * sArr aX) (by unfold sArr aX; omega), hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
        hW, hb aX (by decide), hb aN (by decide)]) rfl) fun t ⟨⟨h12, hbx, h10, hbp, hm⟩, k⟩ =>
      ⟨h.mem hm k (by decide), h12, hbx, h10, hbp⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.S6) [.rbx, .r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h12, hbx, h10, hbp⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk, hk', -⟩ := h'
    refine WP.mono (cmpLoop_ok hs hbx h10 h12 hbp (by omega) hk'
      (by have := slot_le (w := p.w) (show aX < 8 by decide); omega)
      (by have := slot_le (w := p.w) (show aN < 8 by decide); omega)) fun t ⟨_, hm, k⟩ =>
      ⟨h.mem hm k (by decide), (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `-m⁻¹`, and the number 1.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.S7) [.rdi, .r10] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h10, h12⟩
    obtain ⟨hs, hdi, hZ, hk, -, hW, hb, hodd₀⟩ := h
    exact WP.mono (VG.Proof.Bignum.X86_64.blk7_ok hs hdi hZ (by omega) hW hb h10 hodd₀) fun t ⟨mi, hH, hs', hdi', hcx, k⟩ =>
      ⟨mi, hH, hs', hdi', hZ, (k.gpr (by decide)).trans h12, hcx⟩
  -- The number 1.
  rw [VG.Proof.Bignum.X86_64.setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => VG.Proof.Bignum.X86_64.S7 p s ∧ s.gpr .r8 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aOne)) [.rdi]
    (fun p s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
      obtain ⟨⟨_, _, _, _, _, a₁, b₁⟩, c₁⟩ := h₁
      obtain ⟨⟨_, _, _, _, _, a₂, b₂⟩, c₂⟩ := h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [c₁, c₂]
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide))
  rintro p s ⟨mi, hH, hs, hdi, hZ, h12, hcx⟩
  have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * sArr aOne)) 8 :=
    hs.ld (by have := hdr_lt_slot p.w 8 (show sArr aOne < 32 by decide); omega)
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aOne) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl, hH.harr aOne (by decide)]) rfl)
    fun t ⟨⟨h8, hm⟩, k⟩ => ⟨⟨mi, hm ▸ hH, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, hZ,
      (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩, h8⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CTMain`. -/
section

/-!
# `vg_rsa_public` on x86-64: constant time but for `n` and `e`

The result's store (`out_ct`), `main` (`main_ct`) and the whole function
(`code_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-! ## The result -/

/-- The public data of the result: the working space, the length `k` and `out`. -/
structure OPub where
  L : Lay
  k : Nat
  op : Addr

/-- `outPhase_ok`'s hypotheses. -/
def OPre (p : VG.Proof.Bignum.X86_64.OPub) (s : State) : Prop :=
  ∃ c : Bool, VG.Proof.Bignum.X86_64.Good s p.L.B p.L.Z p.L.w p.L.minv ∧ p.L.w = (p.k + 7) / 8 ∧ VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ p.L.Z ∧ 1 ≤ p.k ∧
    p.k < 2 ^ 31 ∧ VG.Proof.Bignum.X86_64.word s.mem p.L.B (8 * sOut) = p.op ∧ VG.Proof.Bignum.X86_64.word s.mem p.L.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    VG.Proof.Bignum.X86_64.word s.mem p.L.B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c ∧ (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.L.Z ≤ VG.Proof.Bignum.X86_64.ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- Before `storeBE`. -/
def O1 (p : VG.Proof.Bignum.X86_64.OPub) (s : State) : Prop :=
  ∃ c : Bool, VG.Proof.Bignum.X86_64.Scr s p.L.B p.L.Z ∧ s.gpr .rdi = p.L.B ∧ p.L.w = (p.k + 7) / 8 ∧ VG.Proof.Bignum.X86_64.slot p.L.w 8 ≤ p.L.Z ∧
    1 ≤ p.k ∧ p.k < 2 ^ 31 ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aY) ∧ s.gpr .rsi = p.op ∧
    s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧
    (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.L.Z ≤ VG.Proof.Bignum.X86_64.ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- The result's store leaks the same in runs with the same working space,
length and `out`. -/
theorem out_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.OPre) (seqs outSteps) fun _ _ => True := by
  unfold outSteps
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.O1) [.rdi] (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    have hn := hg.scr.nowrap
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge p.L.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.L.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega)
    refine WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
        t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.L.B (VG.Proof.Bignum.X86_64.slot p.L.w aY) ∧ t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
        t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
        hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) rfl)
      fun t ⟨⟨hbx, hsi, hcx, h15, hm⟩, k⟩ => ⟨c, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hw, hZ,
        hk1, hk, hbx, hsi, hcx, h15, fun j hj => by rw [k.2.2]; exact hout j hj, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = p.L.B) [.rbx, .rsi, .rcx]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, hdi, hw, hZ, hk1, hk, hbx, hsi, hcx, h15, hout, hsep⟩
    exact WP.mono (storeBE_ok hs hbx hsi hcx h15 hk1 hk hw
      (by have := slot_le (w := p.L.w) (show aY < 8 by decide); omega) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr (by decide)).trans hdi
  exact two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-! ## Sequences and re-indexing -/

theorem exec_seqs_append {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      have e₂' := ih (by simp) e₂
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases e₂' with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

theorem RelCT.seqs_append {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (VG.Proof.Bignum.X86_64.exec_seqs_append ha hb e₁) (VG.Proof.Bignum.X86_64.exec_seqs_append ha hb e₂)

/-- Two runs related with the same `a` are related with the same `b`. -/
theorem two_bind {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop}
    (f : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∃ b, Ψ b s₁ ∧ Ψ b s₂) {s₁ s₂ : State} (h : Two Φ s₁ s₂) :
    Two Ψ s₁ s₂ :=
  let ⟨a, h₁, h₂⟩ := h; f a s₁ s₂ h₁ h₂

/-! ## `main` -/

/-- The public data of `main`: the working space, `k`, the pointers, `e`'s
length and the bytes of `n` and `e`. -/
structure MPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  ep : Addr
  ip : Addr
  len : Nat
  nb : List Byte
  eb : List Byte

abbrev MPub.w (p : VG.Proof.Bignum.X86_64.MPub) : Nat := (p.k + 7) / 8
abbrev MPub.N (p : VG.Proof.Bignum.X86_64.MPub) : Nat := Spec.Rsa.os2ip p.nb

/-- `main_ok`'s hypotheses. -/
def MRel (p : VG.Proof.Bignum.X86_64.MPub) (s : State) : Prop :=
  ∃ xb, MainPre s p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true

/-- After the setup. -/
def MA (p : VG.Proof.Bignum.X86_64.MPub) (t : State) : Prop :=
  ∃ (σ : State) (xb : List Byte) (mi : BitVec 64),
    MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true ∧
    SetupOut t p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb) ∧ Frm p.B (setupRanges p.w) σ.mem t.mem ∧
    VG.Proof.MlKem.X86_64.Keep mmRegs σ t

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem so_minv {t t' : State} {B : Addr} {Z w : Nat} {mi mi' : BitVec 64} {N X X' : Nat}
    (h : SetupOut t B Z w mi N X) (h' : SetupOut t' B Z w mi' N X') (hodd : N % 2 = 1) (hw : 1 ≤ w) :
    mi = mi' := by
  have e : ∀ {t : State} {mi : BitVec 64} {X : Nat}, SetupOut t B Z w mi N X →
      (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ hw, h.n]
  have i := h.inv
  have i' := h'.inv
  rw [e h] at i
  rw [e h'] at i'
  exact VG.Proof.Bignum.X86_64.minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i i'

/-- `main`'s state facts give the setup's. -/
theorem MRel.sh {p : VG.Proof.Bignum.X86_64.MPub} {s : State} (h : VG.Proof.Bignum.X86_64.MRel p s) : VG.Proof.Bignum.X86_64.SH ⟨p.B, p.Z, p.k, p.np, p.ip, p.nb⟩ s := by
  obtain ⟨xb, h, hv⟩ := h
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  exact ⟨h.scr, h.rdi, h.z, show 9 ≤ p.k by omega, show p.k < 2 ^ 31 by omega, h.hK, h.hN, h.hIn, h.n, h.nl,
    hodd, xb, h.x, h.xl⟩

/-- The setup leaks the same in runs that agree on `n`. -/
theorem mainA_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.MRel) (seqs (loadSteps ++ restSteps)) (Two VG.Proof.Bignum.X86_64.MA) := by
  refine two_post ((RelCT.seqs_append (by simp [loadSteps]) (by simp [restSteps])
    (RelCT.seq VG.Proof.Bignum.X86_64.setupLoad_ct (two_map (fun p : VG.Proof.Bignum.X86_64.SPub => (⟨p.B, p.Z, p.w⟩ : VG.Proof.Bignum.X86_64.RPub)) (fun _ _ h => h.sr) VG.Proof.Bignum.X86_64.setupRest_ct))).mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_bind (fun p _ _ h₁ h₂ =>
      ⟨_, h₁.sh, h₂.sh⟩) h) fun _ _ h => h) ?_
  rintro p s ⟨xb, h, hv⟩
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  exact WP.mono (VG.Proof.Bignum.X86_64.setup_ok h.scr h.rdi h.z (by omega) (by omega) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
    fun t ⟨mi, so, f, k⟩ => ⟨s, xb, mi, h, hv, so, f, k⟩

/-- After `R² mod m`. -/
def MB (p : VG.Proof.Bignum.X86_64.MPub) (t : State) : Prop :=
  ∃ (σ : State) (xb : List Byte) (mi : BitVec 64) (t₁ : State),
    MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true ∧
    SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb) ∧ Frm p.B (setupRanges p.w) σ.mem t₁.mem ∧
    VG.Proof.MlKem.X86_64.Keep mmRegs σ t₁ ∧ VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w mi ∧ wv t.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aR2) p.w < p.N ∧
    wv t.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N ∧
    Frm p.B (r2Ranges p.w) t₁.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t₁ t

theorem MA.r2Pre {p : VG.Proof.Bignum.X86_64.MPub} {t : State} {σ : State} {xb : List Byte} {mi : BitVec 64}
    (h : MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true)
    (so : SetupOut t p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb)) : VG.Proof.Bignum.X86_64.R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ t := by
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  exact ⟨⟨so.good, h.z⟩, show 2 ≤ p.w by unfold MPub.w; omega, show p.w < 2 ^ 30 by unfold MPub.w; omega, so.n, so.inv, so.r12, so.r10,
    hodd, hlo⟩

/-- `R² mod m` leaks the same in runs that agree on `n`. -/
theorem mainB_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.MA) (seqs (r2Steps Mont.base)) (Two VG.Proof.Bignum.X86_64.MB) := by
  refine two_post ((VG.Proof.Bignum.X86_64.r2_ct Mont.base).mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h) ?_
  · obtain ⟨σ₁, xb₁, mi₁, hm₁, hv, so₁, -⟩ := h₁
    obtain ⟨σ₂, xb₂, mi₂, hm₂, -, so₂, -⟩ := h₂
    obtain ⟨hodd, -, -⟩ := valid_facts hv hm₁.k1
    have := hm₁.k1
    obtain rfl := VG.Proof.Bignum.X86_64.so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold MPub.w; omega)
    exact ⟨_, MA.r2Pre hm₁ hv so₁, MA.r2Pre hm₂ hv so₂⟩
  rintro p t ⟨σ, xb, mi, hm, hv, so, f, k⟩
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv hm.k1
  have := hm.k1
  have := hm.k2
  exact WP.mono (r2_ok Mont.base so.good hm.z (by unfold MPub.w; omega) (by unfold MPub.w; omega) so.n so.inv so.r12 so.r10 hodd hlo)
    fun t' ⟨hg, hlt, hr, f', k'⟩ => ⟨σ, xb, mi, t, hm, hv, so, f, k, hg, hlt, hr, f', k'⟩

/-- What the exponentiation phase needs, from the facts after `R² mod m`. -/
theorem mb_ePre {p : VG.Proof.Bignum.X86_64.MPub} {t σ t₁ : State} {xb : List Byte} {mi : BitVec 64}
    (hm : MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true)
    (so : SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb)) (f : Frm p.B (setupRanges p.w) σ.mem t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep mmRegs σ t₁) (hg : VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w mi) (hlt : wv t.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aR2) p.w < p.N)
    (hr : wv t.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N)
    (f' : Frm p.B (r2Ranges p.w) t₁.mem t.mem) (k' : VG.Proof.MlKem.X86_64.Keep mmRegs t₁ t) :
    VG.Proof.Bignum.X86_64.EPhasePre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N, p.ep, p.len, p.eb⟩ t := by
  obtain ⟨hodd, hN1, -⟩ := valid_facts hv hm.k1
  have := hm.k1
  have := hm.k2
  have := hm.L2
  have hn := hm.scr.nowrap
  have hZ : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z := hm.z
  have hn' : p.B.toNat + VG.Proof.Bignum.X86_64.slot p.w 8 ≤ 2 ^ 64 := by omega
  have x₁₂ := (Fixed.of_frm f (setupRanges_fixed _)).trans (Fixed.of_frm f' (r2Ranges_fixed _))
  have i₁₂ := (InScr.of_frm f fun r hr => (setupRanges_le _ r hr).trans hZ).trans
    (InScr.of_frm f' fun r hr => (r2Ranges_le _ r hr).trans hZ)
  exact ⟨Spec.Rsa.os2ip xb, hg, hZ, show 2 ≤ p.w by unfold MPub.w; omega,
    show p.w < 2 ^ 31 by unfold MPub.w; omega, hodd, hN1,
    by rw [f'.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n,
    by rw [f'.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv,
    by rw [f'.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x,
    by rw [f'.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one, hlt, hr,
    by rw [x₁₂ sE (by decide)]; exact hm.hE, by rw [x₁₂ sElen (by decide)]; exact hm.hL, hm.el, hm.L1,
    show p.len < 2 ^ 31 by omega, hm.e.congrK i₁₂ (k.trans k')⟩

/-- After the exponentiation. -/
def MC (p : VG.Proof.Bignum.X86_64.MPub) (t : State) : Prop :=
  ∃ (σ : State) (xb : List Byte) (mi : BitVec 64) (t₁ t₂ : State),
    MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true ∧
    SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb) ∧ Frm p.B (setupRanges p.w) σ.mem t₁.mem ∧
    VG.Proof.MlKem.X86_64.Keep mmRegs σ t₁ ∧ Frm p.B (r2Ranges p.w) t₁.mem t₂.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t₁ t₂ ∧
    VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w mi ∧ Frm p.B (expPhaseRanges p.w) t₂.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t₂ t

/-- The exponentiation leaks the same in runs that agree on `n` and `e`. -/
theorem mainC_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.MB) (seqs expSteps) (Two VG.Proof.Bignum.X86_64.MC) := by
  refine two_post (expPhase_ct.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h) ?_
  · obtain ⟨σ₁, xb₁, mi₁, u₁, hm₁, hv, so₁, f₁, k₁, hg₁, hlt₁, hr₁, f₁', k₁'⟩ := h₁
    obtain ⟨σ₂, xb₂, mi₂, u₂, hm₂, -, so₂, f₂, k₂, hg₂, hlt₂, hr₂, f₂', k₂'⟩ := h₂
    obtain ⟨hodd, -, -⟩ := valid_facts hv hm₁.k1
    have := hm₁.k1
    obtain rfl := VG.Proof.Bignum.X86_64.so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold MPub.w; omega)
    exact ⟨_, VG.Proof.Bignum.X86_64.mb_ePre hm₁ hv so₁ f₁ k₁ hg₁ hlt₁ hr₁ f₁' k₁', VG.Proof.Bignum.X86_64.mb_ePre hm₂ hv so₂ f₂ k₂ hg₂ hlt₂ hr₂ f₂' k₂'⟩
  rintro p t ⟨σ, xb, mi, t₁, hm, hv, so, f, k, hg, hlt, hr, f', k'⟩
  obtain ⟨X, hg', hZ, hw, hw', hodd, hN1, hn, hinv, hX, hone, hlt2, hr2, he, hlen, hL, hL1, hL', heb⟩ :=
    VG.Proof.Bignum.X86_64.mb_ePre hm hv so f k hg hlt hr f' k'
  exact WP.mono (expPhase_ok hg' hZ hw hw' hodd hN1 hn hinv hX hone hlt2 hr2 he hlen hL hL1 hL' heb)
    fun t' ⟨hg'', _, f'', k''⟩ => ⟨σ, xb, mi, t₁, t, hm, hv, so, f, k, f', k', hg'', f'', k''⟩

/-- What the result's store needs, from the facts after the exponentiation. -/
theorem mc_oPre {p : VG.Proof.Bignum.X86_64.MPub} {t σ t₁ t₂ : State} {xb : List Byte} {mi : BitVec 64}
    (hm : MainPre σ p.B p.Z p.k p.op p.np p.ep p.ip p.len p.nb p.eb xb)
    (so : SetupOut t₁ p.B p.Z p.w mi p.N (Spec.Rsa.os2ip xb)) (f : Frm p.B (setupRanges p.w) σ.mem t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep mmRegs σ t₁) (f' : Frm p.B (r2Ranges p.w) t₁.mem t₂.mem) (k' : VG.Proof.MlKem.X86_64.Keep mmRegs t₁ t₂)
    (hg : VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w mi) (f'' : Frm p.B (expPhaseRanges p.w) t₂.mem t.mem) (k'' : VG.Proof.MlKem.X86_64.Keep mmRegs t₂ t) :
    VG.Proof.Bignum.X86_64.OPre ⟨⟨p.B, p.Z, p.w, mi⟩, p.k, p.op⟩ t := by
  have := hm.k1
  have := hm.k2
  have hZ : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z := hm.z
  have x := ((Fixed.of_frm f (setupRanges_fixed _)).trans (Fixed.of_frm f' (r2Ranges_fixed _))).trans
    (Fixed.of_frm f'' (expPhaseRanges_fixed _))
  have kk := (k.trans k').trans k''
  refine ⟨decide (Spec.Rsa.os2ip xb < p.N), hg, rfl, hZ, show 1 ≤ p.k by omega, show p.k < 2 ^ 31 by omega,
    by rw [x sOut (by decide)]; exact hm.hO, by rw [x sK (by decide)]; exact hm.hK, ?_,
    fun j hj => by rw [kk.2.2]; exact hm.out j hj, hm.outSep⟩
  rw [f''.ep_hdr (by decide) (by decide) (by decide) (by decide),
    f'.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold sMask sFn; omega)]
  exact so.mask

/-- `main` leaks the same in runs that agree on the public data, `n` and `e`. -/
theorem main_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.MRel) VG.Impl.Bignum.X86_64.Public.main fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [loadSteps]) (by simp [r2Steps]) (RelCT.seq VG.Proof.Bignum.X86_64.mainA_ct ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [expSteps]) (RelCT.seq VG.Proof.Bignum.X86_64.mainB_ct ?_)
  refine RelCT.seqs_append (by simp [expSteps]) (by simp [outSteps, outStepsArr]) (RelCT.seq VG.Proof.Bignum.X86_64.mainC_ct ?_)
  refine out_ct.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h
  obtain ⟨σ₁, xb₁, mi₁, u₁, v₁, hm₁, hv, so₁, f₁, k₁, f₁', k₁', hg₁, f₁'', k₁''⟩ := h₁
  obtain ⟨σ₂, xb₂, mi₂, u₂, v₂, hm₂, -, so₂, f₂, k₂, f₂', k₂', hg₂, f₂'', k₂''⟩ := h₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv hm₁.k1
  have := hm₁.k1
  obtain rfl := VG.Proof.Bignum.X86_64.so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold MPub.w; omega)
  exact ⟨_, VG.Proof.Bignum.X86_64.mc_oPre hm₁ so₁ f₁ k₁ f₁' k₁' hg₁ f₁'' k₁'', VG.Proof.Bignum.X86_64.mc_oPre hm₂ so₂ f₂ k₂ f₂' k₂' hg₂ f₂'' k₂''⟩

/-! ## The whole function -/

theorem WP.and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-- The public data of `vg_rsa_public`: `main`'s and the stack pointer. -/
structure CPub where
  m : VG.Proof.Bignum.X86_64.MPub
  rsp : Addr

/-- A state the contract allows, with the public data `p`. -/
def CRel (p : VG.Proof.Bignum.X86_64.CPub) (s : State) : Prop :=
  pubContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 2 = p.m.B ∧ (stackArg s 3).toNat * 8 = p.m.Z ∧
    (s.gpr .rcx).toNat = p.m.k ∧ s.gpr .rdi = p.m.op ∧ s.gpr .rdx = p.m.np ∧ s.gpr .r8 = p.m.ep ∧
    stackArg s 0 = p.m.ip ∧ (s.gpr .r9).toNat = p.m.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.m.nb ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = p.m.eb

theorem entry_split : VG.Impl.Bignum.X86_64.Public.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) := rfl

/-- After `entry`'s first instruction. -/
def C1 (p : VG.Proof.Bignum.X86_64.CPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.CRel p s ∧ t.gpr .r11 = p.m.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block ((entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))])) t (VG.Proof.Bignum.X86_64.HeadPost s)

/-- After `entry` and the reloads. -/
def C2 (p : VG.Proof.Bignum.X86_64.CPub) (t : State) : Prop := ∃ s, VG.Proof.Bignum.X86_64.CRel p s ∧ VG.Proof.Bignum.X86_64.HeadPost s t

/-- After the modulus' check. -/
def C3 (p : VG.Proof.Bignum.X86_64.CPub) (t : State) : Prop :=
  ∃ s t₁, VG.Proof.Bignum.X86_64.CRel p s ∧ VG.Proof.Bignum.X86_64.HeadPost s t₁ ∧ t.mem = t₁.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.m.nb) p.m.k)

/-- `vg_rsa_public` leaks the same in runs that agree on the public data. -/
theorem code_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.CRel) VG.Impl.Bignum.X86_64.Public.code fun _ _ => True := by
  unfold VG.Impl.Bignum.X86_64.Public.code
  refine RelCT.seq (R := Two VG.Proof.Bignum.X86_64.C3) (RelCT.block_append (RelCT.seq (R := Two VG.Proof.Bignum.X86_64.C2) ?_ ?_)) ?_
  · rw [VG.Proof.Bignum.X86_64.entry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.C1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := VG.Proof.Bignum.X86_64.codeCtx_of hs.1
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 24 })] ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]))) s (VG.Proof.Bignum.X86_64.HeadPost s) := by
      rw [← VG.Proof.Bignum.X86_64.entry_split]; exact VG.Proof.Bignum.X86_64.head_ok c
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha2, hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.1, c₂.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := VG.Proof.Bignum.X86_64.codeCtx_of hs.1
    have hnb := c.hnb.congrK h.inScr h.keep
    refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
      rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ =>
        ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2.2.2.2.2.2.2.2.2.2.1, ← hs.2.2.2.2.1]
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [VG.X86_64.eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold VG.Impl.Bignum.X86_64.Public.fail
    have pin : ∀ p t, (VG.Proof.Bignum.X86_64.C3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.m.B :=
      fun p t ⟨⟨s, t₁, hs, h, _, k, _⟩, _⟩ => ((k.gpr (by decide)).trans h.rdi).trans hs.2.2.1
    refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rsi = p.m.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.m.k ∧
        t.gpr .rdi = p.m.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨⟨s, t₁, hs, h, hm, k, -⟩, -⟩
    have c := VG.Proof.Bignum.X86_64.codeCtx_of hs.1
    have hpre := VG.Proof.Bignum.X86_64.mainPre_of c h hm k
    have hn := hpre.scr.nowrap
    have := c.hZ
    have := c.hk1
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (stackArg s 2) (8 * i)) 8 := fun i hi =>
      hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = s.gpr .rdi ∧
        t'.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat) (by
      xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨by rw [hsi, hs.2.2.2.2.2.1], by rw [hcx, hs.2.2.2.2.1],
        ((k'.gpr (by decide)).trans hpre.rdi).trans hs.2.2.1⟩
  · -- `main`.
    have toM : ∀ p t, VG.Proof.Bignum.X86_64.C3 p t ∧ isa.eval .ne t = some false → VG.Proof.Bignum.X86_64.MRel p.m t := by
      rintro p t ⟨⟨s, t₁, hs, h, hm, k, hz⟩, he⟩
      have c := VG.Proof.Bignum.X86_64.codeCtx_of hs.1
      obtain ⟨_, -, hB, hZ, hk, hop, hnp, hep, hip, hlen, hnb, heb⟩ := hs
      have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.m.nb) p.m.k = true := by
        simp only [VG.X86_64.eval, hz] at he; simpa using he
      refine ⟨Spec.Rsa.bytesAt s.mem p.m.ip p.m.k, ?_, hv⟩
      have := VG.Proof.Bignum.X86_64.mainPre_of c h hm k
      rw [hnb, heb, hB, hZ, hk, hop, hnp, hep, hip, hlen] at this
      exact this
    exact main_ct.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h)
      fun _ _ h => h

/-- The public data of a state. -/
def cpubOf (s : State) : VG.Proof.Bignum.X86_64.CPub :=
  ⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .r8, stackArg s 0,
    (s.gpr .r9).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat⟩, s.gpr .rsp⟩

/-- `vg_rsa_public` is constant time but for `n` and `e`. -/
theorem code_constantTime : ConstantTime isa pubContract.pre pubContract.pub VG.Impl.Bignum.X86_64.Public.code := by
  refine RelCT.constantTime (code_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨VG.Proof.Bignum.X86_64.cpubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, -, a2, a3, hn, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rcx (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, hn.symm, he.symm⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtChk`. -/
section

/-!
# RSA with the CRT on x86-64: the checks

`checks`: the mask of `c < n`, `p q = n` and `qInv < p` into the modulus'
`sMask` and the primes' `sMaskX`, the primes replaced by 3 where it is
clear, and their `-X⁻¹` and the number 1 (`checks_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem mask_and (a b : Bool) : VG.Proof.Bignum.X86_64.mask a &&& VG.Proof.Bignum.X86_64.mask b = VG.Proof.Bignum.X86_64.mask (a && b) := by
  cases a <;> cases b <;> rfl

theorem odd_of_mul_odd {P Q N : Nat} (h : P * Q = N) (hN : N % 2 = 1) : P % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one P with hP | hP
  · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
  · exact hP

/-- The mask of the private key's checks. -/
def keyMask (m0 : Bool) (N P Q QI : Nat) : Bool := m0 && decide (P * Q = N) && decide (QI < P)

/-- The checks: the mask `M` of `c < n` (`m0`), `p q = n` and `qInv < p`;
`p := M ? p : 3`, `q := M ? q : 3`, their `-X⁻¹` and 1. -/
theorem checks_ok {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m0 : Bool} (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op)
    (hop : op + VG.Proof.Bignum.X86_64.slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + VG.Proof.Bignum.X86_64.slot wq 8 + tabBytes wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B op) (hsQ : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq)
    (hN : wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w = N) (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask m0)
    (hP : wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wp Public.aN) wp = P) (hQ : wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wp aChunk) wp = QI) (hodd : N % 2 = 1) :
    WP isa (seqs checks) s fun t => VG.Proof.Bignum.X86_64.Good t B Z w minv ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask (VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI) ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B op ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq ∧
      (∃ mp', WsAt t.mem B op wp mp' ∧ XVals t B op wp mp' (if VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI then P else 3) ∧
        VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask (VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI)) ∧
      (∃ mq', WsAt t.mem B oq wq mq' ∧ XVals t B oq wq mq' (if VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI then Q else 3)) ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w Public.aAcc, 8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, VG.Proof.Bignum.X86_64.slot wp 8), (oq, VG.Proof.Bignum.X86_64.slot wq 8)]
        s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wp 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wq 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hz : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hacc := accs_le w
  have hA0 := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  unfold checks
  simp only [List.append_assoc]
  -- `p q`.
  refine wp_seqs_append (by simp [pqProduct, zeroAccs]) (by simp) ?_
  refine WP.mono (pqProduct_ok hg (by omega) hsP hsQ hwsP.hdr.hw hwsQ.hdr.hw
    (by rw [hwsP.hdr.harr _ (by decide), off_off]) (by rw [hwsQ.hdr.harr _ (by decide), off_off]) hlo hop hoq
    (by omega) hwp' (by omega) hwq') fun s₁ ⟨hpq₁, ho₁, k₁⟩ => ?_
  have hb₁ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega)) (by omega)
  have hab₁ : ∀ d, VG.Proof.Bignum.X86_64.slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₁.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega)) hd'
  have hg₁ : VG.Proof.Bignum.X86_64.Good s₁ B Z w minv := ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    ⟨(hb₁ _ (by decide)).trans hg.hdr.hw, (hb₁ _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₁ _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩
  have hN₁ : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w = N := by
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    have : VG.Proof.Bignum.X86_64.slot w Public.aN + 8 * w ≤ VG.Proof.Bignum.X86_64.slot w Public.aAcc := by unfold VG.Proof.Bignum.X86_64.slot Public.aN Public.aAcc; omega
    rw [ho₁.wv (Or.inl (by omega)) (by omega)]; exact hN
  rw [← wv_off, ← wv_off, hP, hQ] at hpq₁
  -- `p q = n`.
  refine wp_seqs_append (by simp [eqCheck]) (by simp) ?_
  refine WP.mono (eqCheck_ok hg₁ (by omega) (by omega) (by omega)) fun s₂ ⟨hM₂, ho₂, k₂⟩ => ?_
  rw [hpq₁, hN₁, hb₁ _ (by decide), hM, VG.Proof.Bignum.X86_64.mask_and] at hM₂
  have hb₂ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      VG.Proof.Bignum.X86_64.word s₂.mem B d = VG.Proof.Bignum.X86_64.word s₁.mem B d := fun d hd hd' => ho₂.word hd hd'
  have hab₂ : ∀ d, VG.Proof.Bignum.X86_64.slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₂.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd hd' => by
    rw [hb₂ d (Or.inr (by unfold Public.sMask sFn; omega)) hd', hab₁ d hd hd']
  have hpw₂ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₂.mem (VG.Proof.Bignum.X86_64.off B op) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega) (by omega)
  have hqw₂ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₂.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega) (by omega)
  have hpv₂ : ∀ d k, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot wp 8 → wv s₂.mem (VG.Proof.Bignum.X86_64.off B op) d k = wv s.mem (VG.Proof.Bignum.X86_64.off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega) (by omega)
  have hqv₂ : ∀ d k, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot wq 8 → wv s₂.mem (VG.Proof.Bignum.X86_64.off B oq) d k = wv s.mem (VG.Proof.Bignum.X86_64.off B oq) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega) (by omega)
  have hsP₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B op := by
    rw [hb₂ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega)) (by unfold sWsP sFn; omega), hb₁ _ (by decide)]
    exact hsP
  have hsQ₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq := by
    rw [hb₂ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega)) (by unfold sWsQ sFn; omega), hb₁ _ (by decide)]
    exact hsQ
  have hs₂ := hs.congr (k₁.trans k₂).2.2
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hg.rdi
  -- Into `p`'s workspace: `qInv < p`.
  refine wp_seqs_append (by simp) (by simp [qinvCheck]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B op ∧ t.mem = s₂.mem)
    (by xrun [enterP, State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hsP₂]) rfl)
    fun s₃ ⟨⟨hdi₃, hm₃⟩, k₃⟩ => ?_
  have hs₃ := hs₂.congr k₃.2.2
  have hwsP₃ : WsAt s₃.mem B op wp mp := by rw [hm₃]; exact hwsP.of_words fun i hi => hpw₂ i (by omega)
  refine wp_seqs_append (by simp [qinvCheck]) (by simp [primeFix]) ?_
  refine WP.mono (qinvCheck_ok hs₃ hdi₃ hwsP₃.hdr (by omega) (by unfold Public.sMask sFn; omega) (by omega)
    (by omega) hwsP₃.link) fun s₄ ⟨hM₄, ho₄, k₄⟩ => ?_
  rw [hm₃, hpv₂ _ _ (by have := slot_le (w := wp) (show aChunk < 8 by decide); omega),
    hpv₂ _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega), hP, hQI, hM₂, VG.Proof.Bignum.X86_64.mask_and] at hM₄
  have hb₄ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      VG.Proof.Bignum.X86_64.word s₄.mem B d = VG.Proof.Bignum.X86_64.word s₂.mem B d := fun d hd hd' => by rw [ho₄.word hd hd', hm₃]
  have hab₄ : ∀ d, VG.Proof.Bignum.X86_64.slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₄.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd hd' => by
    rw [hb₄ d (Or.inr (by unfold Public.sMask sFn; omega)) hd', hab₂ d hd hd']
  have hH₄ : Hdr s₄.mem B w minv := by
    have : ∀ i < 16, VG.Proof.Bignum.X86_64.word s₄.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
      rw [hb₄ _ (Or.inl (by unfold Public.sMask sFn; omega)) (by omega),
        hb₂ _ (Or.inl (by unfold Public.sMask sFn; omega)) (by omega), hb₁ _ (by omega)]
    exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (this _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩
  have hwsP₄ : WsAt s₄.mem B op wp mp := hwsP.of_words fun i hi => by
    rw [word_off, word_off]; exact hab₄ _ (by omega) (by omega)
  have kk4 := ((k₁.trans k₂).trans k₃).trans k₄
  have hcP₄ := SubCtx.mk' (hs.congr kk4.2.2) hH₄ hwsP₄ ((k₄.gpr (by decide)).trans hdi₃) hlo (by omega)
  have hoddP : VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI = true → P % 2 = 1 := fun h => by
    simp only [VG.Proof.Bignum.X86_64.keyMask, Bool.and_eq_true, decide_eq_true_eq] at h
    exact VG.Proof.Bignum.X86_64.odd_of_mul_odd h.1.2 hodd
  have hoddQ : VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI = true → Q % 2 = 1 := fun h => by
    simp only [VG.Proof.Bignum.X86_64.keyMask, Bool.and_eq_true, decide_eq_true_eq] at h
    exact VG.Proof.Bignum.X86_64.odd_of_mul_odd (by rw [Nat.mul_comm]; exact h.1.2) hodd
  -- `p := M ? p : 3`.
  refine wp_seqs_append (by simp [primeFix]) (by simp) ?_
  refine WP.mono (primeFix_ok hcP₄ hwp hwp' (by omega) hM₄
    (by rw [wv_off, (show wv s₄.mem B (op + VG.Proof.Bignum.X86_64.slot wp Public.aN) wp = wv s.mem B (op + VG.Proof.Bignum.X86_64.slot wp Public.aN) wp from
      wv_congr fun i hi => hab₄ _ (by omega) (by
        have := slot_le (w := wp) (show Public.aN < 8 by decide); omega)), ← wv_off]; exact hP) hoddP)
    fun s₅ ⟨mp', hcP₅, hP₅, hiP₅, hoP₅, hmP₅, f₅, k₅⟩ => ?_
  have hpr : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot wp Public.aN, 8 * (wp + 2)), (VG.Proof.Bignum.X86_64.slot wp Public.aOne, 8 * (wp + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wp 8 := by
    have := slot_le (w := wp) (show Public.aN < 8 by decide)
    have := slot_le (w := wp) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega
  have ho64 : op < 2 ^ 64 := by omega
  have hb₅ : ∀ d, d + 8 ≤ op → VG.Proof.Bignum.X86_64.word s₅.mem B d = VG.Proof.Bignum.X86_64.word s₄.mem B d := fun d hd =>
    f₅.word_below hpr (by omega) ho64 hd
  have hq₅ : ∀ d, oq ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₅.mem B d = VG.Proof.Bignum.X86_64.word s₄.mem B d := fun d hd hd' =>
    (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega).word_eq (fun r hr => Or.inr (by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀; simp only; omega)) hd'
  have hl₅ : InRegions (s₅.rd ++ s₅.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B op) (8 * sLink)) 8 :=
    hcP₅.good.scr.ld (by unfold sLink sFn; omega)
  have hsQ₅ : VG.Proof.Bignum.X86_64.word s₅.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq := by
    rw [hb₅ _ (by unfold sWsQ sFn; omega), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega))
      (by unfold sWsQ sFn; omega)]; exact hsQ₂
  -- Into `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp [primeFix]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B oq ∧ t.mem = s₅.mem)
    (by xrun [leave, enterQ, State.ea, hdr, hcP₅.rdi, hdrOff, hl₅, hcP₅.link,
      hcP₅.scr.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hsQ₅]) rfl)
    fun s₆ ⟨⟨hdi₆, hm₆⟩, k₆⟩ => ?_
  have hH₆ : Hdr s₆.mem B w minv := by
    rw [hm₆]
    exact ⟨(hb₅ _ (by unfold sW; omega)).trans hH₄.hw, (hb₅ _ (by unfold sMinv; omega)).trans hH₄.hminv,
      fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH₄.harr j hj)⟩
  have hwsQ₆ : WsAt s₆.mem B oq wq mq := by
    rw [hm₆]
    exact hwsQ.of_words fun i hi => by
      rw [word_off, word_off, hq₅ _ (by omega) (by omega), hab₄ _ (by omega) (by omega)]
  have kk6 := (kk4.trans k₅).trans k₆
  have hcQ₆ := SubCtx.mk' (hs.congr kk6.2.2) hH₆ hwsQ₆ hdi₆ (by omega) hoq
  have hM₆ : VG.Proof.Bignum.X86_64.word s₆.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask (VG.Proof.Bignum.X86_64.keyMask m0 N P Q QI) := by
    rw [hm₆, hb₅ _ (by unfold Public.sMask sFn; omega)]; exact hM₄
  refine wp_seqs_append (by simp [primeFix]) (by simp) ?_
  refine WP.mono (primeFix_ok hcQ₆ hwq hwq' (by omega) hM₆
    (by rw [hm₆, wv_off, wv_congr fun i hi => hq₅ _ (by omega) (by
        have := slot_le (w := wq) (show Public.aN < 8 by decide); omega),
      wv_congr fun i hi => hab₄ _ (by omega) (by have := slot_le (w := wq) (show Public.aN < 8 by decide); omega),
      ← wv_off]; exact hQ) hoddQ)
    fun s₇ ⟨mq', hcQ₇, hQ₇, hiQ₇, hoQ₇, _, f₇, k₇⟩ => ?_
  have hqr : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot wq Public.aN, 8 * (wq + 2)), (VG.Proof.Bignum.X86_64.slot wq Public.aOne, 8 * (wq + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wq 8 := by
    have := slot_le (w := wq) (show Public.aN < 8 by decide)
    have := slot_le (w := wq) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega
  have hoq64 : oq < 2 ^ 64 := by omega
  have hb₇ : ∀ d, d + 8 ≤ oq → VG.Proof.Bignum.X86_64.word s₇.mem B d = VG.Proof.Bignum.X86_64.word s₆.mem B d := fun d hd =>
    f₇.word_below hqr (by omega) hoq64 hd
  have hl₇ : InRegions (s₇.rd ++ s₇.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (8 * sLink)) 8 :=
    hcQ₇.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₇.mem)
    (by xrun [leave, State.ea, hdr, hcQ₇.rdi, hdrOff, hl₇, hcQ₇.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have kall := (kk6.trans k₇).trans k'
  have hbt : ∀ d, d + 8 ≤ op → VG.Proof.Bignum.X86_64.word t.mem B d = VG.Proof.Bignum.X86_64.word s₄.mem B d := fun d hd => by
    rw [hm, hb₇ d (by omega), hm₆, hb₅ d hd]
  have hpt : ∀ d, op ≤ d → d + 8 ≤ oq → VG.Proof.Bignum.X86_64.word t.mem B d = VG.Proof.Bignum.X86_64.word s₅.mem B d := fun d hd hd' => by
    rw [hm, hb₇ d hd', hm₆]
  have hpt' : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B op) (8 * i) = VG.Proof.Bignum.X86_64.word s₅.mem (VG.Proof.Bignum.X86_64.off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpt _ (by omega) (by omega)
  have hptv : ∀ d k, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot wp 8 → wv t.mem (VG.Proof.Bignum.X86_64.off B op) d k = wv s₅.mem (VG.Proof.Bignum.X86_64.off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpt _ (by omega) (by omega)
  refine ⟨⟨hs.congr kall.2.2, hdi, ⟨(hbt _ (by unfold sW; omega)).trans hH₄.hw,
      (hbt _ (by unfold sMinv; omega)).trans hH₄.hminv,
      fun j hj => (hbt _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH₄.harr j hj)⟩⟩,
    by rw [hbt _ (by unfold Public.sMask sFn; omega)]; exact hM₄,
    by rw [hbt _ (by unfold sWsP sFn; omega), hb₄ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega))
      (by unfold sWsP sFn; omega)]; exact hsP₂,
    by rw [hbt _ (by unfold sWsQ sFn; omega), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega))
      (by unfold sWsQ sFn; omega)]; exact hsQ₂,
    ⟨mp', hcP₅.ws.of_words fun i hi => hpt' i (by omega), ⟨?_, ?_, ?_⟩,
      by rw [hpt' _ (by decide)]; exact hmP₅⟩,
    ⟨mq', by rw [hm]; exact hcQ₇.ws, ⟨by rw [hm]; exact hQ₇, by rw [hm]; exact hiQ₇, by rw [hm]; exact hoQ₇⟩⟩,
    ?_, ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega)]; exact hP₅
  · rw [word_off, hpt _ (by omega) (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega), ← word_off]
    exact hiP₅
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aOne < 8 by decide); omega)]; exact hoP₅
  · have mem1 : (VG.Proof.Bignum.X86_64.slot w Public.aAcc, 8 * (2 * w + 2)) ∈ [(VG.Proof.Bignum.X86_64.slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, VG.Proof.Bignum.X86_64.slot wp 8), (oq, VG.Proof.Bignum.X86_64.slot wq 8)] := by simp
    have mem2 : (8 * Public.sMask, 8) ∈ [(VG.Proof.Bignum.X86_64.slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, VG.Proof.Bignum.X86_64.slot wp 8), (oq, VG.Proof.Bignum.X86_64.slot wq 8)] := by simp
    have g1 := Frm.of_outside ho₁ mem1
    have g2 := Frm.of_outside ho₂ mem2
    have g4 := Frm.of_outside ho₄ mem2
    have g5 := (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega).widen (rs' := [(VG.Proof.Bignum.X86_64.slot w Public.aAcc,
        8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, VG.Proof.Bignum.X86_64.slot wp 8), (oq, VG.Proof.Bignum.X86_64.slot wq 8)]) fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀
      exact ⟨(op, VG.Proof.Bignum.X86_64.slot wp 8), by simp, by simp only; omega, by simp only; omega⟩
    have g7 := (f₇.rebase hoq64 fun r hr => by have := hqr r hr; omega).widen (rs' := [(VG.Proof.Bignum.X86_64.slot w Public.aAcc,
        8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, VG.Proof.Bignum.X86_64.slot wp 8), (oq, VG.Proof.Bignum.X86_64.slot wq 8)]) fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hqr r₀ hr₀
      exact ⟨(oq, VG.Proof.Bignum.X86_64.slot wq 8), by simp, by simp only; omega, by simp only; omega⟩
    rw [hm₃] at g4
    rw [hm₆] at g7
    rw [hm]
    exact (((g1.trans g2).trans g4).trans g5).trans g7
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs`. -/
section

/-!
# RSA with the CRT on x86-64: constant time, the pieces

Two runs agree on the public data (the pointers, the lengths and `n`) but
not on the input or the private key. Each piece of `main` is constant time
for the hypotheses of its correctness lemma, with what is public fixed (a
`…Pub` structure) and the rest (`-p⁻¹`, `p`, the exponents, the values in
the arrays) existential (a `…Pre` predicate).

The small pieces are proven here; the others are stated (`…CT`) so that
the phases can be proven from them before them.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Clearing, copying and masking an array -/

theorem GoodW.hl {L : Ws} {s : State} (h : GoodW L s) :
    ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi => by
  obtain ⟨_, hg, hZ⟩ := h
  have hn := hg.scr.nowrap
  exact hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)

theorem pins_of {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a s₁ s₂ h₁ h₂ r hr => (h a s₁ h₁ r hr).trans (h a s₂ h₂ r hr).symm

/-- `zeroArr j`, given that the taint analysis checks its header loads from
`rdi` (`by taint_decide` for a given `j`). -/
theorem zeroArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc).isSome = true) :
    RelCT isa (Two GoodW) (Crt.zeroArr j) fun _ _ => True := by
  unfold Crt.zeroArr
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w j) ∧
      t.gpr .r12 = BitVec.ofNat 64 L.w) [.rdi] pins_goodW hT fun L s h => ?_)
    (two_taint [.r8, .r12] (VG.Proof.Bignum.X86_64.pins_of (fun L r => if r = .r8 then VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w j) else BitVec.ofNat 64 L.w)
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w j) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun _ h => h.1

/-- `copyArr o a`, given that the taint analysis checks its header loads. -/
theorem copyArr_ct {o a : Nat} (ho : o < 8) (ha : a < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))),
      .mov .rbx (.mem (hdr (sArr o)))]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (Crt.copyArr o a)) fun _ _ => True := by
  unfold Crt.copyArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w a) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o)) [.rdi] pins_goodW hT fun L s h => ?_)
    (two_taint [.r12, .rsi, .rbx] (VG.Proof.Bignum.X86_64.pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else
        if r = .rsi then VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w a) else VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w a) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr o) (by unfold sArr; omega), hl sW (by decide), hg.hdr.harr a ha, hg.hdr.harr o ho,
      hg.hdr.hw]) rfl) fun _ h => h.1

/-- `maskArr j`, given that the taint analysis checks its header loads. -/
theorem maskArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r15 (.mem (hdr sMaskX)), .mov .r12 (.mem (hdr sW)),
      .mov .rbx (.mem (hdr (sArr j)))]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (Crt.maskArr j)) fun _ _ => True := by
  unfold Crt.maskArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w j)) [.rdi] pins_goodW hT fun L s h => ?_)
    (two_taint [.r12, .rbx] (VG.Proof.Bignum.X86_64.pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w j))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w j))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      hl sMaskX (by decide), hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun _ h => h.1

/-! ## The other pieces, as claims

Each `…Pre` is the hypotheses of the piece's correctness lemma (named in its
documentation), with the public data fixed by its `…Pub` and the secrets
existential. -/

/-- `gPow_ok`'s data, all public: it computes in `n`'s workspace with `n`
and the prime's length. -/
structure GPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  Bx : Addr
  wx : Nat

/-- `gPow_ok`'s hypotheses, for the workspace base in slot `sl`. -/
def GPre (sl : Nat) (p : VG.Proof.Bignum.X86_64.GPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 30 ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aN) p.w = p.N ∧
    ((VG.Proof.Bignum.X86_64.word s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aN)).toNat * p.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aOne) p.w = 1 ∧ sl < 32 ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sl) = p.Bx ∧
    VG.Proof.Bignum.X86_64.word s.mem p.Bx (8 * sW) = BitVec.ofNat 64 p.wx ∧ InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.Bx (8 * sW)) 8 ∧
    1 ≤ p.wx ∧ p.wx ≤ p.w

/-- `gPow M.mm sl` is constant time. -/
def GPowCT (M : Mont) (sl : Nat) : Prop :=
  RelCT isa (Two (VG.Proof.Bignum.X86_64.GPre sl)) (seqs (Crt.gPow M.mm sl)) fun _ _ => True

/-- The public data of a prime's workspace at `off B o`: `n`'s workspace
(`B`, `Z`, `w`) and the prime's size `wx`. -/
structure XPub where
  B : Addr
  Z : Nat
  o : Nat
  w : Nat
  wx : Nat

/-- A prime's workspace, as Montgomery multiplication sees it. -/
abbrev XPub.ws (p : VG.Proof.Bignum.X86_64.XPub) : Ws := ⟨VG.Proof.Bignum.X86_64.off p.B p.o, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩

/-- `redc_ok`'s hypotheses. -/
def RPre (j : Nat) (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx s p.B p.Z p.o p.w p.wx minv ∧ XVals s p.B p.o p.wx minv X ∧
    2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30 ∧ 1 < X ∧ j < 8

/-- `redc M.mm j` is constant time. -/
def RedcCT (M : Mont) (j : Nat) : Prop :=
  RelCT isa (Two (VG.Proof.Bignum.X86_64.RPre j)) (seqs (Crt.redc M.mm j)) fun _ _ => True

/-- The public data of a byte string read from a prime's workspace: its
pointer and length. -/
structure BPub where
  x : VG.Proof.Bignum.X86_64.XPub
  ptr : Addr
  len : Nat

/-- `crtExpLoop_ok`'s hypotheses, for the exponent's pointer and length in
`n`'s slots `sp` and `sl`. -/
def EPre (sp sl : Nat) (p : VG.Proof.Bignum.X86_64.BPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X x y : Nat) (eb : List Byte),
    SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 30 ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aN) p.x.wx = X ∧
    ((VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
    X % 2 = 1 ∧ wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx aXc) p.x.wx < X ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx aXc) p.x.wx % X = x * 2 ^ (64 * p.x.wx) % X ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx < X ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx % X = y * 2 ^ (64 * p.x.wx) % X ∧
    sp < 32 ∧ sl < 32 ∧ VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * sp) = p.ptr ∧
    VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.x.B p.x.Z p.ptr eb

/-- `expLoop M.mm sp sl` is constant time. -/
def ExpCT (M : Mont) (sp sl : Nat) : Prop :=
  RelCT isa (Two (VG.Proof.Bignum.X86_64.EPre sp sl)) (seqs (Crt.expLoop M.mm sp sl)) fun _ _ => True

/-- `primeLoad_ok`'s hypotheses. -/
def LPre (j sp sl : Nat) (p : VG.Proof.Bignum.X86_64.BPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (bs : List Byte), SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧
    p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 30 ∧ j < 8 ∧ sp < 32 ∧ sl < 32 ∧ VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * sp) = p.ptr ∧
    VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length ∧ bs.length = p.len ∧ Src s p.x.B p.x.Z p.ptr bs ∧
    1 ≤ bs.length ∧ bs.length < 2 ^ 31 ∧ (bs.length + 7) / 8 ≤ p.x.wx

/-- `loadArr j sp sl` is constant time. -/
def LoadCT (j sp sl : Nat) : Prop :=
  RelCT isa (Two (VG.Proof.Bignum.X86_64.LPre j sp sl)) (seqs (loadArr j sp sl)) fun _ _ => True

/-- The public data of the setup: `n`'s workspace, `-n⁻¹`, the primes'
lengths and the pointers to `p`, `q` and `qInv`. -/
structure SetupPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  pl : Nat
  ql : Nat
  pp : Addr
  qp : Addr
  ip : Addr

/-- `primesSetup_ok`'s hypotheses. -/
def SetupPre (p : VG.Proof.Bignum.X86_64.SetupPub) (s : State) : Prop :=
  ∃ pb qb ib : List Byte, VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sP) = p.pp ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sQ) = p.qp ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sQinv) = p.ip ∧
    Src s p.B p.Z p.pp pb ∧ Src s p.B p.Z p.qp qb ∧ Src s p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

/-- `primesSetup` is constant time. -/
def SetupCT : Prop := RelCT isa (Two VG.Proof.Bignum.X86_64.SetupPre) (seqs primesSetup) fun _ _ => True

/-- The public data of the checks: `n`'s workspace, `-n⁻¹`, `n` and the
primes' workspaces. -/
structure ChecksPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  op : Nat
  oq : Nat
  wp : Nat
  wq : Nat

/-- `checks_ok`'s hypotheses. -/
def ChecksPre (p : VG.Proof.Bignum.X86_64.ChecksPub) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q QI : Nat) (m0 : Bool), VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧ p.op + VG.Proof.Bignum.X86_64.slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + VG.Proof.Bignum.X86_64.slot p.wq 8 + tabBytes p.wq ≤ p.Z ∧
    2 ≤ p.wp ∧ p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.B p.op ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ WsAt s.mem p.B p.op p.wp mp ∧ WsAt s.mem p.B p.oq p.wq mq ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aN) p.w = p.N ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask m0 ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (VG.Proof.Bignum.X86_64.slot p.wp Public.aN) p.wp = P ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot p.wq Public.aN) p.wq = Q ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (VG.Proof.Bignum.X86_64.slot p.wp aChunk) p.wp = QI ∧ p.N % 2 = 1

/-- `checks` is constant time. -/
def ChecksCT : Prop := RelCT isa (Two VG.Proof.Bignum.X86_64.ChecksPre) (seqs checks) fun _ _ => True

/-- The public data of the phases' parts: `n`'s workspace, `-n⁻¹`, `n`, the
prime's workspace (its base in slot `sl`). -/
structure UPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  o : Nat
  wx : Nat

/-- `unitPhase_ok`'s hypotheses. -/
def UPre (sl : Nat) (p : VG.Proof.Bignum.X86_64.UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.o ∧
    p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ sl ≠ Crt.sD ∧ sl ≠ Public.sCnt ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sl) = VG.Proof.Bignum.X86_64.off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1

/-- The phases' first part (`unitPhase_ok`) is constant time. -/
def UnitCT (M : Mont) (sl : Nat) : Prop :=
  RelCT isa (Two (VG.Proof.Bignum.X86_64.UPre sl)) (seqs (Crt.gPow M.mm sl ++ [.block [.mov .rdi (.mem (hdr sl))]] ++
    redc M.mm Public.aY ++ copyArr Public.aY aXc ++ [.block [leave]])) fun _ _ => True

/-- `powPhase_ok`'s hypotheses, for the exponent's pointer and length in
slots `sd` and `slen`. -/
def PwPre (sl sd slen : Nat) (p : VG.Proof.Bignum.X86_64.BPub) (s : State) : Prop :=
  ∃ (minv mx : BitVec 64) (N X C : Nat) (eb : List Byte), VG.Proof.Bignum.X86_64.Good s p.x.B p.x.Z p.x.w minv ∧ p.x.w < 2 ^ 28 ∧
    VG.Proof.Bignum.X86_64.slot p.x.w 8 ≤ p.x.o ∧ p.x.o + VG.Proof.Bignum.X86_64.slot p.x.wx 8 + tabBytes p.x.wx ≤ p.x.Z ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ sl < 32 ∧
    VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * sl) = VG.Proof.Bignum.X86_64.off p.x.B p.x.o ∧ WsAt s.mem p.x.B p.x.o p.x.wx mx ∧
    XVals s p.x.B p.x.o p.x.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    wv s.mem p.x.B (VG.Proof.Bignum.X86_64.slot p.x.w Public.aY) p.x.w % N = C * 2 ^ (64 * p.x.wx * (nChunks p.x.w p.x.wx + 1)) % N ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx < X ∧
    (X ∣ N → wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx % X = 2 ^ (64 * p.x.wx) % X) ∧
    sd < 32 ∧ slen < 32 ∧ VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * sd) = p.ptr ∧
    VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * slen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.x.B p.x.Z p.ptr eb

/-- The phases' exponentiation (`powPhase_ok`) is constant time. -/
def PowCT (M : Mont) (sl sd slen : Nat) : Prop :=
  RelCT isa (Two (VG.Proof.Bignum.X86_64.PwPre sl sd slen)) (seqs ([.block [.mov .rdi (.mem (hdr sl))]] ++ redc M.mm Public.aY ++
    Crt.expLoop M.mm sd slen)) fun _ _ => True

/-- The public data of a prime's phase: `n`'s workspace, `-n⁻¹`, `n`, the
prime's workspace and the exponent's pointer and length. -/
structure PhasePub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  o : Nat
  wx : Nat
  ep : Addr
  len : Nat

/-- `qPhase_ok`'s hypotheses. -/
def QPre (p : VG.Proof.Bignum.X86_64.PhasePub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X C : Nat) (eb : List Byte), VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.o ∧ p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N ∧
    XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sDq) = p.ep ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.B p.Z p.ep eb

/-- `qPhase M.mm` is constant time. -/
def QPhaseCT (M : Mont) : Prop := RelCT isa (Two VG.Proof.Bignum.X86_64.QPre) (seqs (qPhase M.mm)) fun _ _ => True

/-- The public data of `p`'s phase: also `q`'s workspace and `qInv`'s
pointer. -/
structure PPhasePub where
  ph : VG.Proof.Bignum.X86_64.PhasePub
  oq : Nat
  wq : Nat
  qp : Addr

/-- `pPhase_ok`'s hypotheses. -/
def PPre (p : VG.Proof.Bignum.X86_64.PPhasePub) (s : State) : Prop :=
  ∃ (mx mq : BitVec 64) (X C : Nat) (eb qib : List Byte) (c : Bool), VG.Proof.Bignum.X86_64.Good s p.ph.B p.ph.Z p.ph.w p.ph.minv ∧
    8 ≤ p.ph.w ∧ p.ph.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.ph.w 8 ≤ p.ph.o ∧
    p.ph.o + VG.Proof.Bignum.X86_64.slot p.ph.wx 8 + tabBytes p.ph.wx ≤ p.oq ∧ p.oq + VG.Proof.Bignum.X86_64.slot p.wq 8 + tabBytes p.wq ≤ p.ph.Z ∧
    2 ≤ p.ph.wx ∧ p.ph.wx ≤ p.ph.w ∧ 1 ≤ p.wq ∧ p.wq ≤ p.ph.w ∧
    VG.Proof.Bignum.X86_64.word s.mem p.ph.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.ph.B p.ph.o ∧ WsAt s.mem p.ph.B p.ph.o p.ph.wx mx ∧
    VG.Proof.Bignum.X86_64.word s.mem p.ph.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.ph.B p.oq ∧ WsAt s.mem p.ph.B p.oq p.wq mq ∧
    NVals s p.ph.B p.ph.w p.ph.minv p.ph.N ∧ p.ph.N % 2 = 1 ∧ 1 < p.ph.N ∧
    wv s.mem p.ph.B (VG.Proof.Bignum.X86_64.slot p.ph.w Public.aXm) p.ph.w % p.ph.N = C * 2 ^ (64 * p.ph.w) % p.ph.N ∧
    XVals s p.ph.B p.ph.o p.ph.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.ph.B p.ph.o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c ∧ (c = true → X ∣ p.ph.N) ∧
    VG.Proof.Bignum.X86_64.word s.mem p.ph.B (8 * sDp) = p.ph.ep ∧ VG.Proof.Bignum.X86_64.word s.mem p.ph.B (8 * sPlen) = BitVec.ofNat 64 eb.length ∧
    eb.length = p.ph.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧ Src s p.ph.B p.ph.Z p.ph.ep eb ∧
    VG.Proof.Bignum.X86_64.word s.mem p.ph.B (8 * sQinv) = p.qp ∧ qib.length = eb.length ∧ Src s p.ph.B p.ph.Z p.qp qib ∧
    (qib.length + 7) / 8 ≤ p.ph.wx ∧ (c = true → Spec.Rsa.os2ip qib < X)

/-- `pPhase M.mm` is constant time. -/
def PPhaseCT (M : Mont) : Prop := RelCT isa (Two VG.Proof.Bignum.X86_64.PPre) (seqs (pPhase M.mm)) fun _ _ => True

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp`. -/
section

/-!
# RSA with the CRT on x86-64: the exponentiation is constant time

`expLoop` reads the exponent's bytes, a secret, but at public addresses (its
pointer plus the byte index), and reads its table by a masked selection
from every entry, the mask computed from each window: the windows flow only
into data. Its loops count public numbers (the exponent's length, 2
windows a byte, 16 entries and the table's 14 products), the products are
Montgomery multiplications (constant time for any prime, `Mont.ct`), and
the addresses come from the header, which the steps' correctness
(`CrtExp.lean`, for the bounds alone: `Q := False`) pins in both runs.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The prime's workspace of `p` and its context, as the steps' bounds need it. -/
def XCtx (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc ∧ Xc < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

theorem XCtx.goodW {p : VG.Proof.Bignum.X86_64.XPub} {s : State} (h : VG.Proof.Bignum.X86_64.XCtx p s) : GoodW p.ws s :=
  let ⟨minv, _, _, hc, _⟩ := h; ⟨minv, hc.good, Nat.le_refl _⟩

theorem XCtx.rdi {p : VG.Proof.Bignum.X86_64.XPub} {s : State} (h : VG.Proof.Bignum.X86_64.XCtx p s) : s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o :=
  let ⟨_, _, _, hc, _⟩ := h; hc.good.rdi

theorem pins_rdi {α : Type} {Φ : α → State → Prop} (f : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = f a) :
    Pins Φ [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_of (fun a _ => f a) fun a s hs r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h a s hs

/-- A block whose only public input is `rdi`, the prime's workspace. -/
theorem rdi_ct {α : Type} {Φ : α → State → Prop} (f : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = f a)
    {c : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_rdi f h) hT

/-! ## Reading an entry -/

/-- After `j` entries of the selection, in the workspace of `p`. -/
def SelI (p : VG.Proof.Bignum.X86_64.XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc v : Nat), TabSelInv t₀ (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc v j s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 16

/-- Before the selection of entry `j`: its bases, `w_X` and the mask. -/
def SelB (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  ∃ lt : Bool, VG.Proof.Bignum.X86_64.Scr t (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx 8 + tabBytes q.1.wx) ∧ t.gpr .rdi = VG.Proof.Bignum.X86_64.off q.1.B q.1.o ∧
    t.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt ∧ t.gpr .r12 = BitVec.ofNat 64 q.1.wx ∧
    t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx (8 + q.2)) ∧
    t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx Crt.aT) ∧
    t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx Crt.aT) ∧ 2 ≤ q.1.wx ∧ q.1.wx < 2 ^ 30 ∧ q.2 < 16

theorem pins_selB : Pins VG.Proof.Bignum.X86_64.SelB [.r8, .rsi, .rbx, .r12] := by
  intro p s₁ s₂ ⟨_, _, _, _, a₁, b₁, c₁, d₁, _⟩ ⟨_, _, _, _, a₂, b₂, c₂, d₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [a₁, a₂]

/-- An entry of the selection leaks the same in runs with the same workspace,
whatever the window. -/
theorem selBody_ct : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => q.2 < 16 ∧ VG.Proof.Bignum.X86_64.SelI q.1 q.2 s) (seqs VG.Proof.Bignum.X86_64.selBody)
    fun _ _ => True := by
  simp only [VG.Proof.Bignum.X86_64.selBody, seqs]
  -- The mask and the bases.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.SelB) [.rdi] (VG.Proof.Bignum.X86_64.pins_rdi (fun q => VG.Proof.Bignum.X86_64.off q.1.B q.1.o)
    fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi) (by taint_decide) fun q s ⟨hj, t₀, minv, X, Xc, v, hI, hw, hw', hv⟩ =>
      WP.mono (selHead_ok hI.ctx hj hv hI.idx hI.nib hI.ent) fun t ⟨hbp, h12, h8, hsi, hbx, _, k⟩ =>
        ⟨_, hI.ctx.scrT.congr k.2.2, (k.gpr (by decide)).trans hI.ctx.good.rdi, hbp, h12, h8, hsi, hbx, hw, hw', hj⟩) ?_
  -- `T := j = v ? T_j : T`.
  refine RelCT.seq (two_post (Ψ := fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off q.1.B q.1.o)
    (two_taint [.r8, .rsi, .rbx, .r12] VG.Proof.Bignum.X86_64.pins_selB (by taint_decide)) fun q s h => ?_) ?_
  · obtain ⟨lt, hs, hdi, hbp, h12, h8, hsi, hbx, hw, hw', hj⟩ := h
    have hn := hs.nowrap
    have hT0 := slot_le (w := q.1.wx) (show Crt.aT < 8 by decide)
    have hE := ent_le q.1.wx hj
    have hTE := VG.Proof.Bignum.X86_64.slot_sep (w := q.1.wx) (show Crt.aT ≠ 8 + q.2 by unfold Crt.aT; omega)
    exact WP.mono (sseSelect_ok hs h8 hbx h12 hbp (by omega) (by omega) (by omega) (by omega)
      (by omega)) fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hdi
  -- The next entry, and the index.
  exact VG.Proof.Bignum.X86_64.rdi_ct (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)

/-- `tabSel_ok`'s hypotheses. -/
def SelP (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc v : Nat), CExpCtx s (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    v < 16 ∧ VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * Crt.sTab) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8) ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

/-- The selection leaks the same in runs with the same workspace. -/
theorem tabSel_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.SelP) (seqs Crt.tabSelect) fun _ _ => True := by
  rw [tabSelect_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < 16 ∧ VG.Proof.Bignum.X86_64.SelI p 0 s) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_rdi (fun p : VG.Proof.Bignum.X86_64.XPub => VG.Proof.Bignum.X86_64.off p.B p.o) fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.rdi) (by taint_decide)
    fun p s ⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩ => ?_) ?_
  · have hn := hc.scrT.nowrap
    refine WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ⟨by decide, t₁, minv, X, Xc, v, ?_, hw, hw', hv⟩
    have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (d := 8 * Crt.sEnt) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8)) (by decide)
    have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * Crt.sEnt)) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8)))
      (VG.Proof.Bignum.X86_64.off p.B p.o) (d := 8 * Crt.sJ) (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
    rw [← hm₁] at o2
    have f₁ : Frm (VG.Proof.Bignum.X86_64.off p.B p.o) (selRanges p.wx) s.mem t₁.mem :=
      (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
    refine ⟨hc.of_win (f₁.mono (selRanges_sub p.wx)) k₁.2.2 (k₁.gpr (by decide)), ?_, ?_, ?_, by simp,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]
    · rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
  exact (two_loop (Φ := VG.Proof.Bignum.X86_64.SelI) (Ψ := fun _ _ => True) (fun _ => 16) VG.Proof.Bignum.X86_64.selBody_ct
    fun p j s hj ⟨t₀, minv, X, Xc, v, hI, hw, hw', hv⟩ =>
      WP.mono (selStep_ok hw hw' hv hj hI) fun s' ⟨hz, hI'⟩ =>
        ⟨VG.Proof.Bignum.X86_64.eval_ne_count hj hz, fun _ => ⟨t₀, minv, X, Xc, v, hI', hw, hw', hv⟩, fun _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## A window -/

/-- After `j` windows of a byte, in the prime's workspace of `p`. -/
def WinI (p : VG.Proof.Bignum.X86_64.XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc E v : Nat),
    CWinInv t₀ (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc False 0 E v j s ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X ∧ Xc < X ∧ v < 256

/-- Within a window: the workspace, its table, `Y < X` and the value in `sV`. -/
def WinQ (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc V : Nat), CExpCtx t (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc ∧
    CTab t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx X False 0 ∧ wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx < X ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 56 ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

theorem WinQ.goodW {p : VG.Proof.Bignum.X86_64.XPub} {t : State} (h : VG.Proof.Bignum.X86_64.WinQ p t) : GoodW p.ws t :=
  let ⟨minv, _, _, _, hc, _⟩ := h; ⟨minv, hc.good, Nat.le_refl _⟩

theorem WinQ.rdi {p : VG.Proof.Bignum.X86_64.XPub} {t : State} (h : VG.Proof.Bignum.X86_64.WinQ p t) : t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o :=
  let ⟨_, _, _, _, hc, _⟩ := h; hc.good.rdi

/-- A squaring keeps `WinQ`. -/
theorem winSq_q (M : Mont) {p : VG.Proof.Bignum.X86_64.XPub} {s : State} (h : VG.Proof.Bignum.X86_64.WinQ p s) :
    WP isa (M.mm Public.aY Public.aY Public.aY) s (VG.Proof.Bignum.X86_64.WinQ p) := by
  obtain ⟨minv, X, Xc, V, hc, htab, hY, hV, hV', hw, hw', hR⟩ := h
  refine WP.mono (crtSq_ok M (Q := False) (x := 0) (E := 0) hc hw hw' hR hY False.elim)
    fun t ⟨hc', hY', _, hh, hf, _⟩ => ⟨minv, X, Xc, V, hc', htab.of_win hf hc.scrT.nowrap, hY', ?_, hV', hw, hw', hR⟩
  rw [hh _ (by decide)]; exact hV

/-- Before the selection: `tabSel_ok`'s hypotheses, and the rest of `WinQ`. -/
def WinS (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.SelP p t ∧ ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx t (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc ∧
    CTab t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx X False 0 ∧ wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx < X ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

/-- After the selection: `T < X`, for `Y := Y T`. -/
def WinT (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx t (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc ∧
    wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Crt.aT) p.wx < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- A window leaks the same in runs with the same workspace, whatever the window. -/
theorem crtWin_ct (M : Mont) :
    RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => q.2 < 2 ∧ VG.Proof.Bignum.X86_64.WinI q.1 q.2 s) (seqs (Crt.expWin M.mm))
      fun _ _ => True := by
  rw [expWin_eq]
  refine RelCT.seqs_append (by simp) (by simp [tabSelect_eq]) ?_
  have sq : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinQ q.1 s) (M.mm Public.aY Public.aY Public.aY)
      (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinQ q.1 s) :=
    two_post (two_map (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => q.1.ws) (fun _ _ h => h.goodW) (M.ct (by unfold MmUse; decide)))
      fun _ _ h => VG.Proof.Bignum.X86_64.winSq_q M h
  -- Four squarings.
  have sq0 : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => q.2 < 2 ∧ VG.Proof.Bignum.X86_64.WinI q.1 q.2 s) (M.mm Public.aY Public.aY Public.aY)
      (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinQ q.1 s) :=
    two_post (two_map (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => q.1.ws)
      (fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => ⟨_, hI.ctx.good, Nat.le_refl _⟩)
      (M.ct (by unfold MmUse; decide))) fun q s ⟨_, t₀, minv, X, Xc, E, v, hI, hw, hw', hR, hXN, hv⟩ => by
        have hp : v * 16 ^ q.2 < 2 ^ 56 := by
          have : 16 ^ q.2 ≤ 16 := by rcases (show q.2 = 0 ∨ q.2 = 1 by omega) with h | h <;> rw [h] <;> decide
          have := Nat.mul_le_mul_left v this; omega
        exact VG.Proof.Bignum.X86_64.winSq_q M ⟨minv, X, Xc, _, hI.ctx, hI.tab, hI.ylt, hI.v, hp, hw, hw', hR⟩
  -- The window, and `sV` up.
  have mid : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinQ q.1 s)
      (.block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr Crt.sV) .rax,
        .shift .shr .rdx 4, .alu .and .rdx (.imm 15), .store (hdr Crt.sNib) .rdx])
      (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinS q.1 s) := by
    refine two_piece [.rdi] (VG.Proof.Bignum.X86_64.pins_rdi (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => VG.Proof.Bignum.X86_64.off q.1.B q.1.o) fun _ _ h => h.rdi) (by taint_decide)
      fun q s h => ?_
    obtain ⟨minv, X, Xc, V, hc, htab, hY, hV, hV', hw, hw', hR⟩ := h
    have hn := hc.scrT.nowrap
    refine WP.mono (winMid_ok hc hV (by omega)) fun t ⟨hm, k⟩ => ?_
    have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (d := 8 * Crt.sV) (BitVec.ofNat 64 (16 * V)) (by decide)
    have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V)))
      (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 (V / 16 % 16)) (by decide)
    rw [← hm] at o2
    have f : Frm (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (crtWinRanges q.1.wx) s.mem t.mem :=
      (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
    have hc' := hc.of_win f k.2.2 (k.gpr (by decide))
    have hY0 := slot_le (w := q.1.wx) (show Public.aY < 8 by decide)
    have hYe : wv t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx Public.aY) q.1.wx =
        wv s.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx Public.aY) q.1.wx := by
      rw [o2.wv (by have := hdr_lt_slot q.1.wx Public.aY (show Crt.sNib < 32 by decide); omega) (by omega),
        o1.wv (by have := hdr_lt_slot q.1.wx Public.aY (show Crt.sV < 32 by decide); omega) (by omega)]
    exact ⟨⟨minv, X, Xc, V / 16 % 16, hc', hw, hw', Nat.mod_lt _ (by decide), by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
          hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact htab.tab,
        by rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self]⟩,
      minv, X, Xc, hc', htab.of_win f hn, hYe ▸ hY, hR⟩
  refine RelCT.seq (R := Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinS q.1 s) ?_ ?_
  · simp only [seqs]
    exact RelCT.seq sq0 (RelCT.seq sq (RelCT.seq sq (RelCT.seq sq mid)))
  -- The selection, `Y := Y T` and the count.
  refine RelCT.seqs_append (by simp [tabSelect_eq]) (by simp) ?_
  refine RelCT.seq (two_post (Ψ := fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.WinT q.1 s)
    (two_map (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => q.1) (fun _ _ h => h.1) VG.Proof.Bignum.X86_64.tabSel_ct) fun q s h => ?_) ?_
  · obtain ⟨⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩, minv', X', Xc', hc₂, htab, -, -⟩ := h
    refine WP.mono (tabSel_ok hc hw hw' hv ht hN) fun t ⟨hc', hT, _, _⟩ => ⟨minv, X, Xc, hc', ?_, hw, hw'⟩
    have hX : X' = X := hc₂.n.symm.trans hc.n
    rw [hT, ← hX]; exact htab.lt _ hv
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off q.1.B q.1.o)
    (two_map (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => q.1.ws) (fun _ _ ⟨minv, _, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (M.ct (o := Public.aY) (a := Public.aY) (b := Crt.aT) (by unfold MmUse; decide)))
    fun q s ⟨minv, X, Xc, hc, hT, hw, hw'⟩ => ?_) ?_
  · exact WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hT)) fun t ⟨hg, _⟩ => hg.rdi
  exact VG.Proof.Bignum.X86_64.rdi_ct (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)

/-- The two windows of a byte leak the same in runs with the same workspace. -/
theorem crtWins_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 2 ∧ VG.Proof.Bignum.X86_64.WinI p 0 s) (.loop (seqs (Crt.expWin M.mm)) .ne)
      (Two fun p s => VG.Proof.Bignum.X86_64.WinI p 2 s) :=
  two_loop (Φ := VG.Proof.Bignum.X86_64.WinI) (fun _ => 2) (VG.Proof.Bignum.X86_64.crtWin_ct M)
    fun _ _ _ hj ⟨t₀, minv, X, Xc, E, v, hI, hw, hw', hR, hXN, hv⟩ =>
      WP.mono (crtWinStep_ok M hw hw' hR hv hj hI) fun _ ⟨hz, hI'⟩ =>
        ⟨VG.Proof.Bignum.X86_64.eval_ne_count hj hz, fun _ => ⟨t₀, minv, X, Xc, E, v, hI', hw, hw', hR, hXN, hv⟩,
          fun h => h ▸ ⟨t₀, minv, X, Xc, E, v, hI', hw, hw', hR, hXN, hv⟩⟩

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (at `a.ptr`, `a.len` bytes). -/
def CBytesInv (a : VG.Proof.Bignum.X86_64.BPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat) (eb : List Byte),
    CByteInv t₀ (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) a.x.wx minv X Xc False 0 a.ptr eb.length eb i s ∧ 2 ≤ a.x.wx ∧
    a.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) X ∧ Xc < X ∧
    eb.length = a.len ∧ eb.length < 2 ^ 31 ∧ Src t₀ a.x.B a.x.Z a.ptr eb ∧
    ∀ i < eb.length, VG.Proof.Bignum.X86_64.slot a.x.wx 8 + tabBytes a.x.wx ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i)

/-- After the loads of the byte's address. -/
def CHeadMid (q : VG.Proof.Bignum.X86_64.BPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.CBytesInv q.1 q.2 s ∧ s.gpr .rax = q.1.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

theorem pins_cBytes : Pins (fun (q : VG.Proof.Bignum.X86_64.BPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.CBytesInv q.1 q.2 s) [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_rdi (fun q : VG.Proof.Bignum.X86_64.BPub × Nat => VG.Proof.Bignum.X86_64.off q.1.x.B q.1.x.o) fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi

theorem pins_cHeadMid : Pins VG.Proof.Bignum.X86_64.CHeadMid [.rdi, .rax, .rcx] := by
  rintro q s₁ s₂ ⟨-, ⟨_, _, _, _, _, i₁, _⟩, a₁, c₁⟩ ⟨-, ⟨_, _, _, _, _, i₂, _⟩, a₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of the exponent leaks the same in runs with the same workspace
and the same exponent's pointer and length. -/
theorem crtByte_ct (M : Mont) : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.BPub × Nat) s => q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.CBytesInv q.1 q.2 s)
    (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (Crt.expWin M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) fun _ _ => True := by
  simp only [seqs]
  rw [crtByteHead_eq]
  have w₁ : ∀ (q : VG.Proof.Bignum.X86_64.BPub × Nat) s, q.2 < q.1.len ∧ VG.Proof.Bignum.X86_64.CBytesInv q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) s (VG.Proof.Bignum.X86_64.CHeadMid q) := by
    rintro q s ⟨hi, t₀, minv, X, Xc, eb, hI, hrest⟩
    exact WP.mono (crtByteHead1_ok hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, minv, X, Xc, eb, h3, hrest⟩, h1, h2⟩
  have w₂ : ∀ (q : VG.Proof.Bignum.X86_64.BPub × Nat) s, VG.Proof.Bignum.X86_64.CHeadMid q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
        .mov32 .rax (.imm 2), .store (hdr Crt.sBit) .rax]) s fun t => 0 < 2 ∧ VG.Proof.Bignum.X86_64.WinI q.1.x 0 t := by
    rintro q s ⟨hi, ⟨t₀, minv, X, Xc, eb, hI, hw, hw', hR, hXN, hL, -, he, hout⟩, hax, hcx⟩
    have hi' : q.2 < eb.length := by omega
    exact WP.mono (crtByteHead2_ok rfl hi' he.rd he.val hout hI hax hcx) fun t ⟨_, _, hB⟩ =>
      ⟨by decide, t, minv, X, Xc, _, _, hB, hw, hw', hR, hXN, (eb[q.2]'hi').isLt⟩
  have h₃ : RelCT isa (Two fun (p : VG.Proof.Bignum.X86_64.XPub) s => VG.Proof.Bignum.X86_64.WinI p 2 s)
      (.block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]) fun _ _ => True :=
    VG.Proof.Bignum.X86_64.rdi_ct (fun p : VG.Proof.Bignum.X86_64.XPub => VG.Proof.Bignum.X86_64.off p.B p.o) (fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq (two_piece _ VG.Proof.Bignum.X86_64.pins_cBytes (by taint_decide) w₁)
      (two_piece _ VG.Proof.Bignum.X86_64.pins_cHeadMid (by taint_decide) w₂)))
    (RelCT.seq (two_map (fun q : VG.Proof.Bignum.X86_64.BPub × Nat => q.1.x) (fun _ _ h => h) (VG.Proof.Bignum.X86_64.crtWins_ct M)) h₃)

/-! ## The table -/

/-- `toEnt a` into entry `q.2`: its bases, as the header gives them. -/
def EntP (a : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.XCtx q.1 s ∧ VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx (8 + q.2)) ∧
    q.2 < 16 ∧ a < 8

/-- `toEnt a`'s bases. -/
def EntB (a : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 q.1.wx ∧ s.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx a) ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx (8 + q.2))

theorem pins_entB (a : Nat) : Pins (VG.Proof.Bignum.X86_64.EntB a) [.r12, .rsi, .rbx] := by
  intro q s₁ s₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]

/-- `toEnt a` leaks the same in runs with the same workspace and entry,
given that the taint analysis checks its loads from `rdi`. -/
theorem toEnt_ct {a : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))),
      .mov .rbx (.mem (hdr Crt.sEnt))]) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.EntP a)) (seqs (Crt.toEnt a)) fun _ _ => True := by
  unfold Crt.toEnt
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.EntB a) [.rdi] (VG.Proof.Bignum.X86_64.pins_rdi (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => VG.Proof.Bignum.X86_64.off q.1.B q.1.o)
    fun _ _ h => h.1.rdi) hT fun q s ⟨⟨minv, X, Xc, hc, _⟩, he, hj, ha⟩ => ?_)
    (two_taint [.r12, .rsi, .rbx] (VG.Proof.Bignum.X86_64.pins_entB a) (by taint_decide))
  exact WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 q.1.wx ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx a) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx (8 + q.2)))
    (by xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sArr a) (by unfold sArr; omega),
      hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide), hc.good.hdr.harr a ha, he,
      hc.good.hdr.hw]) rfl) fun t ⟨h, _⟩ => h

/-- After `i` of the table's products, in the workspace of `p`. -/
def BldI (p : VG.Proof.Bignum.X86_64.XPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat), BuildInv t₀ (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc False 0 i s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X ∧ Xc < X

/-- After the product `i`: the entry `i + 1` in `sEnt`. -/
def BldM (q : VG.Proof.Bignum.X86_64.XPub × Nat) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.XCtx q.1 s ∧ VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx (8 + (q.2 + 1))) ∧
    q.2 < 14

/-- A product of the table's build leaks the same in runs with the same workspace. -/
theorem buildBody_ct (M : Mont) :
    RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => q.2 < 14 ∧ VG.Proof.Bignum.X86_64.BldI q.1 q.2 s)
      (seqs (tabBody M.mm)) fun _ _ => True := by
  -- `T := T Xc`.
  have mmPart : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => q.2 < 14 ∧ VG.Proof.Bignum.X86_64.BldI q.1 q.2 s) (M.mm Crt.aT Crt.aT Crt.aXc)
      (Two VG.Proof.Bignum.X86_64.BldM) := by
    refine two_post (two_map (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => q.1.ws)
      (fun _ _ ⟨_, _, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
      (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide)))
      fun q s ⟨hi, t₀, minv, X, Xc, hI, hw, hw', hR, hXN⟩ => ?_
    have hc := hI.ctx
    refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _) hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.x, hc.n]; exact hXN)) fun t ⟨_, _, _, ha, k⟩ => ?_
    have f : Frm (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (buildRanges q.1.wx) s.mem t.mem := Frm.of_arrays ha (by simp [buildRanges])
    exact ⟨⟨minv, X, Xc, hc.of_frm (f.mono (buildRanges_sub q.1.wx)) k.2.2 (k.gpr (by decide)), hXN, hw, hw'⟩,
      by rw [ha.hslot (by decide)]; exact hI.ent, hi⟩
  -- `sEnt` up.
  have entPart : RelCT isa (Two VG.Proof.Bignum.X86_64.BldM) Crt.nextEnt (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.EntP Crt.aT (q.1, q.2 + 2) s) := by
    refine two_post (VG.Proof.Bignum.X86_64.rdi_ct (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (fun _ _ h => h.1.rdi) (by taint_decide))
      fun q s ⟨⟨minv, X, Xc, hc, hXN, hw, hw'⟩, he, hi⟩ => ?_
    refine WP.mono (nextEnt_ok hc he) fun t ⟨hm, k⟩ => ?_
    have o := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (d := 8 * Crt.sEnt)
      (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx (8 + (q.2 + 1)) + 8 * (q.1.wx + 2))) (by decide)
    rw [← hm] at o
    exact ⟨⟨minv, X, Xc, hc.of_frm (Frm.of_outside o (by simp [crtExpRanges, crtWinRanges])) k.2.2
      (k.gpr (by decide)), hXN, hw, hw'⟩, by rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self, ← slot_succ]; rfl, by simp only; omega,
      by decide⟩
  -- Entry `i + 2 := T`, the count.
  have restPart : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.XPub × Nat) s => VG.Proof.Bignum.X86_64.EntP Crt.aT (q.1, q.2 + 2) s)
      (seqs (Crt.toEnt Crt.aT ++
        [.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]]))
      fun _ _ => True := by
    refine RelCT.seqs_append (by simp [Crt.toEnt]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      t.gpr .rdi = VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (two_map (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => (q.1, q.2 + 2)) (fun _ _ h => h)
        (VG.Proof.Bignum.X86_64.toEnt_ct (by taint_decide))) fun q s ⟨⟨minv, X, Xc, hc, _, hw, hw'⟩, he, hj, ha⟩ =>
      WP.mono (toEnt_ok hc hw hw' ha hj he) fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hc.good.rdi) ?_)
    simp only [seqs]
    exact VG.Proof.Bignum.X86_64.rdi_ct (fun q : VG.Proof.Bignum.X86_64.XPub × Nat => VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)
  unfold tabBody
  refine RelCT.seqs_append (by simp) (by simp [Crt.toEnt]) (RelCT.seq ?_ restPart)
  simp only [seqs]
  exact RelCT.seq mmPart entPart

/-- `tabBuild_ok`'s hypotheses, for the bounds. -/
def TPre (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (VG.Proof.Bignum.X86_64.off p.B p.o) p.wx minv X Xc ∧ Xc < X ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

theorem toEnt_post {a : Nat} {q : VG.Proof.Bignum.X86_64.XPub × Nat} {s : State} (h : VG.Proof.Bignum.X86_64.EntP a q s) :
    WP isa (seqs (Crt.toEnt a)) s fun t => VG.Proof.Bignum.X86_64.XCtx q.1 t ∧
      ∀ k < 32, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * k) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * k) := by
  obtain ⟨⟨minv, X, Xc, hc, hXN, hw, hw'⟩, he, hj, ha⟩ := h
  have hn := hc.scrT.nowrap
  have hE := ent_le q.1.wx hj
  have hE8 := slot_mono q.1.wx (show 8 ≤ 8 + q.2 by omega)
  refine WP.mono (toEnt_ok hc hw hw' ha hj he) fun t ⟨_, o, k⟩ => ⟨⟨minv, X, Xc, hc.of_frm
    (Frm.of_outside (o.mono (o' := VG.Proof.Bignum.X86_64.slot q.1.wx 8) (n' := tabBytes q.1.wx) hE8 (by omega)) (by simp [crtExpRanges]))
    k.2.2 (k.gpr (by decide)), hXN, hw, hw'⟩, fun k hk => ?_⟩
  exact o.word (by have := hdr_lt_slot q.1.wx (8 + q.2) hk; omega) (by omega)

/-- The table's first entries leak the same in runs with the same workspace. -/
theorem tabPre_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.TPre) (seqs tabPre) fun _ _ => True := by
  unfold tabPre
  refine RelCT.seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  -- The base.
  refine RelCT.seq (two_post (Ψ := fun p s => VG.Proof.Bignum.X86_64.EntP Public.aY (p, 0) s)
    (VG.Proof.Bignum.X86_64.rdi_ct (fun p : VG.Proof.Bignum.X86_64.XPub => VG.Proof.Bignum.X86_64.off p.B p.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.rdi) (by taint_decide))
    fun p s ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ => ?_) ?_
  · refine WP.mono (tabInit_ok hc) fun t ⟨hm, k⟩ => ?_
    have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (d := 8 * Crt.sTab) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8)) (by decide)
    have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * Crt.sTab)) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8)))
      (VG.Proof.Bignum.X86_64.off p.B p.o) (d := 8 * Crt.sEnt) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8)) (by decide)
    rw [← hm] at o2
    have f : Frm (VG.Proof.Bignum.X86_64.off p.B p.o) (buildRanges p.wx) s.mem t.mem :=
      (Frm.of_outside o1 (by simp [buildRanges])).trans (Frm.of_outside o2 (by simp [buildRanges]))
    exact ⟨⟨minv, X, Xc, hc.of_frm (f.mono (buildRanges_sub p.wx)) k.2.2 (k.gpr (by decide)), hXN, hw, hw'⟩,
      by rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl, by simp only; omega, by decide⟩
  -- `T_0 := Y`.
  refine RelCT.seqs_append (by simp [Crt.toEnt]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p s => VG.Proof.Bignum.X86_64.XCtx p s ∧ VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8))
    (two_map (fun p : VG.Proof.Bignum.X86_64.XPub => (p, 0)) (fun _ _ h => h) (VG.Proof.Bignum.X86_64.toEnt_ct (by taint_decide))) fun p s h =>
      WP.mono (VG.Proof.Bignum.X86_64.toEnt_post h) fun t ⟨hx, hh⟩ => ⟨hx, by rw [hh _ (by decide)]; exact h.2.1⟩) ?_)
  refine RelCT.seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  -- `sEnt` up.
  refine RelCT.seq (two_post (Ψ := fun p s => VG.Proof.Bignum.X86_64.EntP Crt.aXc (p, 1) s)
    (VG.Proof.Bignum.X86_64.rdi_ct (fun p : VG.Proof.Bignum.X86_64.XPub => VG.Proof.Bignum.X86_64.off p.B p.o) (fun _ _ h => h.1.rdi) (by taint_decide))
    fun p s ⟨⟨minv, X, Xc, hc, hXN, hw, hw'⟩, he⟩ => ?_) ?_
  · refine WP.mono (nextEnt_ok hc he) fun t ⟨hm, k⟩ => ?_
    have o := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (d := 8 * Crt.sEnt)
      (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8 + 8 * (p.wx + 2))) (by decide)
    rw [← hm] at o
    exact ⟨⟨minv, X, Xc, hc.of_frm (Frm.of_outside o (by simp [crtExpRanges, crtWinRanges])) k.2.2
      (k.gpr (by decide)), hXN, hw, hw'⟩, by rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self, ← slot_succ], by simp only; omega,
      by decide⟩
  -- `T_1 := Xc`.
  refine RelCT.seqs_append (by simp [Crt.toEnt]) (by simp [Crt.copyArr]) (RelCT.seq (two_post
    (Ψ := fun p s => VG.Proof.Bignum.X86_64.XCtx p s) (two_map (fun p : VG.Proof.Bignum.X86_64.XPub => (p, 1)) (fun _ _ h => h) (VG.Proof.Bignum.X86_64.toEnt_ct (by taint_decide)))
    fun p s h => WP.mono (VG.Proof.Bignum.X86_64.toEnt_post h) fun t ⟨hx, _⟩ => hx) ?_)
  -- `T := Xc`, the count.
  refine RelCT.seqs_append (by simp [Crt.copyArr]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o) (two_map (fun p : VG.Proof.Bignum.X86_64.XPub => p.ws) (fun _ _ h => h.goodW)
      (VG.Proof.Bignum.X86_64.copyArr_ct (by decide) (by decide) (by taint_decide))) fun p s ⟨minv, X, Xc, hc, _, hw, hw'⟩ =>
    WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (o := Crt.aT) (a := Crt.aXc)
      (by decide) (by decide) (by decide)) fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hc.good.rdi) ?_)
  simp only [seqs]
  exact VG.Proof.Bignum.X86_64.rdi_ct (fun p : VG.Proof.Bignum.X86_64.XPub => VG.Proof.Bignum.X86_64.off p.B p.o) (fun _ _ h => h) (by taint_decide)

/-- The table's build leaks the same in runs with the same workspace. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two VG.Proof.Bignum.X86_64.TPre) (seqs (Crt.tabBuild M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine RelCT.seqs_append (by simp [tabPre]) (by simp) (RelCT.seq (two_post (Ψ := fun p s => 0 < 14 ∧ VG.Proof.Bignum.X86_64.BldI p 0 s)
    VG.Proof.Bignum.X86_64.tabPre_ct fun p s ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ =>
      WP.mono (tabPre_ok (Q := False) (x := 0) hc hw hw' hXN False.elim hY False.elim) fun t hI =>
        ⟨by decide, s, minv, X, Xc, hI, hw, hw', hR, hXN⟩) ?_)
  exact (two_loop (Φ := VG.Proof.Bignum.X86_64.BldI) (Ψ := fun _ _ => True) (fun _ => 14) (VG.Proof.Bignum.X86_64.buildBody_ct M)
    fun p i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN⟩ =>
      WP.mono (buildStep_ok M hw hw' hR hXN False.elim hi hI) fun s' ⟨hz, hI'⟩ =>
        ⟨VG.Proof.Bignum.X86_64.eval_ne_count hi hz, fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR, hXN⟩, fun _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The exponentiation -/

/-- `expLoop`'s start: the load of the link, then the rest. -/
theorem crtExpInit_eq (sp sl : Nat) : ([.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx] : List Instr) =
    ([.mov .rax (.mem (hdr Crt.sLink))] : List Instr) ++
    ([.mov .rdx (.mem (Crt.ws .rax sp)), .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)),
      .store (hdr Crt.sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx] : List Instr) := rfl

theorem pins_ePre (sp sl : Nat) : Pins (VG.Proof.Bignum.X86_64.EPre sp sl) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, _, h₁, _⟩ ⟨_, _, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]

/-- The link into `rax`: the modulus' workspace. -/
theorem crtLink_ok {sp sl : Nat} {a : VG.Proof.Bignum.X86_64.BPub} {s : State} (h : VG.Proof.Bignum.X86_64.EPre sp sl a s) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink))]) s fun t =>
      t.gpr .rdi = VG.Proof.Bignum.X86_64.off a.x.B a.x.o ∧ t.gpr .rax = a.x.B := by
  obtain ⟨minv, X, x, y, eb, hc, -⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (8 * Crt.sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot a.x.wx 8 (show Crt.sLink < 32 by decide); omega)
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = a.x.B)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl)
    fun t ⟨h, k⟩ => ⟨(k.gpr (by decide)).trans hc.rdi, h⟩

/-- `expLoop`'s start keeps `tabBuild_ok`'s hypotheses. -/
theorem crtExpInit_tpre {sp sl : Nat} {a : VG.Proof.Bignum.X86_64.BPub} {s : State} (h : VG.Proof.Bignum.X86_64.EPre sp sl a s) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) s (VG.Proof.Bignum.X86_64.TPre a.x) := by
  obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, -⟩ := h
  have hPn := hc.scrT.nowrap
  have hY0 := slot_le (w := a.x.wx) (show Public.aY < 8 by decide)
  have hY1 := hdr_lt_slot a.x.wx Public.aY (show 31 < 32 by decide)
  have hc₀ : CExpCtx s (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) a.x.wx minv X (wv s.mem (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (VG.Proof.Bignum.X86_64.slot a.x.wx Crt.aXc) a.x.wx) :=
    ⟨hc.good, hc.scrT, hn, hinv, rfl⟩
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (d := 8 * Crt.sExp) a.ptr (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr) (VG.Proof.Bignum.X86_64.off a.x.B a.x.o)
    (d := 8 * Crt.sExpLen) (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := VG.Proof.Bignum.X86_64.writeW_outside ((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr).writeW
    (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (crtExpRanges a.x.wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  refine ⟨minv, X, _, hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide)), hxl, ?_, hw2, by omega,
    VG.Proof.Bignum.coprime_pow2 hodd _⟩
  rw [o3.wv (by unfold Crt.sI sFn at *; omega) (by omega), o2.wv (by unfold Crt.sExpLen sFn at *; omega)
    (by omega), o1.wv (by unfold Crt.sExp sFn at *; omega) (by omega)]
  exact hyl

/-- `expLoop M.mm sp sl` is constant time, given that the taint analysis
checks its start after the link's load. -/
theorem crtExpLoop_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    VG.Proof.Bignum.X86_64.ExpCT M sp sl := by
  unfold VG.Proof.Bignum.X86_64.ExpCT
  rw [expLoop_eq, ← List.cons_append]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun a s => 0 < a.len ∧ VG.Proof.Bignum.X86_64.CBytesInv a 0 s) ?_ fun a s h => ?_) ?_)
  · -- The start and the table.
    rw [← List.singleton_append]
    refine RelCT.seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) (RelCT.seq (two_post (Ψ := fun a s => VG.Proof.Bignum.X86_64.TPre a.x s)
      ?_ fun _ _ h => by simp only [seqs, expInit]; exact VG.Proof.Bignum.X86_64.crtExpInit_tpre h) (two_map (fun a : VG.Proof.Bignum.X86_64.BPub => a.x)
        (fun _ _ h => h) (VG.Proof.Bignum.X86_64.tabBuild_ct M)))
    simp only [seqs, expInit]
    rw [VG.Proof.Bignum.X86_64.crtExpInit_eq]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : VG.Proof.Bignum.X86_64.BPub) t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off a.x.B a.x.o ∧
        t.gpr .rax = a.x.B) [.rdi] (VG.Proof.Bignum.X86_64.pins_ePre sp sl) (by taint_decide) fun _ _ h => VG.Proof.Bignum.X86_64.crtLink_ok h)
      (two_taint [.rdi, .rax] (VG.Proof.Bignum.X86_64.pins_of (fun a r => if r = .rdi then VG.Proof.Bignum.X86_64.off a.x.B a.x.o else a.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  · obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, hL, hL1, hL2,
      he⟩ := h
    have hPn := hc.scrT.nowrap
    have hBn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot a.x.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
    have hout : ∀ i < eb.length, VG.Proof.Bignum.X86_64.slot a.x.wx 8 + tabBytes a.x.wx ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) :=
      fun i hi' => by
        have := he.out i hi'
        rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
        · omega
        · omega
    exact WP.mono (crtExpHead_ok M (Q := False) (x := 0) hc hw2 hwx hw30 hn hinv hodd hxl False.elim hyl False.elim
      hsp hsl hep hel he) fun t hI => ⟨by omega, s, minv, X, _, eb, hI, hw2, by omega,
        VG.Proof.Bignum.coprime_pow2 hodd _, hxl, hL, by omega, he, hout⟩
  simp only [seqs, expBytes]
  refine (two_loop (Φ := VG.Proof.Bignum.X86_64.CBytesInv) (Ψ := fun _ _ => True) (fun a => a.len) (VG.Proof.Bignum.X86_64.crtByte_ct M) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, eb, hI, hw, hw', hR, hXN, hL, hL', he, hout⟩
  exact WP.mono (crtByte_ok M hw hw' hR rfl hL' (by omega) he.rd he.val hout hI)
    fun s' ⟨hz, hI'⟩ => ⟨VG.Proof.Bignum.X86_64.eval_ne_count hi (by rw [hz, hL]), fun _ => ⟨t₀, minv, X, Xc, eb, hI', hw, hw', hR, hXN, hL,
      hL', he, hout⟩, fun _ => trivial⟩

theorem expLoop_ct_P (M : Mont) : VG.Proof.Bignum.X86_64.ExpCT M sDp sPlen := VG.Proof.Bignum.X86_64.crtExpLoop_ct M (by taint_decide)

theorem expLoop_ct_Q (M : Mont) : VG.Proof.Bignum.X86_64.ExpCT M sDq sQlen := VG.Proof.Bignum.X86_64.crtExpLoop_ct M (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow`. -/
section

/-!
# RSA with the CRT on x86-64: `G = 2^E mod n` is constant time

`gPow` computes in `n`'s workspace, all public: the prime's length `w_X`,
hence `K`, `D` and the bits of `D` the loop branches on, are the same in
both runs (`gPow_ct`). Its loads through the prime's base (in a header slot)
are pinned by correctness, the bits of `D` from `gBit_ok`'s invariant.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `n`'s layout. -/
abbrev GPub.L (p : VG.Proof.Bignum.X86_64.GPub) : Lay := ⟨p.B, p.Z, p.w, p.minv⟩

/-- After the top `j` bits of `D` in `gPow`'s loop. -/
def GLoop (p : VG.Proof.Bignum.X86_64.GPub) (j : Nat) (t : State) : Prop :=
  ∃ s₀, GInv s₀ p.B p.Z p.w p.minv p.N (gD p.w p.wx) (gD p.w p.wx).log2 j t ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2
      ^ 30 ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ 1 ≤ p.wx ∧ p.wx ≤ p.w

/-- After the squaring of bit `j`. -/
def GB1 (q : VG.Proof.Bignum.X86_64.GPub × Nat) (t : State) : Prop :=
  (VG.Proof.Bignum.X86_64.Good t q.1.B q.1.Z q.1.w q.1.minv ∧ VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z) ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧ q.2 < (gD q.1.w
      q.1.wx).log2 + 1 ∧ (gD q.1.w q.1.wx).log2 < 62 ∧
    wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w Public.aY) q.1.w < wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w Public.aN) q.1.w ∧
    VG.Proof.Bignum.X86_64.word t.mem q.1.B (8 * sD) = BitVec.ofNat 64 (gD q.1.w q.1.wx) ∧
    VG.Proof.Bignum.X86_64.word t.mem q.1.B (8 * Public.sCnt) = BitVec.ofNat 64 (2 ^ ((gD q.1.w q.1.wx).log2 - q.2))

/-- After the test of bit `j`. -/
def GB2 (q : VG.Proof.Bignum.X86_64.GPub × Nat) (t : State) : Prop :=
  (VG.Proof.Bignum.X86_64.Good t q.1.B q.1.Z q.1.w q.1.minv ∧ VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z) ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧
    wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w Public.aY) q.1.w < wv t.mem q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w Public.aN) q.1.w ∧
    t.zf = some (decide ((gD q.1.w q.1.wx) / 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) % 2 = 0))

theorem exec_seqs_split {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases ih (by simp) e₂ with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

/-- A sequence in two parts leaks as their sequence. -/
theorem RelCT.seqs_split {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (VG.Proof.Bignum.X86_64.exec_seqs_split ha hb e₁) (VG.Proof.Bignum.X86_64.exec_seqs_split ha hb e₂)

theorem pins_rdiB {α : Type} {Φ : α → State → Prop} (B : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = B a) :
    Pins Φ [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_of (fun a _ => B a) fun a s hs r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h a s hs

/-- One bit of `D`: the squaring, the test and the doubling. -/
theorem gBody_ct (M : Mont) : RelCT isa (Two fun (q : VG.Proof.Bignum.X86_64.GPub × Nat) s => q.2 < (gD q.1.w q.1.wx).log2 + 1 ∧ VG.Proof.Bignum.X86_64.GLoop q.1
    q.2 s)
    (seqs (gBody M.mm)) fun _ _ => True := by
  simp only [gBody, seqs]
  -- The squaring.
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.GB1) (two_map (fun q => q.1.L.ws)
    (fun q s ⟨_, _, hI, hZ, _⟩ => ⟨q.1.minv, hI.good, hZ⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · rintro q s ⟨hj, s₀, hI, hZ, hw, hw30, -, -, hwx, hwx'⟩
    obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
    have hL : (gD q.1.w q.1.wx).log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
    have hc2 : 2 ^ ((gD q.1.w q.1.wx).log2 + 1 - q.2) / 2 = 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) := by
      rw [show (gD q.1.w q.1.wx).log2 + 1 - q.2 = ((gD q.1.w q.1.wx).log2 - q.2) + 1 by omega, Nat.pow_succ,
        Nat.mul_div_cancel _ (by decide)]
    refine WP.mono (mmN_ok M (o := Public.aY) (a := Public.aY) (b := Public.aY) hI.good hZ hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv
      hI.ylt) fun t₁ ⟨hg₁, hn₁, _, hlt₁, _, ha₁, _⟩ => ⟨⟨hg₁, hZ⟩, hw, hw30, hj, hL, by rw [hn₁]; exact hlt₁,
        by rw [ha₁.hslot (by decide)]; exact hI.d, by rw [ha₁.hslot (by decide), hI.c, hc2]⟩
  -- The bit, into ZF.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.GB2) [.rdi] (VG.Proof.Bignum.X86_64.pins_rdiB (fun q => q.1.B) fun _ _ h => h.1.1.rdi)
    (by taint_decide) ?_) ?_
  · rintro q t₁ ⟨hg₁, hw, hw30, hj, hL, hlt, hd, hc⟩
    have hZ := hg₁.2
    have hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off q.1.B (8 * i)) 8 := fun i hi =>
      hg₁.1.scr.ld (by have := hdr_lt_slot q.1.w 8 hi; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t₂ =>
        t₂.zf = some (decide ((gD q.1.w q.1.wx) / 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) % 2 = 0)) ∧ t₂.mem = t₁.mem) (by
      xrun [State.ea, hdr, hg₁.1.rdi, hdrOff, hl₁ sD (by decide), hl₁ Public.sCnt (by decide), hd, hc,
        and_pow_beq (gD q.1.w q.1.wx) ((gD q.1.w q.1.wx).log2 - q.2) (by omega)]) rfl)
      fun t₂ ⟨⟨hz, hm⟩, k⟩ => ⟨⟨⟨hg₁.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg₁.1.rdi, hm ▸ hg₁.1.hdr⟩,
        hg₁.2⟩, hw, hw30, by rw [hm]; exact hlt, hz⟩
  -- Doubled if it is set.
  refine RelCT.seq (R := Two fun (q : VG.Proof.Bignum.X86_64.GPub × Nat) t => (VG.Proof.Bignum.X86_64.Good t q.1.B q.1.Z q.1.w q.1.minv ∧ VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z))
    (two_ite (fun q s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2.2.2.2, h₂.2.2.2.2]) ?_ ?_) ?_
  · refine two_post (two_map (fun q => q.1.L) (fun _ _ h => h.1.1)
      (VG.Proof.Bignum.X86_64.double_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide))) fun q t h => ?_
    obtain ⟨⟨hg, hw, hw30, hlt, -⟩, -⟩ := h
    exact WP.mono (double_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hw (by omega) (mo := Public.aN) (acc := Public.aAcc)
      (tmp := Public.aTmp) (o := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hlt) fun t' ⟨_, ha, k⟩ =>
        ⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hg.2⟩
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun _ _ h => h.1.1) hp
  -- The next bit.
  exact two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_rdiB (fun q => q.1.B) fun _ _ h => h.1.rdi) (by taint_decide)

/-- The bits of `D`. -/
theorem gLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < (gD p.w p.wx).log2 + 1 ∧ VG.Proof.Bignum.X86_64.GLoop p 0 s)
    (.loop (seqs (gBody M.mm)) .ne) (Two fun (_ : VG.Proof.Bignum.X86_64.GPub) (_ : State) => True) :=
  two_loop (Φ := VG.Proof.Bignum.X86_64.GLoop) (fun p => (gD p.w p.wx).log2 + 1) (VG.Proof.Bignum.X86_64.gBody_ct M)
    fun p j s hj ⟨s₀, hI, hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩ => by
      obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
      have hL : (gD p.w p.wx).log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
      exact WP.mono (gBit_ok M hZ hw (by omega) (VG.Proof.Bignum.coprime_pow2 hodd _) (by omega) (by omega) hj hI)
        fun s' ⟨hz, hI'⟩ => ⟨VG.Proof.Bignum.X86_64.eval_ne_count hj hz, fun _ => ⟨s₀, hI', hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩,
          fun _ => trivial⟩

/-- After the load of the prime's base. -/
def GA (sl : Nat) (p : VG.Proof.Bignum.X86_64.GPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.GPre sl p s ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.gpr .rax = p.Bx

/-- After the loads of `w_X` and `w`. -/
def GBk (p : VG.Proof.Bignum.X86_64.GPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧
    t.gpr .rcx = BitVec.ofNat 64 0

/-- After `gHead`: `D`. -/
def GHd (sl : Nat) (p : VG.Proof.Bignum.X86_64.GPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.GPre sl p s ∧ t.gpr .rax = BitVec.ofNat 64 (gD p.w p.wx) ∧
    t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .r12] s t

/-- After `D`'s top bit into `sCnt`. -/
def GTop (sl : Nat) (p : VG.Proof.Bignum.X86_64.GPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.GPre sl p s ∧ VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w p.minv ∧
    t.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))).writeW (VG.Proof.Bignum.X86_64.off p.B (8 * Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t

/-- `gHead`, given that the taint analysis checks the load of the prime's
base (`by taint_decide` for a given `sl`). -/
theorem gHead_ct {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.GPre sl)) (seqs (gHead sl)) fun _ _ => True := by
  simp only [gHead, seqs]
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sl))] : List Instr))
    (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.GA sl) [.rdi] (VG.Proof.Bignum.X86_64.pins_rdiB (fun p => p.B) fun _ _ h => h.1.rdi) hT ?_)
      (two_piece (Ψ := VG.Proof.Bignum.X86_64.GBk) [.rdi, .rax] (VG.Proof.Bignum.X86_64.pins_of (fun p r => if r = .rdi then p.B else p.Bx) fun p s h r hr => ?_)
        (by taint_decide) ?_)))
    (two_taint [.rdi, .rax, .r12, .rcx] (VG.Proof.Bignum.X86_64.pins_of (fun p r => if r = .rdi then p.B else if r = .rax then
      BitVec.ofNat 64 p.wx else if r = .r12 then BitVec.ofNat 64 p.w else BitVec.ofNat 64 0) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide))
  · intro p s h
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * i)) 8 := fun i hi =>
      h.1.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := h.2.1; omega)
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.Bx ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, h.1.rdi, hdrOff, hl sl h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1]) rfl)
      fun t ⟨⟨h1, h2⟩, k⟩ => ⟨s, h, h2, k, h1⟩
  · obtain ⟨σ, hσ, -, k, hax⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr (by decide)).trans hσ.1.rdi
    · exact hax
  · rintro p t ⟨s, ⟨hg, hZ, _, _, _, _, _, _, _, _, _, _, hXw, hXr, _⟩, hm, k, hax⟩
    have hdi : t.gpr .rdi = p.B := (k.gpr (by decide)).trans hg.rdi
    have hXr' : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.Bx (8 * sW)) 8 := by rw [k.2.1, k.2.2]; exact hXr
    have hW : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * sW)) 8 := by
      rw [k.2.1, k.2.2]; exact hg.scr.ld (by have := hdr_lt_slot p.w 8 (show sW < 32 by decide); omega)
    have hXw' : VG.Proof.Bignum.X86_64.word t.mem p.Bx (8 * sW) = BitVec.ofNat 64 p.wx := by rw [hm]; exact hXw
    have hw' : VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sW) = BitVec.ofNat 64 p.w := by rw [hm]; exact hg.hdr.hw
    exact WP.mono (WP.keep [.rax, .r12, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 p.wx ∧
        t'.gpr .r12 = BitVec.ofNat 64 p.w ∧ t'.gpr .rcx = BitVec.ofNat 64 0)
      (by xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdi, hax, hdrOff, hXr', hXw', hW, hw']) rfl)
      fun t' ⟨h', k'⟩ => ⟨(k'.gpr (by decide)).trans hdi, h'⟩

/-- `D`'s top bit into `sCnt`. -/
theorem gTop_ct (sl : Nat) : RelCT isa (Two (VG.Proof.Bignum.X86_64.GHd sl)) (.seq topBit (.block [.store (hdr Public.sCnt) .rdx]))
    (Two (VG.Proof.Bignum.X86_64.GTop sl)) := by
  refine two_piece [.rax, .rdi] (VG.Proof.Bignum.X86_64.pins_of (fun p r => if r = .rax then BitVec.ofNat 64 (gD p.w p.wx) else p.B)
    fun p s h r hr => ?_) (by taint_decide) ?_
  · obtain ⟨σ, hσ, hax, -, k⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hax
    · exact (k.gpr (by decide)).trans hσ.1.rdi
  rintro p t₁ ⟨s, h, hax₁, hm₁, k₁⟩
  obtain ⟨hg, hZ, hw, hw30, _, _, _, _, _, _, _, _, _, _, hwx, hwx'⟩ := id h
  obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
  have hs₁ := hg.scr.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hg.rdi
  refine WP.seq (WP.mono (topBit_ok hax₁ hD0 (by omega)) fun t₂ ⟨hdx₂, _, hm₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = p.B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * Public.sCnt + 8 ≤ p.Z by
      have := hdr_lt_slot p.w 8 (show Public.sCnt < 32 by decide); omega), hdx₂]) rfl) fun t₃ ⟨hm₃, k₃⟩ => ?_
  have hm₃' : t₃.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))).writeW (VG.Proof.Bignum.X86_64.off p.B (8 *
      Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) := by rw [hm₃, hm₂, hm₁]
  exact ⟨s, h,
    ⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, by
      rw [hm₃']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    hm₃', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `Y := R`: the loop's start. -/
theorem gStart_ok (M : Mont) {sl : Nat} {p : VG.Proof.Bignum.X86_64.GPub} {t : State} (h : VG.Proof.Bignum.X86_64.GTop sl p t) :
    WP isa (M.mm Public.aY Public.aR2 Public.aOne) t fun t' => 0 < (gD p.w p.wx).log2 + 1 ∧ VG.Proof.Bignum.X86_64.GLoop p 0 t' := by
  obtain ⟨s, ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2', hone, _, _, _, _, hwx, hwx'⟩, hg₃, hm₃', k₃⟩ := h
  have hnw := hg.scr.nowrap
  have hn' : p.B.toNat + VG.Proof.Bignum.X86_64.slot p.w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * p.w)) p.N := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
  have hwv₃ : ∀ j < 8, wv t.mem p.B (VG.Proof.Bignum.X86_64.slot p.w j) p.w = wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w j) p.w := fun j hj => by
    rw [hm₃', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  refine WP.mono (mmN_ok M (N := p.N) (o := Public.aY) (a := Public.aR2) (b := Public.aOne) hg₃ hZ hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ Public.aN (by decide)).trans hn)
    (by rw [hm₃', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₃ Public.aOne (by decide), hone]; exact hN1))
    fun t₄ ⟨hg₄, hn₄, hinv₄, hlt₄, hm₄, ha₄, k₄⟩ => ⟨by omega, s, ?_, hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩
  rw [hwv₃ Public.aR2 (by decide), hwv₃ Public.aOne (by decide), hone, Nat.mul_one] at hm₄
  have hY₄ : wv t₄.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aY) p.w % p.N =
      2 ^ ((gD p.w p.wx) / 2 ^ ((gD p.w p.wx).log2 + 1 - 0)) * 2 ^ (64 * p.w) % p.N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hr2']
  have hfr₄ : Frm p.B (gRanges p.w) s.mem t₄.mem := by
    have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem p.B (BitVec.ofNat 64 (gD p.w p.wx)) (d := 8 * sD) (by unfold sD sFn; omega)
    have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))) p.B
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) (d := 8 * Public.sCnt) (by unfold Public.sCnt sFn; omega)
    rw [← hm₃'] at o2
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_outside o2 (by simp [gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [gRanges]))
  exact ⟨hg₄, hn₄, hinv₄, hlt₄, hY₄,
    by rw [ha₄.hslot (by decide), hm₃', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self],
    by rw [ha₄.hslot (by decide), hm₃', VG.Proof.Bignum.X86_64.word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₄, (k₃.trans k₄).mono (by decide)⟩

/-- `gPow sl`, given that the taint analysis checks the load of the
prime's base. -/
theorem gPow_ct_of {M : Mont} {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sl))]) hc).isSome = true) :
    VG.Proof.Bignum.X86_64.GPowCT M sl := by
  unfold VG.Proof.Bignum.X86_64.GPowCT
  rw [gPow_eq]
  refine RelCT.seqs_split (by simp [gHead]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.GHd sl) (VG.Proof.Bignum.X86_64.gHead_ct hT)
    fun p s h => ?_) ?_)
  · obtain ⟨hg, hZ, hw, hw30, _, _, _, _, _, _, hsl, hX, hXw, hXr, hwx, hwx'⟩ := id h
    exact WP.mono (gHead_ok hg hZ hw hw30 hsl hX hXw hXr hwx hwx') fun t ⟨h1, h2, h3⟩ => ⟨s, h, h1, h2, h3⟩
  refine RelCT.assoc (RelCT.seq (VG.Proof.Bignum.X86_64.gTop_ct sl) (RelCT.seq (two_post (two_map (fun p => p.L.ws)
    (fun p s h => ?_) (M.ct (by unfold MmUse; decide))) fun p s h => VG.Proof.Bignum.X86_64.gStart_ok M h)
    ((VG.Proof.Bignum.X86_64.gLoop_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)))
  obtain ⟨_, ⟨_, hZ, _⟩, hg, _⟩ := h
  exact ⟨p.minv, hg, hZ⟩

theorem gPow_ct_P (M : Mont) : VG.Proof.Bignum.X86_64.GPowCT M sWsP := VG.Proof.Bignum.X86_64.gPow_ct_of (by taint_decide)

theorem gPow_ct_Q (M : Mont) : VG.Proof.Bignum.X86_64.GPowCT M sWsQ := VG.Proof.Bignum.X86_64.gPow_ct_of (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub`. -/
section

/-!
# RSA with the CRT on x86-64: constant time, the steps of `p`'s phase

How a phase is composed: each piece's claim, for a predicate that carries
its hypotheses and what correctness gives after it (`ct_step`), and
`subModArr` (`subModArr_ct`), whose two loops run from bases loaded from the
header: the second block's header loads are checked from `rdi`, which the
first loop keeps (`subModArr_wp`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Composing pieces

`CTMain`'s `RelCT.seqs_append`, which this file cannot import (its names
clash with `CrtCTDefs`'). -/

theorem exec_seqs_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      have e₂' := ih (by simp) e₂
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases e₂' with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

theorem RelCT.seqs_app {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (VG.Proof.Bignum.X86_64.exec_seqs_app ha hb e₁) (VG.Proof.Bignum.X86_64.exec_seqs_app ha hb e₂)

/-- A piece whose claim holds for public data `g a`, then the rest, from
what correctness gives after the piece. -/
theorem ct_step {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hc : RelCT isa (Two P) c fun _ _ => True) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_post (two_map g hP hc) hw) hr

/-- A piece checked by the taint analysis from the registers `rs`, then the rest. -/
theorem ct_taint {α : Type} {Φ Ψ : α → State → Prop} {c rest : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_piece rs hpin h hw) hr

/-- A list of pieces whose claim holds for public data `g a`, then the rest. -/
theorem ct_steps {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : List (Prog isa)}
    (hc0 : c ≠ []) (hr0 : rest ≠ []) (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s)
    (hw : ∀ a s, Φ a s → WP isa (seqs c) s (Ψ a))
    (hc : RelCT isa (Two P) (seqs c) fun _ _ => True) (hr : RelCT isa (Two Ψ) (seqs rest) fun _ _ => True) :
    RelCT isa (Two Φ) (seqs (c ++ rest)) fun _ _ => True :=
  RelCT.seqs_app hc0 hr0 (VG.Proof.Bignum.X86_64.ct_step g hP hw hc hr)

/-- The last piece. -/
theorem ct_last {α β : Type} {Φ : α → State → Prop} {P : β → State → Prop} {c : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hc : RelCT isa (Two P) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  two_map g hP hc

/-! ## `subModArr` -/

/-- `subModArr`'s blocks and loops. -/
def smBlk1 (a b : Nat) : List Instr :=
  [.mov .r8 (.mem (hdr (sArr a))), .mov .r10 (.mem (hdr (sArr b))), .mov .rsi (.mem (hdr (sArr Public.aAcc))),
    .mov .r12 (.mem (hdr sW)), .mov32 .rbp (.imm 0)]

def smLoop1 : Prog isa :=
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp]

def smBlk3 (o : Nat) : List Instr :=
  [.mov .r15 (.reg .rbp), .mov32 .rbp (.imm 0), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .rbx (.mem (hdr (sArr o)))]

def smLoop2 : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp,
    .alu .adc .rax (.mem (ix .r8 .r14)), .store (ix .rbx .r14) .rax, cfToRbp]

theorem subModArr_eq (o a b : Nat) :
    seqs (subModArr o a b) = .seq (.block (VG.Proof.Bignum.X86_64.smBlk1 a b)) (.seq VG.Proof.Bignum.X86_64.smLoop1 (.seq (.block (VG.Proof.Bignum.X86_64.smBlk3 o)) VG.Proof.Bignum.X86_64.smLoop2)) := rfl

/-- Before `subModArr`'s second loop: its bases and `w`. -/
def Sm3 (o : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aN) ∧ s.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o) ∧ s.gpr .r12 = BitVec.ofNat 64 L.w

/-- After `subModArr`'s first loop: the base in `rdi`, and the second block
gives `Sm3`. -/
def Sm2 (o : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .rdi = L.B ∧ WP isa (.block (VG.Proof.Bignum.X86_64.smBlk3 o)) s (VG.Proof.Bignum.X86_64.Sm3 o L)

/-- Before `subModArr`'s first loop: its bases and `w`, and the loop gives `Sm2`. -/
def Sm1 (o a b : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w a) ∧ s.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w b) ∧
    s.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧ s.gpr .r12 = BitVec.ofNat 64 L.w ∧ WP isa VG.Proof.Bignum.X86_64.smLoop1 s (VG.Proof.Bignum.X86_64.Sm2 o L)

/-- `subModArr`'s hypotheses for its timing: the workspace and its size. -/
def SmPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

/-- `subModArr`'s first block and loop, as `subModArr_ok` runs them. -/
theorem subModArr_wp {L : Ws} {s : State} (h : VG.Proof.Bignum.X86_64.SmPre L s) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc) :
    WP isa (.block (VG.Proof.Bignum.X86_64.smBlk1 a b)) s (VG.Proof.Bignum.X86_64.Sm1 o a b L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => (slot_le hj).trans hZ
  have sp : ∀ {j k}, j ≠ k → VG.Proof.Bignum.X86_64.slot L.w j + 8 * (L.w + 2) ≤ VG.Proof.Bignum.X86_64.slot L.w k ∨ VG.Proof.Bignum.X86_64.slot L.w k + 8 * (L.w + 2) ≤ VG.Proof.Bignum.X86_64.slot L.w j :=
    fun h => VG.Proof.Bignum.X86_64.slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have hacc : Public.aAcc < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  refine WP.mono (WP.keep [.r8, .r10, .rsi, .r12, .rbp] (Q := fun t =>
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w a) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w b) ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
      t.mem = s.mem)
    (by xrun [VG.Proof.Bignum.X86_64.smBlk1, State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hg.hdr.harr a ha, hg.hdr.harr b hb, hg.hdr.harr Public.aAcc hacc, hg.hdr.hw]) rfl)
    fun s₁ ⟨⟨h8, h10, hsi, h12, hbp, hm₁⟩, k₁⟩ => ⟨h8, h10, hsi, h12, ?_⟩
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      SubInv s₁ L.B L.Z (VG.Proof.Bignum.X86_64.slot L.w a) (VG.Proof.Bignum.X86_64.slot L.w b) (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := L.w) (by omega) hw'
    (SubInv s₁ L.B L.Z (VG.Proof.Bignum.X86_64.slot L.w a) (VG.Proof.Bignum.X86_64.slot L.w b) (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc)) h0
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) (by have := sl a ha; omega)
      (by have := sl b hb; omega) (by have := sl _ hacc; omega) (by have := sp d3; omega)
      (by have := sp d4; omega) hj hI)) fun s₂ hI => ?_
  have k12 := k₁.trans hI.keep
  have s₂di : s₂.gpr .rdi = L.B := (k12.gpr (by decide)).trans hg.rdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have fh : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₂.mem L.B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem L.B (8 * i) := fun i hi => by
    rw [hI.out.word (Or.inl (by have := hdr_lt_slot L.w Public.aAcc hi; omega)) (by
      have := hdr_lt_slot L.w 8 hi; omega), hm₁]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 L.w := (hI.keep.gpr (by decide)).trans h12
  refine ⟨s₂di, WP.mono (WP.keep [.r15, .rbp, .r10, .r8, .rbx] (Q := fun t =>
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aN) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o))
    (by xrun [VG.Proof.Bignum.X86_64.smBlk3, State.ea, hdr, s₂di, hdrOff, hl₂ (sArr Public.aN) (by decide),
      hl₂ (sArr Public.aAcc) (by decide), hl₂ (sArr o) (by unfold sArr; omega),
      (fh _ (by decide)).trans (hg.hdr.harr Public.aN hmo), (fh _ (by decide)).trans (hg.hdr.harr Public.aAcc hacc),
      (fh _ (by unfold sArr; omega)).trans (hg.hdr.harr o ho)]) rfl)
    fun t ⟨⟨h10, h8, hbx⟩, k⟩ => ⟨h10, h8, hbx, (k.gpr (by decide)).trans h12₂⟩⟩

/-- `subModArr aT aY aXc`, `p`'s difference, is constant time. -/
theorem subModArr_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.SmPre) (seqs (subModArr aT Public.aY aXc)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.subModArr_eq]
  refine VG.Proof.Bignum.X86_64.ct_taint [.rdi] (fun L s₁ s₂ ⟨⟨_, h₁, _⟩, _⟩ ⟨⟨_, h₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide)
    (fun L s h => VG.Proof.Bignum.X86_64.subModArr_wp (o := aT) h (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VG.Proof.Bignum.X86_64.ct_taint [.r8, .r10, .rsi, .r12] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide) (fun L s h => h.2.2.2.2) ?_
  refine VG.Proof.Bignum.X86_64.ct_taint [.rdi] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun L s h => h.2) ?_
  exact two_taint [.r10, .r8, .rbx, .r12] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPMq`. -/
section

/-!
# RSA with the CRT on x86-64: constant time, `m_q G mod n`

`mqSteps` (`mqPart_ok`) is constant time (`mq_ct`) for a predicate (`Mq0`)
that carries, before each piece, its claim's hypotheses and what
correctness gives after it; `mq_chain` proves it from `mqPart_ok`'s
hypotheses, as `mqPart_ok` runs the pieces.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `mqSteps`: the modulus' workspace and `q`'s. -/
structure MqPub where
  B : Addr
  Z : Nat
  w : Nat
  oq : Nat
  wq : Nat

/-- The modulus' workspace. -/
abbrev MqPub.ws (p : VG.Proof.Bignum.X86_64.MqPub) : Ws := ⟨p.B, p.Z, p.w⟩

/-- `mqSteps`' block loading `q`'s `Y`: `q`'s base, then from it. -/
def mqBlk1 : List Instr := [.mov .rax (.mem (hdr sWsQ))]

def mqBlk2 : List Instr :=
  [.mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr Public.aY))), .mov .r12 (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sW)), .mov .rbx (.mem (hdr (sArr Public.aX)))]

theorem mqSteps_eq (mul : Nat → Nat → Nat → Prog isa) :
    seqs (mqSteps mul) = .seq (zeroArr Public.aX) (.seq (.block (VG.Proof.Bignum.X86_64.mqBlk1 ++ VG.Proof.Bignum.X86_64.mqBlk2)) (.seq copyWords
      (.seq (mul Public.aX Public.aX Public.aR2) (mul Public.aX Public.aX Public.aY)))) := rfl

/-- Before `X := X R² R⁻¹`. -/
def Mq3 (M : Mont) (p : VG.Proof.Bignum.X86_64.MqPub) (s : State) : Prop :=
  GoodW p.ws s ∧ WP isa (M.mm Public.aX Public.aX Public.aR2) s (GoodW p.ws)

/-- Before the copy of `m_q`. -/
def Mq2 (M : Mont) (p : VG.Proof.Bignum.X86_64.MqPub) (s : State) : Prop :=
  s.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot p.wq Public.aY) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wq ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aX) ∧ WP isa copyWords s (VG.Proof.Bignum.X86_64.Mq3 M p)

/-- Before the loads from `q`'s workspace. -/
def Mq1b (M : Mont) (p : VG.Proof.Bignum.X86_64.MqPub) (s : State) : Prop :=
  s.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ s.gpr .rdi = p.B ∧ WP isa (.block VG.Proof.Bignum.X86_64.mqBlk2) s (VG.Proof.Bignum.X86_64.Mq2 M p)

/-- Before the load of `q`'s base. -/
def Mq1 (M : Mont) (p : VG.Proof.Bignum.X86_64.MqPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block VG.Proof.Bignum.X86_64.mqBlk1) s (VG.Proof.Bignum.X86_64.Mq1b M p)

/-- Before `mqSteps`. -/
def Mq0 (M : Mont) (p : VG.Proof.Bignum.X86_64.MqPub) (s : State) : Prop :=
  GoodW p.ws s ∧ WP isa (zeroArr Public.aX) s (VG.Proof.Bignum.X86_64.Mq1 M p)

/-- `mqSteps` is constant time. -/
theorem mq_ct (M : Mont) : RelCT isa (Two (VG.Proof.Bignum.X86_64.Mq0 M)) (seqs (mqSteps M.mm)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.mqSteps_eq]
  refine VG.Proof.Bignum.X86_64.ct_step MqPub.ws (fun _ _ h => h.1) (fun _ _ h => h.2) (VG.Proof.Bignum.X86_64.zeroArr_ct (by decide) (by taint_decide)) ?_
  have b1 : RelCT isa (Two (VG.Proof.Bignum.X86_64.Mq1 M)) (.block VG.Proof.Bignum.X86_64.mqBlk1) (Two (VG.Proof.Bignum.X86_64.Mq1b M)) :=
    two_piece [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) fun _ _ h => h.2
  have b2 : RelCT isa (Two (VG.Proof.Bignum.X86_64.Mq1b M)) (.block VG.Proof.Bignum.X86_64.mqBlk2) (Two (VG.Proof.Bignum.X86_64.Mq2 M)) :=
    two_piece [.rax, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  refine RelCT.seq (RelCT.block_append (RelCT.seq b1 b2)) ?_
  refine VG.Proof.Bignum.X86_64.ct_taint [.rsi, .r12, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) (fun _ _ h => h.2.2.2) ?_
  exact VG.Proof.Bignum.X86_64.ct_step MqPub.ws (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (VG.Proof.Bignum.X86_64.ct_last MqPub.ws (fun _ _ h => h) (M.ct (by unfold MmUse; decide)))

/-- `mqPart_ok`'s hypotheses give `Mq0`. -/
theorem mq_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mq : BitVec 64} {N oq wq : Nat}
    (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N)
    (hq : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq) (hws : WsAt s.mem B oq wq mq) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ oq)
    (hhi : oq + VG.Proof.Bignum.X86_64.slot wq 8 + tabBytes wq ≤ Z) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) : VG.Proof.Bignum.X86_64.Mq0 M ⟨B, Z, w, oq, wq⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have hX0 := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have hY8 := slot_le (w := wq) (show Public.aY < 8 by decide)
  have hq8 : 8 * 32 ≤ VG.Proof.Bignum.X86_64.slot wq 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hqo : oq < 2 ^ 64 := by omega
  -- `X := 0`.
  refine ⟨⟨minv, hg, show VG.Proof.Bignum.X86_64.slot w 8 ≤ Z by omega⟩, WP.mono (zeroArr_ok hg (by omega) (by omega) (by omega)
    (show Public.aX < 8 by decide)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_⟩
  have hb₁ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega)) (by omega)
  have hq₁ : ∀ d, VG.Proof.Bignum.X86_64.slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₁.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega)) hd'
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hsq : VG.Proof.Bignum.X86_64.Scr s₁ (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wq 8) := hs₁.sub (by omega) (by omega)
  have hqw : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hq₁ _ (by omega) (by omega)
  refine ⟨hdi₁, WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off B oq ∧ t.mem = s₁.mem)
    (by xrun [VG.Proof.Bignum.X86_64.mqBlk1, State.ea, hdr, hdi₁, hdrOff, hs₁.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega),
      hb₁ sWsQ (by decide), hq]) rfl) fun s₁' ⟨⟨hax, hm₁'⟩, k₁'⟩ =>
    ⟨hax, (k₁'.gpr (by decide)).trans hdi₁, ?_⟩⟩
  have hs₁' := hs₁.congr k₁'.2.2
  have hsq' : VG.Proof.Bignum.X86_64.Scr s₁' (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wq 8) := hsq.congr k₁'.2.2
  have hdi₁' : s₁'.gpr .rdi = B := (k₁'.gpr (by decide)).trans hdi₁
  have hb₁' : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁'.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by rw [hm₁']; exact hb₁ i hi
  have hqw' : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁'.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * i) := fun i hi => by
    rw [hm₁']; exact hqw i hi
  refine WP.mono (WP.keep [.rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wq Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aX) ∧ t.mem = s₁.mem)
    (by xrun [VG.Proof.Bignum.X86_64.mqBlk2, State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdi₁', hax, hdrOff, hm₁', hsq'.ld (d := 8 * sArr Public.aY) (by unfold sArr Public.aY; omega),
      hqw (sArr Public.aY) (by decide), hws.hdr.harr Public.aY (by decide),
      hsq'.ld (d := 8 * sW) (by unfold sW; omega), hqw sW (by decide), hws.hdr.hw,
      hs₁'.ld (d := 8 * sArr Public.aX) (by unfold sArr Public.aX; omega), hb₁ (sArr Public.aX) (by decide),
      hg.hdr.harr Public.aX (by decide)]) rfl) fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ =>
    ⟨hsi₂, h12₂, hbx₂, ?_⟩
  have k₂ := k₁'.trans k₂
  have hs₂ := hs₁.congr k₂.2.2
  have hsq₂ := hsq.congr k₂.2.2
  -- `X := m_q`.
  refine WP.mono (copyWords_ok (S := VG.Proof.Bignum.X86_64.off B oq) (eS := VG.Proof.Bignum.X86_64.slot wq Public.aY) (D := B) (eD := VG.Proof.Bignum.X86_64.slot w Public.aX)
    (w := wq) hsi₂ hbx₂ h12₂ hwq (by omega) (by omega) (fun j hj => hsq₂.ld (by omega))
    (fun j hj => hs₂.st (by omega)) (fun j hj b hb => Or.inr (by
      rw [off_off, VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega))) fun s₃ ⟨_, _, ho₃, k₃⟩ => ?_
  have hn₃ : ∀ j < 8, j ≠ Public.aX → wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w j) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun j hj hjx => by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hjx
    have := slot_le (w := w) hj
    rw [ho₃.wv (by omega) (by omega), hm₂, ho₁.wv (by omega) (by omega)]
  have hg₃ : VG.Proof.Bignum.X86_64.Good s₃ B Z w minv := ⟨hs.congr ((k₁.trans k₂).trans k₃).2.2,
    ((k₂.trans k₃).gpr (by decide)).trans hdi₁, by
      have : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
        rw [ho₃.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega)) (by omega), hm₂, hb₁ i hi]
      exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
        fun j hj => (this _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩
  have hw0 : VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    rw [ho₃.word (by omega) (by omega), hm₂, ho₁.word (by omega) (by omega)]
  -- `X := m_q R`.
  refine ⟨⟨minv, hg₃, show VG.Proof.Bignum.X86_64.slot w 8 ≤ Z by omega⟩, WP.mono (mmN_ok M hg₃ (by omega) (by omega) (by omega) (o := Public.aX)
    (a := Public.aX) (b := Public.aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ((hn₃ _ (by decide) (by decide)).trans hN.n) (by rw [hw0]; exact hN.inv)
    (by rw [hn₃ _ (by decide) (by decide)]; exact hN.r2lt)) fun s₄ h₄ => ⟨minv, h₄.1, show VG.Proof.Bignum.X86_64.slot w 8 ≤ Z by omega⟩⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ`. -/
section

/-!
# RSA with the CRT on x86-64: constant time of `q`'s phase

The start of a prime's phase (`unit_ct`, `unitPhase_ok`), its power
(`pow_ct`, `powPhase_ok`) and `q`'s phase (`qPhase_ct`, `qPhase_ok`), from
the claims about their parts (`GPowCT`, `RedcCT`, `ExpCT`). Between the
parts, each state predicate fixes the public data and keeps of the secrets
only what the next part's claim and the correctness of the parts after it
need.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Helpers -/

namespace CrtCTQ

/-- `Φ a` fixes `rdi`. -/
theorem pinsRdi {α : Type} {Φ : α → State → Prop} (f : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = f a) :
    Pins Φ [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_of (fun a _ => f a) fun a s hs r hr => by rw [List.mem_singleton.mp hr]; exact h a s hs

theorem gRanges_le (w : Nat) : ∀ r ∈ gRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem gxRanges_le {w o wx : Nat} (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o) :
    ∀ r ∈ gRanges w ++ [xRange o wx], r.1 + r.2 ≤ o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx := by
  have hX8 : 8 * 17 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · have := VG.Proof.Bignum.X86_64.CrtCTQ.gRanges_le w r hr; omega
  · rw [List.mem_singleton.mp hr]; simp only [xRange]; omega

/-- The modulus' header words but `sD`'s and `sCnt`'s, past a change within
`gRanges` and a prime's workspace. -/
theorem Frm.gx_hdr {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (gRanges w ++ [xRange o wx]) m m')
    (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD)
    (h2 : i ≠ Public.sCnt) : VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := by
  have := hdr_lt_slot w Public.aAcc hi
  have := hdr_lt_slot w Public.aTmp hi
  have := hdr_lt_slot w Public.aY hi
  have := hdr_lt_slot w 8 hi
  refine hf.word_eq (fun r hr => ?_) (by omega)
  simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
    unfold Crt.sD sFn at h1 ⊢; omega
  · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
    unfold Public.sCnt sFn at h2 ⊢; omega
  · exact Or.inl (by omega)

/-- A prime's workspace header past a change within `gRanges`. -/
theorem WsAt.of_g {m m' : Mem} {B : Addr} {w o wx : Nat} {mx : BitVec 64} (h : WsAt m B o wx mx)
    (hf : Frm B (gRanges w) m m') (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o) (hoL : B.toNat + o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64) :
    WsAt m' B o wx mx :=
  h.of_words fun i hi => by
    have : 8 * 32 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
    rw [word_off, word_off]
    exact hf.word_eq (fun r hr => Or.inr (by have := VG.Proof.Bignum.X86_64.CrtCTQ.gRanges_le w r hr; omega)) (by omega)

/-! ## The start of a prime's phase -/

/-- `gPow`'s public data. -/
def gp (p : VG.Proof.Bignum.X86_64.UPub) : VG.Proof.Bignum.X86_64.GPub := ⟨p.B, p.Z, p.w, p.minv, p.N, VG.Proof.Bignum.X86_64.off p.B p.o, p.wx⟩

/-- The prime's workspace. -/
def xp (p : VG.Proof.Bignum.X86_64.UPub) : VG.Proof.Bignum.X86_64.XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

theorem gPre {sl : Nat} {p : VG.Proof.Bignum.X86_64.UPub} {s : State} (h : VG.Proof.Bignum.X86_64.UPre sl p s) : VG.Proof.Bignum.X86_64.GPre sl (VG.Proof.Bignum.X86_64.CrtCTQ.gp p) s := by
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, -, -, hslv, hws, hN, hodd, hN1, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  dsimp only [VG.Proof.Bignum.X86_64.GPre, VG.Proof.Bignum.X86_64.CrtCTQ.gp]
  exact ⟨hg, by omega, by omega, by omega, hN.n, hN.inv, hodd, hN1, hN.r2, hN.one, hsl, hslv, hws.hdr.hw,
    (hs.sub (o := p.o) (n := VG.Proof.Bignum.X86_64.slot p.wx 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega), by omega, hwx⟩

/-- After `gPow`. -/
def U1 (sl : Nat) (p : VG.Proof.Bignum.X86_64.UPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.o ∧
    p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sl) = VG.Proof.Bignum.X86_64.off p.B p.o ∧
    WsAt t.mem p.B p.o p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X

theorem gPow_u1 (M : Mont) {sl : Nat} {p : VG.Proof.Bignum.X86_64.UPub} {s : State} (h : VG.Proof.Bignum.X86_64.UPre sl p s) :
    WP isa (seqs (Crt.gPow M.mm sl)) s (VG.Proof.Bignum.X86_64.CrtCTQ.U1 sl p) := by
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, hsl1, hsl2, hslv, hws, hN, hodd, hN1, hX, hX1, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hoL : p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (gPow_ok M hg (by omega) (by omega) (by omega) hN.n hN.inv hodd hN1 hN.r2 hN.one hsl hslv
    hws.hdr.hw ((hs.sub (o := p.o) (n := VG.Proof.Bignum.X86_64.slot p.wx 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega))
    (by omega) hwx) fun s₁ ⟨hg₁, _, _, f₁, _⟩ => ?_
  have f₁' : Frm p.B (gRanges p.w) s.mem s₁.mem := f₁
  have fx : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem s₁.mem :=
    Frm.mono f₁' fun r hr => List.mem_append_left _ hr
  exact ⟨mx, X, hg₁, hw28, hlo, hhi, hwx2, hwx, hsl, by rw [Frm.gx_hdr fx hlo hsl hsl1 hsl2]; exact hslv,
    WsAt.of_g hws f₁' hlo (by omega), hX.of_below f₁' (fun r hr => (VG.Proof.Bignum.X86_64.CrtCTQ.gRanges_le _ r hr).trans hlo) hoL, hX1⟩

theorem blk_rpre {sl : Nat} {p : VG.Proof.Bignum.X86_64.UPub} {s : State} (h : VG.Proof.Bignum.X86_64.CrtCTQ.U1 sl p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (VG.Proof.Bignum.X86_64.RPre Public.aY (VG.Proof.Bignum.X86_64.CrtCTQ.xp p)) := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
      (by rw [hm]; exact hws) hdi hlo hhi, ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv,
      by rw [hm]; exact hX.one⟩, hwx2, hwx, (by omega : p.w < 2 ^ 30), hX1, by decide⟩

/-- A prime's workspace, its base in `rdi`, and its size. -/
def XG (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  ∃ minv : BitVec 64, VG.Proof.Bignum.X86_64.Good t (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx 8) p.wx minv ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- `Y := X_c` in a prime's workspace, and back to the modulus'. -/
theorem copyLeave_ct :
    RelCT isa (Two VG.Proof.Bignum.X86_64.CrtCTQ.XG) (seqs (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa))))
      fun _ _ => True := by
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o)
    (two_map (fun p : VG.Proof.Bignum.X86_64.XPub => (⟨VG.Proof.Bignum.X86_64.off p.B p.o, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩ : Ws))
      (fun _ _ ⟨minv, hg, _⟩ => ⟨minv, hg, Nat.le_refl _⟩)
      (VG.Proof.Bignum.X86_64.copyArr_ct (by decide) (by decide) (by taint_decide)))
    fun p s ⟨_, hg, hwx2, hwx⟩ => WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) (by omega)
      (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide))
      fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hg.rdi) ?_)
  exact two_taint [.rdi] (VG.Proof.Bignum.X86_64.CrtCTQ.pinsRdi (fun p : VG.Proof.Bignum.X86_64.XPub => VG.Proof.Bignum.X86_64.off p.B p.o) fun _ _ h => h) (by taint_decide)

/-- `redc`, `Y := X_c` and back to the modulus'. -/
theorem redcCopy_ct (M : Mont) (hR : VG.Proof.Bignum.X86_64.RedcCT M Public.aY) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RPre Public.aY))
      (seqs (redc M.mm Public.aY ++ (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))))
      fun _ _ => True :=
  RelCT.seqs_append (by simp [redc]) (by simp [copyArr]) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.CrtCTQ.XG) hR
    fun _ _ ⟨minv, _, hc, hX, hwx2, hwx, hw30, hX1, hj⟩ =>
      WP.mono (redc_ok M hc hX hwx2 hwx hw30 hX1 hj) fun _ ⟨hc', _⟩ => ⟨minv, hc'.good, hwx2, by omega⟩)
    VG.Proof.Bignum.X86_64.CrtCTQ.copyLeave_ct)

end CrtCTQ

open CrtCTQ in
/-- The start of a prime's phase is constant time. -/
theorem unit_ct (M : Mont) {sl : Nat} (hG : VG.Proof.Bignum.X86_64.GPowCT M sl) (hR : VG.Proof.Bignum.X86_64.RedcCT M Public.aY)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    VG.Proof.Bignum.X86_64.UnitCT M sl := by
  unfold VG.Proof.Bignum.X86_64.UnitCT
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.CrtCTQ.U1 sl)
    (two_map VG.Proof.Bignum.X86_64.CrtCTQ.gp (fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.gPre h) hG) fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.gPow_u1 M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece
    (Ψ := fun p => VG.Proof.Bignum.X86_64.RPre Public.aY (VG.Proof.Bignum.X86_64.CrtCTQ.xp p)) [.rdi]
    (VG.Proof.Bignum.X86_64.CrtCTQ.pinsRdi (fun p : VG.Proof.Bignum.X86_64.UPub => p.B) fun _ _ ⟨_, _, hg, _⟩ => hg.rdi) hT fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.blk_rpre h) ?_)
  exact two_map VG.Proof.Bignum.X86_64.CrtCTQ.xp (fun _ _ h => h) (VG.Proof.Bignum.X86_64.CrtCTQ.redcCopy_ct M hR)

/-! ## The power in a prime's phase -/

namespace CrtCTQ

/-- After entering the prime's workspace. -/
def P1 (sd slen : Nat) (p : VG.Proof.Bignum.X86_64.BPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat) (eb : List Byte), SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx mx ∧
    XVals t p.x.B p.x.o p.x.wx mx X ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 28 ∧ 1 < X ∧ X % 2 = 1 ∧
    wv t.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx < X ∧ sd < 32 ∧ slen < 32 ∧
    VG.Proof.Bignum.X86_64.word t.mem p.x.B (8 * sd) = p.ptr ∧ VG.Proof.Bignum.X86_64.word t.mem p.x.B (8 * slen) = BitVec.ofNat 64 eb.length ∧
    eb.length = p.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧ Src t p.x.B p.x.Z p.ptr eb

theorem blk_p1 {sl sd slen : Nat} {p : VG.Proof.Bignum.X86_64.BPub} {s : State} (h : VG.Proof.Bignum.X86_64.PwPre sl sd slen p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (VG.Proof.Bignum.X86_64.CrtCTQ.P1 sd slen p) := by
  obtain ⟨_, mx, _, X, _, eb, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, hXodd, -, hyl, -, hsd, hsln,
    hep, hel, hlen, hL1, hL2, he⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.x.B p.x.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, eb, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
      (by rw [hm]; exact hws) hdi hlo hhi, ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv,
      by rw [hm]; exact hX.one⟩, hwx2, hwx, hw28, hX1, hXodd, by rw [hm]; exact hyl, hsd, hsln,
      by rw [hm]; exact hep, by rw [hm]; exact hel, hlen, hL1, hL2,
      he.congrK (by rw [hm]; exact InScr.refl _ _ _) k⟩

theorem redc_ePre (M : Mont) {sd slen : Nat} {p : VG.Proof.Bignum.X86_64.BPub} {s : State} (h : VG.Proof.Bignum.X86_64.CrtCTQ.P1 sd slen p s) :
    WP isa (seqs (redc M.mm Public.aY)) s (VG.Proof.Bignum.X86_64.EPre sd slen p) := by
  obtain ⟨mx, X, eb, hc, hX, hwx2, hwx, hw28, hX1, hXodd, hyl, hsd, hsln, hep, hel, hlen, hL1, hL2, he⟩ := h
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hhi := hc.hi
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.x.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : p.x.o < 2 ^ 64 := by omega
  have hoL : p.x.o + VG.Proof.Bignum.X86_64.slot p.x.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (redc_ok M hc hX hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide))
    fun t ⟨hc₂, hX₂, hlt₂, _, f₂, k₂⟩ => ?_
  have fx₂ : Frm p.x.B [xRange p.x.o p.x.wx] s.mem t.mem :=
    f₂.to_x (redcRanges_ok _) hoL (List.mem_singleton_self _)
  have hY₂ : wv t.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx =
      wv s.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx := by
    have rY := redcRanges_arr p.x.wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := p.x.wx) (show Public.aY < 8 by decide)
    have := hc.good.scr.nowrap
    exact f₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega)
  have hR : Nat.Coprime (2 ^ (64 * p.x.wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  obtain ⟨x, hx⟩ := VG.Proof.Bignum.exists_mont hR (by omega)
    (wv t.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx aXc) p.x.wx)
  obtain ⟨y, hy⟩ := VG.Proof.Bignum.exists_mont hR (by omega)
    (wv t.mem (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx Public.aY) p.x.wx)
  exact ⟨mx, X, x, y, eb, hc₂, hwx2, hwx, by omega, hX₂.n, hX₂.inv, hXodd, hlt₂, hx,
    by rw [hY₂]; exact hyl, hy,
    hsd, hsln, by rw [fx₂.x_below (by omega) ho64]; exact hep, by rw [fx₂.x_below (by omega) ho64]; exact hel,
    hlen, hL1, hL2, he.congrK (InScr.of_frm fx₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) k₂⟩

end CrtCTQ

open CrtCTQ in
/-- The power in a prime's phase is constant time. -/
theorem pow_ct (M : Mont) {sl sd slen : Nat} (hR : VG.Proof.Bignum.X86_64.RedcCT M Public.aY) (hE : VG.Proof.Bignum.X86_64.ExpCT M sd slen)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    VG.Proof.Bignum.X86_64.PowCT M sl sd slen := by
  unfold VG.Proof.Bignum.X86_64.PowCT
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.CrtCTQ.P1 sd slen) [.rdi]
    (VG.Proof.Bignum.X86_64.CrtCTQ.pinsRdi (fun p : VG.Proof.Bignum.X86_64.BPub => p.x.B) fun _ _ ⟨_, _, _, _, _, _, hg, _⟩ => hg.rdi) hT
    fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.blk_p1 h) ?_)
  exact RelCT.seqs_append (by simp [redc]) (by simp [Crt.expLoop]) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.EPre sd slen)
    (two_map BPub.x (fun _ _ ⟨mx, X, _, hc, hX, hwx2, hwx, hw28, hX1, _⟩ =>
      ⟨mx, X, hc, hX, hwx2, hwx, by omega, hX1, by decide⟩) hR) fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.redc_ePre M h) hE)

/-! ## `q`'s phase -/

namespace CrtCTQ

/-- The start of `q`'s phase's public data. -/
def up (p : VG.Proof.Bignum.X86_64.PhasePub) : VG.Proof.Bignum.X86_64.UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.o, p.wx⟩

/-- The power's public data. -/
def sp (p : VG.Proof.Bignum.X86_64.PhasePub) : VG.Proof.Bignum.X86_64.BPub := ⟨⟨p.B, p.Z, p.o, p.w, p.wx⟩, p.ep, p.len⟩

theorem uPre {p : VG.Proof.Bignum.X86_64.PhasePub} {s : State} (h : VG.Proof.Bignum.X86_64.QPre p s) : VG.Proof.Bignum.X86_64.UPre sWsQ (VG.Proof.Bignum.X86_64.CrtCTQ.up p) s := by
  obtain ⟨mx, X, _, _, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -, hX, hX1, hXodd, -⟩ := h
  exact ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, by decide, by decide, by decide, hslv, hws, hN, hodd, hN1,
    hX, hX1, hXodd⟩

/-- After the start of `q`'s phase. -/
def Q1 (p : VG.Proof.Bignum.X86_64.PhasePub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat) (eb : List Byte), VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.o ∧ p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.o ∧ WsAt t.mem p.B p.o p.wx mx ∧ NVals t p.B p.w p.minv p.N ∧
    wv t.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aY) p.w < p.N ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx < X ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sDq) = p.ep ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src t p.B p.Z p.ep eb

theorem unit_q1 (M : Mont) {p : VG.Proof.Bignum.X86_64.PhasePub} {s : State} (h : VG.Proof.Bignum.X86_64.QPre p s) :
    WP isa (seqs (unitSteps M.mm sWsQ)) s (VG.Proof.Bignum.X86_64.CrtCTQ.Q1 p) := by
  obtain ⟨mx, X, _, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -, hX, hX1, hXodd, hep,
    hel, hlen, hL1, hL2, he⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hz : p.B.toNat + VG.Proof.Bignum.X86_64.slot p.w 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (unitPhase_ok M hg hw hw28 hlo hhi hwx2 hwx (by decide) (by decide) (by decide) hslv hws hN
    hodd hN1 hX hX1 hXodd) fun t ⟨hg₁, hws₁, hX₁, hlt₁, _, hlq₁, _, _, f₁, k₁⟩ => ?_
  have hX8 : 8 * 17 ≤ VG.Proof.Bignum.X86_64.slot p.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact ⟨mx, X, eb, hg₁, hw, hw28, hlo, hhi, hwx2, hwx,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hslv, hws₁,
    hN.of_frm f₁ hlo hz (by omega), hlt₁, hX₁, hX1, hXodd, hlq₁,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hep,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hel, hlen, hL1, hL2,
    he.congrK (InScr.of_frm f₁ fun r hr => (VG.Proof.Bignum.X86_64.CrtCTQ.gxRanges_le hlo r hr).trans hhi) k₁⟩

theorem mm_pwPre (M : Mont) {p : VG.Proof.Bignum.X86_64.PhasePub} {s : State} (h : VG.Proof.Bignum.X86_64.CrtCTQ.Q1 p s) :
    WP isa (M.mm Public.aY Public.aXm Public.aY) s (VG.Proof.Bignum.X86_64.PwPre sWsQ sDq sQlen (VG.Proof.Bignum.X86_64.CrtCTQ.sp p)) := by
  obtain ⟨mx, X, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hlt, hX, hX1, hXodd, hyl, hep, hel, hlen,
    hL1, hL2, he⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hoL : p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (mmY_ok M hg (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
    (by decide) hN hlt) fun t ⟨hg₂, _, _, f₂, k₂⟩ => ?_
  have f₂' : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem t.mem :=
    Frm.mono f₂ fun r hr => List.mem_append_left _ hr
  have hY₂ : wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx =
      wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx := by
    have := slot_le (w := p.wx) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]
    exact f₂.wv_eq (fun r hr => Or.inr (by have := VG.Proof.Bignum.X86_64.CrtCTQ.gRanges_le p.w r hr; omega)) (by omega)
  -- `N := 1` makes the facts about the modulus trivial: the power's time does not depend on them.
  dsimp only [VG.Proof.Bignum.X86_64.PwPre, VG.Proof.Bignum.X86_64.CrtCTQ.sp]
  refine ⟨p.minv, mx, 1, X, 0, eb, hg₂, hw28, hlo, hhi, hwx2, hwx, by decide,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hslv, WsAt.of_g hws f₂ hlo (by omega),
    hX.of_below f₂ (fun r hr => (VG.Proof.Bignum.X86_64.CrtCTQ.gRanges_le _ r hr).trans hlo) hoL, hX1, hXodd, by simp only [Nat.mod_one],
    by rw [hY₂]; exact hyl, fun hd => absurd (Nat.le_of_dvd Nat.one_pos hd) (by omega), by decide, by decide,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hep,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hel, hlen, hL1, hL2,
    he.congrK (InScr.of_frm f₂' fun r hr => (VG.Proof.Bignum.X86_64.CrtCTQ.gxRanges_le hlo r hr).trans hhi) k₂⟩

/-- After the power: in the prime's workspace. -/
def Q3 (p : VG.Proof.Bignum.X86_64.PhasePub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 28

theorem pow_q3 (M : Mont) {p : VG.Proof.Bignum.X86_64.PhasePub} {s : State} (h : VG.Proof.Bignum.X86_64.PwPre sWsQ sDq sQlen (VG.Proof.Bignum.X86_64.CrtCTQ.sp p) s) :
    WP isa (seqs (powSteps M.mm sWsQ sDq sQlen)) s (VG.Proof.Bignum.X86_64.CrtCTQ.Q3 p) := by
  obtain ⟨_, mx, _, X, _, eb, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, hXodd, hnY, hyl, hyc, hsd,
    hsln, hep, hel, _, hL1, hL2, he⟩ := h
  exact WP.mono (powPhase_ok M hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1 hXodd hnY hyl hyc hsd hsln hep hel
    hL1 hL2 he) fun _ ⟨hc, hX', _⟩ => ⟨mx, X, hc, hX', hX1, hwx2, (by omega : (sp p).x.wx < 2 ^ 28)⟩

/-- Back to `Y`'s value, and to the modulus' workspace. -/
theorem mmLeave_ct (M : Mont) :
    RelCT isa (Two VG.Proof.Bignum.X86_64.CrtCTQ.Q3) (seqs [M.mm Public.aY Public.aY Public.aOne, .block [leave]]) fun _ _ => True := by
  show RelCT isa _ (.seq _ _) _
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o)
    (two_map (fun p : VG.Proof.Bignum.X86_64.PhasePub => (⟨VG.Proof.Bignum.X86_64.off p.B p.o, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩ : Ws))
      (fun _ _ ⟨mx, _, hc, _⟩ => ⟨mx, hc.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide)))
    fun _ _ ⟨_, _, hc, hX, hX1, hwx2, hwx⟩ => WP.mono (M.mm_ok hc.good (Nat.le_refl _) hwx2 (by omega)
      (o := Public.aY) (a := Public.aY) (b := Public.aOne) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hX.inv (by rw [hX.one, hX.n]; exact hX1))
      fun _ h => h.1.rdi) ?_
  exact two_taint [.rdi] (VG.Proof.Bignum.X86_64.CrtCTQ.pinsRdi (fun p : VG.Proof.Bignum.X86_64.PhasePub => VG.Proof.Bignum.X86_64.off p.B p.o) fun _ _ h => h) (by taint_decide)

end CrtCTQ

open CrtCTQ in
/-- `q`'s phase is constant time. -/
theorem qPhase_ct (M : Mont) (hU : VG.Proof.Bignum.X86_64.UnitCT M sWsQ) (hP : VG.Proof.Bignum.X86_64.PowCT M sWsQ sDq sQlen) : VG.Proof.Bignum.X86_64.QPhaseCT M := by
  unfold VG.Proof.Bignum.X86_64.QPhaseCT
  rw [qPhase_eq]
  refine RelCT.seqs_append (by simp [unitSteps, Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.CrtCTQ.Q1)
    (two_map VG.Proof.Bignum.X86_64.CrtCTQ.up (fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.uPre h) hU) fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.unit_q1 M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [powSteps]) (RelCT.seq (two_post
    (Ψ := fun p => VG.Proof.Bignum.X86_64.PwPre sWsQ sDq sQlen (VG.Proof.Bignum.X86_64.CrtCTQ.sp p))
    (two_map (fun p : VG.Proof.Bignum.X86_64.PhasePub => (⟨p.B, p.Z, p.w⟩ : Ws))
      (fun _ _ ⟨_, _, _, hg, _, _, hlo, hhi, _⟩ =>
        ⟨_, hg, by dsimp only; omega⟩)
      (M.ct (by unfold MmUse; decide))) fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.mm_pwPre M h) ?_)
  exact RelCT.seqs_append (by simp [powSteps]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.CrtCTQ.Q3)
    (two_map VG.Proof.Bignum.X86_64.CrtCTQ.sp (fun _ _ h => h) hP) fun _ _ h => VG.Proof.Bignum.X86_64.CrtCTQ.pow_q3 M h) (VG.Proof.Bignum.X86_64.CrtCTQ.mmLeave_ct M))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc`. -/
section

/-!
# RSA with the CRT on x86-64: `redc` is constant time

`redc j` reduces `n`'s array `j` in chunks of `w_X` words: the number of
chunks `K = ⌈w / w_X⌉`, the words left (`sRem`) and whether the last chunk is
short depend only on `w`, `w_X` and the iteration, which both runs share
(`RInv`), and its multiplications are constant time for any modulus (`M.ct`).
Its loads from the header are pinned by correctness (`redcLoad_ok`,
`redcAcc_ok` and their steps), and `addMod`'s reload of its output's base by
`addStep_ok`'s invariant (`addMod_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem SubCtx.of_keep {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List Reg}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem) (k : VG.Proof.MlKem.X86_64.Keep rs s t) (hr : Reg.rdi ∉ rs) :
    SubCtx t B Z o w wx minv :=
  h.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k.2.2 (k.gpr hr)

theorem lt_of_cf {t : State} {a b : Nat} (hcf : t.cf = some (decide (a < b))) (h : isa.eval .b t = some true) :
    a < b := by
  simp only [VG.X86_64.eval, hcf, Option.some.injEq, decide_eq_true_eq] at h; exact h

theorem ge_of_cf {t : State} {a b : Nat} (hcf : t.cf = some (decide (a < b))) (h : isa.eval .b t = some false) :
    b ≤ a := by
  simp only [VG.X86_64.eval, hcf, Option.some.injEq, decide_eq_false_iff_not] at h; omega

/-! ## `addMod aXc aXc aT` -/

/-- `addMod`'s loads. -/
def amB1 : List Instr :=
  [.mov .rbx (.mem (hdr (sArr aXc))), .mov .r9 (.mem (hdr (sArr aT))), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr Public.aTmp))),
    .mov32 .rbp (.imm 0)]

/-- `addMod`'s sum. -/
def amLoop : Prog isa :=
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
    .store (ix .r8 .r14) .rax, cfToRbp]

/-- `addMod`'s carry and the reload of its output's base. -/
def amB3 : List Instr :=
  [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
    .mov .rbx (.mem (hdr (sArr aXc)))]

theorem addMod_eq :
    addMod aXc aXc aT = .seq (.block VG.Proof.Bignum.X86_64.amB1) (.seq VG.Proof.Bignum.X86_64.amLoop (.seq (.block VG.Proof.Bignum.X86_64.amB3) (.seq subMod selectAcc))) := rfl

/-- The workspace of `addMod`, for some `-m⁻¹`. -/
def AmPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- After `addMod`'s loads. -/
def AmHd (L : Ws) (t : State) : Prop :=
  t.gpr .rdi = L.B ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXc) ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aT) ∧
    t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aN) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧
    t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aTmp) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
    GoodW L t ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- Before `addMod`'s subtraction and selection. -/
def AmMid (L : Ws) (t : State) : Prop :=
  t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXc) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aN) ∧
    t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aTmp)

theorem amHd_ok {L : Ws} {s : State} (h : VG.Proof.Bignum.X86_64.AmPre L s) : WP isa (.block VG.Proof.Bignum.X86_64.amB1) s (VG.Proof.Bignum.X86_64.AmHd L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r9, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXc) ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aT) ∧
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aN) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aTmp) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
      t.mem = s.mem)
    (by unfold VG.Proof.Bignum.X86_64.amB1; xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aXc) (by decide), hl (sArr aT) (by decide),
      hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hl (sArr Public.aTmp) (by decide), hg.hdr.harr aXc (by decide), hg.hdr.harr aT (by decide),
      hg.hdr.harr Public.aN (by decide), hg.hdr.harr Public.aAcc (by decide), hg.hdr.harr Public.aTmp (by decide),
      hg.hdr.hw]) rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6, h7, hm⟩, k⟩ => ⟨(k.gpr (by decide)).trans hg.rdi, h1, h2, h3, h4, h5, h6, h7,
      ⟨minv, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hw, hw'⟩

theorem amTail_ok {L : Ws} {s₁ : State} (h : VG.Proof.Bignum.X86_64.AmHd L s₁) : WP isa (.seq VG.Proof.Bignum.X86_64.amLoop (.block VG.Proof.Bignum.X86_64.amB3)) s₁ (VG.Proof.Bignum.X86_64.AmMid L) := by
  obtain ⟨hdi, hbx, h9, h10, h8, h12, hsi, hbp, ⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hs₁ := hg.scr
  have hn := hs₁.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => (slot_le hj).trans hZ
  have sA := sl Public.aAcc (by decide)
  have sX := sl aXc (by decide)
  have sT := sl aT (by decide)
  have p1 := VG.Proof.Bignum.X86_64.slot_sep (w := L.w) (show aXc ≠ Public.aAcc by decide)
  have p2 := VG.Proof.Bignum.X86_64.slot_sep (w := L.w) (show aT ≠ Public.aAcc by decide)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      AddInv s₁ L.B L.Z (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) (VG.Proof.Bignum.X86_64.slot L.w aXc) (VG.Proof.Bignum.X86_64.slot L.w aT) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := L.w) (by omega) hw'
    (AddInv s₁ L.B L.Z (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) (VG.Proof.Bignum.X86_64.slot L.w aXc) (VG.Proof.Bignum.X86_64.slot L.w aT)) h0
    (fun j _ hj t hI => addStep_ok h8 hbx h9 h12 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, -⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 L.w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = L.B := (hI.keep.gpr (by decide)).trans hdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (VG.Proof.Bignum.X86_64.off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have q1 := hdr_lt_slot L.w Public.aAcc (show sArr aXc < 32 by decide)
  have q2 := hdr_lt_slot L.w 8 (show sArr aXc < 32 by decide)
  have ho₂ : VG.Proof.Bignum.X86_64.word s₂.mem L.B (8 * sArr aXc) = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXc) := by
    rw [hI.out.word (by omega) (by omega)]
    exact hg.hdr.harr aXc (by decide)
  have hX : ∀ v : BitVec 64,
      (s₂.mem.writeW (VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w Public.aAcc + 8 * L.w)) v).readW (VG.Proof.Bignum.X86_64.off L.B (8 * sArr aXc)) 64 =
        VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXc) := fun v =>
    ((VG.Proof.Bignum.X86_64.writeW_outside s₂.mem L.B v (by omega)).word (Or.inl (by omega)) (by omega)).trans ho₂
  refine WP.mono (WP.keep [.rax, .rbp, .rbx] (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aXc))
    (by
      unfold VG.Proof.Bignum.X86_64.amB3 cfFromRbp
      xrun [State.ea, ix, hdr, s₂di, hdrOff, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show VG.Proof.Bignum.X86_64.slot L.w Public.aAcc + 8 * L.w + 8 ≤ L.Z by omega), sx0, hl₂ (sArr aXc) (by decide),
        hX]) rfl) fun t ⟨hbx', k⟩ => ⟨hbx', ?_, ?_, ?_, ?_⟩
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h10)
  · exact (k.gpr (by decide)).trans s₂8
  · exact (k.gpr (by decide)).trans s₂12
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans hsi)

theorem pins_amHd : Pins VG.Proof.Bignum.X86_64.AmHd [.rdi, .rbx, .r9, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, -⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, -⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]

theorem pins_amMid : Pins VG.Proof.Bignum.X86_64.AmMid [.rbx, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

/-- `addMod aXc aXc aT` is constant time for any modulus. -/
theorem addMod_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.AmPre) (addMod aXc aXc aT) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.addMod_eq]
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.AmMid)
    (RelCT.assoc' (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.AmHd) [.rdi]
      (VG.Proof.Bignum.X86_64.pins_rdiB (fun L => L.B) fun _ _ ⟨⟨_, hg, _⟩, _⟩ => hg.rdi) (by taint_decide) fun _ _ h => VG.Proof.Bignum.X86_64.amHd_ok h)
      (two_taint _ VG.Proof.Bignum.X86_64.pins_amHd (by taint_decide))))
    fun _ _ h => WP.seq (WP.seq (WP.mono (VG.Proof.Bignum.X86_64.amHd_ok h) fun _ h₁ => WP.seq_iff.mp (VG.Proof.Bignum.X86_64.amTail_ok h₁))))
    (two_taint _ VG.Proof.Bignum.X86_64.pins_amMid (by taint_decide))))

/-! ## The loop's body -/

/-- The sizes. -/
def XF (p : VG.Proof.Bignum.X86_64.XPub) : Prop := 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30

/-- After `k` chunks. -/
def RLoop (j : Nat) (p : VG.Proof.Bignum.X86_64.XPub) (k : Nat) (t : State) : Prop :=
  ∃ (s : State) (minv : BitVec 64) (X : Nat), RInv s p.B p.Z p.o p.w p.wx j minv X k t ∧ VG.Proof.Bignum.X86_64.XF p ∧ 1 < X ∧ j < 8

/-- Before chunk `k`. -/
def RBody (j : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  q.2 < (q.1.w + q.1.wx - 1) / q.1.wx ∧ VG.Proof.Bignum.X86_64.RLoop j q.1 q.2 t

/-- After the chunk's array is cleared. -/
def RB1 (j : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧ VG.Proof.Bignum.X86_64.XF q.1

/-- After the comparison of the words left with `w_X`. -/
def RB2 (j : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .r12 = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    t.cf = some (decide (q.1.w - q.2 * q.1.wx < q.1.wx))

/-- The chunk's length. -/
def RB3 (j : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)

/-- Before the chunk's copy. -/
def RB4 (j : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  t.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx aChunk) ∧
    t.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)

/-- After the chunk's copy (`redcLoad_ok`). -/
def RB5 (j : Nat) (q : VG.Proof.Bignum.X86_64.XPub × Nat) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    XVals t q.1.B q.1.o q.1.wx minv X ∧ 1 < X ∧
    t.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx) ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧ VG.Proof.Bignum.X86_64.XF q.1

/-- The prime, before a multiplication. -/
def RA0 (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧ 1 < X ∧ VG.Proof.Bignum.X86_64.XF p

/-- After `A' := A R⁻¹`. -/
def RA1 (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧ 1 < X ∧
    wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx aXc) p.wx < X ∧ VG.Proof.Bignum.X86_64.XF p

/-- After `T := c R⁻¹`. -/
def RA2 (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧
    wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx aXc) p.wx < X ∧ wv t.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx aT) p.wx < X ∧ VG.Proof.Bignum.X86_64.XF p

theorem rb1_ok {j : Nat} {q : VG.Proof.Bignum.X86_64.XPub × Nat} {t : State} (h : VG.Proof.Bignum.X86_64.RBody j q t) :
    WP isa (zeroArr aChunk) t (VG.Proof.Bignum.X86_64.RB1 j q) := by
  obtain ⟨hk, s, minv, X, hI, hf, -, -⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hkw : q.2 * q.1.wx < q.1.w := (lt_chunks (by omega)).mp hk
  have hlw : lowW q.1.w q.1.wx q.2 = q.2 * q.1.wx := Nat.min_eq_right (by omega)
  have hc := hI.ctx
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hC := slot_le (w := q.1.wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot q.1.wx aChunk (show 31 < 32 by decide)
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (show aChunk < 8 by decide))
    fun t₁ ⟨_, ho₁, k₁⟩ => ⟨minv, hc.of_frm (Frm.of_outside ho₁ (by simp [redcRanges])) (redcRanges_ok _) k₁.2.2
      (k₁.gpr (by decide)), ?_, ?_, hf⟩
  · rw [ho₁.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega), hI.rem, hlw]
  · rw [ho₁.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega), hI.src, hlw]

theorem rb2_ok {j : Nat} {q : VG.Proof.Bignum.X86_64.XPub × Nat} {t : State} (h : VG.Proof.Bignum.X86_64.RB1 j q t) :
    WP isa (.block [.mov .r12 (.mem (hdr sRem)), .alu .cmp .r12 (.mem (hdr sW))]) t (VG.Proof.Bignum.X86_64.RB2 j q) := by
  obtain ⟨minv, hc, hrem, hsrc, hw2, hwx, hw30⟩ := h
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  exact WP.mono (WP.keep [.r12] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
      t₂.cf = some (decide (q.1.w - q.2 * q.1.wx < q.1.wx)) ∧ t₂.mem = t.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sRem (by decide), hrem, hl sW (by decide), hc.hdr.hw,
      ofNat_lt_ofNat (show q.1.w - q.2 * q.1.wx < 2 ^ 64 by omega) (show q.1.wx < 2 ^ 64 by omega)]) rfl)
    fun t₂ ⟨⟨h12, hcf, hm⟩, k⟩ => ⟨minv, hc.of_keep hm k (by decide), by rw [hm]; exact hsrc, h12, hcf⟩

theorem rb3_ok {j : Nat} {q : VG.Proof.Bignum.X86_64.XPub × Nat} {t : State} (h : VG.Proof.Bignum.X86_64.RB2 j q t ∧ isa.eval .b t = some false) :
    WP isa (.block [.mov .r12 (.mem (hdr sW))]) t (VG.Proof.Bignum.X86_64.RB3 j q) := by
  obtain ⟨⟨minv, hc, hsrc, -, hcf⟩, hb⟩ := h
  have hge := VG.Proof.Bignum.X86_64.ge_of_cf hcf hb
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  exact WP.mono (WP.keep [.r12] (Q := fun t' => t'.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx) ∧
      t'.mem = t.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sW (by decide), hc.hdr.hw, Nat.min_eq_right hge]) rfl)
    fun t' ⟨⟨h12, hm⟩, k⟩ => ⟨minv, hc.of_keep hm k (by decide), by rw [hm]; exact hsrc, h12⟩

theorem rb4_ok {j : Nat} {q : VG.Proof.Bignum.X86_64.XPub × Nat} {t : State} (h : VG.Proof.Bignum.X86_64.RB3 j q t) :
    WP isa (.block [.mov .rsi (.mem (hdr sSrc)), .mov .rbx (.mem (hdr (sArr aChunk)))]) t (VG.Proof.Bignum.X86_64.RB4 j q) := by
  obtain ⟨minv, hc, hsrc, h12⟩ := h
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  exact WP.mono (WP.keep [.rsi, .rbx] (Q := fun t' => t'.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
      t'.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx aChunk))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sSrc (by decide), hsrc, hl (sArr aChunk) (by decide),
      hc.hdr.harr aChunk (by decide)]) rfl)
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, (k.gpr (by decide)).trans h12⟩

theorem pins_subCtx {α : Type} {Φ : α → State → Prop} (f : α → VG.Proof.Bignum.X86_64.XPub)
    (h : ∀ a s, Φ a s → ∃ minv, SubCtx s (f a).B (f a).Z (f a).o (f a).w (f a).wx minv) : Pins Φ [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_rdiB (fun a => VG.Proof.Bignum.X86_64.off (f a).B (f a).o) fun a s hs => let ⟨_, hc⟩ := h a s hs; hc.rdi

/-- A chunk into its array. -/
theorem redcLoad_ct (j : Nat) : RelCT isa (Two (VG.Proof.Bignum.X86_64.RBody j)) (seqs redcLoad) fun _ _ => True := by
  simp only [redcLoad, seqs]
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.RB1 j) (two_map (fun q => q.1.ws)
    (fun q t ⟨_, _, minv, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩) (VG.Proof.Bignum.X86_64.zeroArr_ct (by decide) (by taint_decide)))
    fun _ _ h => VG.Proof.Bignum.X86_64.rb1_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.RB2 j) [.rdi] (VG.Proof.Bignum.X86_64.pins_subCtx (·.1) fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩)
    (by taint_decide) fun _ _ h => VG.Proof.Bignum.X86_64.rb2_ok h) ?_
  refine RelCT.seq (R := Two (VG.Proof.Bignum.X86_64.RB3 j)) (two_ite (fun q s₁ s₂ ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => by
    simp only [VG.X86_64.eval, h₁, h₂]) ?_ ?_) ?_
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun q t ⟨⟨minv, hc, hs, h12, hcf⟩, hb⟩ =>
      ⟨minv, hc, hs, by rw [h12, Nat.min_eq_left (Nat.le_of_lt (VG.Proof.Bignum.X86_64.lt_of_cf hcf hb))]⟩) hp
  · exact two_piece [.rdi] (VG.Proof.Bignum.X86_64.pins_subCtx (·.1) fun _ _ ⟨⟨minv, hc, _⟩, _⟩ => ⟨minv, hc⟩) (by taint_decide)
      fun _ _ h => VG.Proof.Bignum.X86_64.rb3_ok h
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.RB4 j) [.rdi] (VG.Proof.Bignum.X86_64.pins_subCtx (·.1) fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩)
    (by taint_decide) fun _ _ h => VG.Proof.Bignum.X86_64.rb4_ok h) ?_
  refine two_taint [.rsi, .rbx, .r12] (VG.Proof.Bignum.X86_64.pins_of (fun q r => if r = .rsi then VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 *
      q.1.wx))
    else if r = .rbx then VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (VG.Proof.Bignum.X86_64.slot q.1.wx aChunk)
    else BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)) fun q s h r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem ra0_ok {j : Nat} {q : VG.Proof.Bignum.X86_64.XPub × Nat} {t : State} (h : VG.Proof.Bignum.X86_64.RB5 j q t) :
    WP isa (.block [.mov .rax (.mem (hdr sRem)), .alu .sub .rax (.reg .r12), .store (hdr sRem) .rax,
      .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12),
      .alu .add .r12 (.mem (hdr sSrc)), .store (hdr sSrc) .r12]) t (VG.Proof.Bignum.X86_64.RA0 q.1) := by
  obtain ⟨minv, X, hc, hv, hX1, h12, hrem, hsrc, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hcr : min (q.1.w - q.2 * q.1.wx) q.1.wx ≤ q.1.w - q.2 * q.1.wx := Nat.min_le_left _ _
  have hr : q.1.w - q.2 * q.1.wx < 2 ^ 31 := by omega
  generalize q.1.w - q.2 * q.1.wx = r at hrem h12 hcr hr
  generalize min r q.1.wx = c at h12 hcr
  generalize VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 * q.1.wx) = e at hsrc
  have hn := hc.good.scr.nowrap
  have rok := redcRanges_ok q.1.wx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  have hst : ∀ i < 32, InRegions t.wr (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.st (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  have hX : ∀ v : BitVec 64, (t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sRem)) v).readW
      (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sSrc)) 64 = VG.Proof.Bignum.X86_64.off q.1.B e := fun v =>
    (hdrStore_hdr t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) v (by decide) (by decide) (by decide)).trans hsrc
  refine WP.mono (WP.keep [.rax, .r12] (Q := fun t₁ => t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sRem))
      (BitVec.ofNat 64 (r - c))).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sSrc)) (VG.Proof.Bignum.X86_64.off q.1.B (e + 8 * c)))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sRem (by decide), hrem, h12, VG.Offset.ofNat_sub_ofNat hcr,
      hst sRem (by decide), ofNat_dbl, hX, hl sSrc (by decide), hst sSrc (by decide), ofNat_add_off,
      show e + 2 * (2 * (2 * c)) = e + 8 * c by omega]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t.mem (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (d := 8 * sRem) (BitVec.ofNat 64 (r - c)) (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (8 * sRem)) (BitVec.ofNat 64 (r - c)))
    (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (d := 8 * sSrc) (VG.Proof.Bignum.X86_64.off q.1.B (e + 8 * c)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off q.1.B q.1.o) (redcRanges q.1.wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [redcRanges])).trans (Frm.of_outside o2 (by simp [redcRanges]))
  exact ⟨minv, X, hc.of_frm f₁ rok k₁.2.2 (k₁.gpr (by decide)), hv.of_frm (by omega) (by omega) f₁, hX1, hf⟩

theorem ra1_ok (M : Mont) {p : VG.Proof.Bignum.X86_64.XPub} {t : State} (h : VG.Proof.Bignum.X86_64.RA0 p t) :
    WP isa (M.mm aXc aXc Public.aOne) t (VG.Proof.Bignum.X86_64.RA1 p) := by
  obtain ⟨minv, X, hc, hv, hX1, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  exact WP.mono (mmOne_ok M hc hv hw2 (by omega) hX1 (d := aXc) (a := aXc) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t' ⟨hc', hv', hlt, _⟩ => ⟨minv, X, hc', hv', hX1, hlt, hf⟩

theorem ra2_ok (M : Mont) {p : VG.Proof.Bignum.X86_64.XPub} {t : State} (h : VG.Proof.Bignum.X86_64.RA1 p t) :
    WP isa (M.mm aT aChunk Public.aOne) t (VG.Proof.Bignum.X86_64.RA2 p) := by
  obtain ⟨minv, X, hc, hv, hX1, hlt, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hn : (VG.Proof.Bignum.X86_64.off p.B p.o).toNat + VG.Proof.Bignum.X86_64.slot p.wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  exact WP.mono (mmOne_ok M hc hv hw2 (by omega) hX1 (d := aT) (a := aChunk) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t' ⟨hc', hv', hlt', _, ha, _⟩ =>
      ⟨minv, X, hc', hv', by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hlt, hlt', hf⟩

theorem ra3_ok {p : VG.Proof.Bignum.X86_64.XPub} {t : State} (h : VG.Proof.Bignum.X86_64.RA2 p t) :
    WP isa (addMod aXc aXc aT) t fun t' => t'.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o := by
  obtain ⟨minv, X, hc, hv, hlt, hlt', hw2, hwx, hw30⟩ := h
  exact WP.mono (addMod_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hw2 (by omega) (o := aXc) (a := aXc) (b := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hv.n]; exact hlt) (by rw [hv.n]; exact hlt')) fun t' ⟨_, _, k⟩ => (k.gpr (by decide)).trans hc.rdi

/-- The words left and the source advanced, and `A := A R⁻¹ + c R⁻¹`. -/
theorem redcAcc_ct (M : Mont) (j : Nat) : RelCT isa (Two (VG.Proof.Bignum.X86_64.RB5 j)) (seqs (redcAcc M.mm)) fun _ _ => True := by
  simp only [redcAcc, seqs]
  refine RelCT.seq (two_piece (Ψ := fun q t => VG.Proof.Bignum.X86_64.RA0 q.1 t) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_subCtx (·.1) fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide) fun _ _ h => VG.Proof.Bignum.X86_64.ra0_ok h)
    (two_map (fun q => q.1) (fun _ _ h => h) ?_)
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.RA1) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun _ _ h => VG.Proof.Bignum.X86_64.ra1_ok M h) ?_
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.RA2) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun _ _ h => VG.Proof.Bignum.X86_64.ra2_ok M h) ?_
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o) (two_map XPub.ws
    (fun p _ ⟨minv, _, hc, _, _, _, hw2, _, hw30⟩ => ⟨⟨minv, hc.good, Nat.le_refl _⟩, show 1 ≤ p.wx by omega,
      show p.wx < 2 ^ 31 by omega⟩) VG.Proof.Bignum.X86_64.addMod_ct) fun _ _ h => VG.Proof.Bignum.X86_64.ra3_ok h) ?_
  exact two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_rdiB (fun p => VG.Proof.Bignum.X86_64.off p.B p.o) fun _ _ h => h) (by taint_decide)

/-- One chunk. -/
theorem redcBody_ct (M : Mont) (j : Nat) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RBody j)) (seqs (redcLoad ++ redcAcc M.mm)) fun _ _ => True := by
  refine RelCT.seqs_split (by simp [redcLoad]) (by simp [redcAcc])
    (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.RB5 j) (VG.Proof.Bignum.X86_64.redcLoad_ct j) fun q t h => ?_) (VG.Proof.Bignum.X86_64.redcAcc_ct M j))
  obtain ⟨hk, s, minv, X, hI, hf, hX1, hj⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hkw : q.2 * q.1.wx < q.1.w := (lt_chunks (by omega)).mp hk
  have hlw : lowW q.1.w q.1.wx q.2 = q.2 * q.1.wx := Nat.min_eq_right (by omega)
  have hsl := slot_le (w := q.1.w) hj
  have hrem0 := hI.rem
  have hsrc0 := hI.src
  rw [hlw] at hrem0 hsrc0
  exact WP.mono (redcLoad_ok hI.ctx hw2 hwx hw30 hj (r := q.1.w - q.2 * q.1.wx) (e := VG.Proof.Bignum.X86_64.slot q.1.w j + 8 * (q.2 *
      q.1.wx))
    (by omega) (by omega) (by omega) hrem0 hsrc0) fun t₁ ⟨hc₁, h12₁, _, hrem₁, hsrc₁, _, f₁, _⟩ =>
      ⟨minv, X, hc₁, hI.xv.of_frm (by have := hc₁.good.scr.nowrap; omega) (by omega) f₁, hX1, h12₁, hrem₁, hsrc₁, hf⟩

/-! ## `redc` -/

/-- After `A := 0`. -/
def RZ (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop := ∃ minv, SubCtx t p.B p.Z p.o p.w p.wx minv ∧ VG.Proof.Bignum.X86_64.XF p

/-- After the load of `n`'s base. -/
def RL (p : VG.Proof.Bignum.X86_64.XPub) (t : State) : Prop := t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o ∧ t.gpr .rax = p.B

theorem rz_ok {j : Nat} {p : VG.Proof.Bignum.X86_64.XPub} {s : State} (h : VG.Proof.Bignum.X86_64.RPre j p s) : WP isa (zeroArr aXc) s (VG.Proof.Bignum.X86_64.RZ p) := by
  obtain ⟨minv, X, hc, _, hw2, hwx, hw30, _⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  exact WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (show aXc < 8 by decide))
    fun s₁ ⟨_, ho₁, k₁⟩ => ⟨minv, hc.of_frm (Frm.of_outside ho₁ (by simp [redcRanges])) (redcRanges_ok _) k₁.2.2
      (k₁.gpr (by decide)), hw2, hwx, hw30⟩

theorem rl_ok {p : VG.Proof.Bignum.X86_64.XPub} {t : State} (h : VG.Proof.Bignum.X86_64.RZ p t) : WP isa (.block [.mov .rax (.mem (hdr sLink))]) t (VG.Proof.Bignum.X86_64.RL p) := by
  obtain ⟨_, hc, _⟩ := h
  have hl : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sLink < 32 by decide); omega)
  exact WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = p.B)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl) fun t' ⟨h1, k⟩ => ⟨(k.gpr (by decide)).trans
        hc.rdi, h1⟩

/-- `redc`'s start, given that the taint analysis checks its loads through
`n`'s base (`by taint_decide` for a given `j`). -/
theorem redcHead_ct {j : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr j))),
      .store (hdr sSrc) .rdx, .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sW)), .store (hdr sRem) .rdx]) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RPre j)) (.seq (zeroArr aXc) (.block [.mov .rax (.mem (hdr sLink)),
      .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr j))), .store (hdr sSrc) .rdx, .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sW)),
      .store (hdr sRem) .rdx])) fun _ _ => True :=
  RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.RZ) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (VG.Proof.Bignum.X86_64.zeroArr_ct (by decide) (by taint_decide))) fun _ _ h => VG.Proof.Bignum.X86_64.rz_ok h)
    (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr))
      (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.RL) [.rdi] (VG.Proof.Bignum.X86_64.pins_subCtx id fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide)
        fun _ _ h => VG.Proof.Bignum.X86_64.rl_ok h)
      (two_taint [.rdi, .rax] (VG.Proof.Bignum.X86_64.pins_of (fun p r => if r = .rdi then VG.Proof.Bignum.X86_64.off p.B p.o else p.B) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hT)))

/-- `redc j`, given that the taint analysis checks its loads through `n`'s
base. -/
theorem redc_ct_of (M : Mont) {j : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr j))),
      .store (hdr sSrc) .rdx, .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sW)), .store (hdr sRem) .rdx]) hc).isSome = true) :
    VG.Proof.Bignum.X86_64.RedcCT M j := by
  unfold VG.Proof.Bignum.X86_64.RedcCT
  rw [redc_eq]
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun p t => 0 < (p.w + p.wx - 1) / p.wx ∧ VG.Proof.Bignum.X86_64.RLoop j p 0 t)
    (VG.Proof.Bignum.X86_64.redcHead_ct hT) fun p s h => ?_) ((two_loop (Φ := VG.Proof.Bignum.X86_64.RLoop j) (Ψ := fun _ _ => True) (fun p => (p.w + p.wx - 1) /
        p.wx)
      (VG.Proof.Bignum.X86_64.redcBody_ct M j) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial))
  · obtain ⟨minv, X, hc, hv, hw2, hwx, hw30, hX1, hj⟩ := h
    have hn := hc.good.scr.nowrap
    have hK : 0 < (p.w + p.wx - 1) / p.wx := (lt_chunks (k := 0) (by omega)).mpr (by omega)
    have hl0 : lowW p.w p.wx 0 = 0 := by simp [lowW]
    exact WP.mono (redcHead_ok hc hw2 hwx hw30 hj) fun t₁ ⟨hc₁, hz₁, hsrc₁, hrem₁, f₁, k₁⟩ =>
      ⟨hK, s, minv, X, ⟨hc₁, hv.of_frm hn (by omega) f₁, by rw [hl0, Nat.sub_zero]; exact hrem₁,
        by rw [hl0, Nat.mul_zero, Nat.add_zero]; exact hsrc₁, by rw [hz₁]; omega, by rw [hz₁, hl0]; rfl, f₁, k₁⟩,
        ⟨hw2, hwx, hw30⟩, hX1, hj⟩
  · rintro p k t hk ⟨s, minv, X, hI, hf, hX1, hj⟩
    obtain ⟨hw2, hwx, hw30⟩ := id hf
    exact WP.mono (redcStep_ok M hw2 hwx hw30 hX1 hj hk hI) fun t' ⟨hz, hI'⟩ =>
      ⟨VG.Proof.Bignum.X86_64.eval_ne_count hk hz, fun _ => ⟨s, minv, X, hI', hf, hX1, hj⟩, fun _ => trivial⟩

theorem redc_ct_Y (M : Mont) : VG.Proof.Bignum.X86_64.RedcCT M Public.aY := VG.Proof.Bignum.X86_64.redc_ct_of M (by taint_decide)

theorem redc_ct_X (M : Mont) : VG.Proof.Bignum.X86_64.RedcCT M Public.aX := VG.Proof.Bignum.X86_64.redc_ct_of M (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad`. -/
section

/-!
# RSA with the CRT on x86-64: constant time of the loads into the primes'
workspaces

`loadArr j sp sl` clears an array of a prime's workspace (`zeroArr_ct`),
reads the bytes' pointer and length through the workspace's link, and loads
them (`loadArr_ct`): the link is pinned by correctness, the rest by the taint
analysis.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- A prime's workspace context with the same memory, `rdi` kept. -/
theorem SubCtx.mem {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx s B Z o w wx minv)
    (hm : t.mem = s.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : SubCtx t B Z o w wx minv :=
  ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, hm ▸ h.hdr, hm ▸ h.link, hm ▸ h.nw, hm ▸ h.narr, h.lo, h.hi⟩

theorem LPre.mem {j sp sl : Nat} {p : VG.Proof.Bignum.X86_64.BPub} {s t : State} (h : VG.Proof.Bignum.X86_64.LPre j sp sl p s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.LPre j sp sl p t := by
  obtain ⟨minv, bs, hc, a1, a2, a3, a4, a5, a6, hp, hl, hbl, hsrc, b1, b2, b3⟩ := h
  exact ⟨minv, bs, hc.mem hm k hr, a1, a2, a3, a4, a5, a6, hm ▸ hp, hm ▸ hl, hbl,
    hsrc.congrK (by rw [hm]; exact InScr.refl _ _ _) k, b1, b2, b3⟩

/-- `zeroArr j` keeps `LPre`. -/
theorem LPre.zero {j sp sl : Nat} {p : VG.Proof.Bignum.X86_64.BPub} {s : State} (h : VG.Proof.Bignum.X86_64.LPre j sp sl p s) :
    WP isa (Crt.zeroArr j) s (VG.Proof.Bignum.X86_64.LPre j sp sl p) := by
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.x.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hJ := slot_le (w := p.x.wx) hj
  have hJ0 := hdr_lt_slot p.x.wx j (show 31 < 32 by decide)
  have ho64 : p.x.o < 2 ^ 64 := by omega
  have hr : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot p.x.wx j, 8 * (p.x.wx + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot p.x.wx 8 := by
    simp only [List.mem_singleton, forall_eq]; omega
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) hj) fun t ⟨_, ho₁, k₁⟩ => ?_
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) [(VG.Proof.Bignum.X86_64.slot p.x.wx j, 8 * (p.x.wx + 2))] s.mem t.mem := Frm.of_outside ho₁ (by simp)
  have hb : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem p.x.B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem p.x.B (8 * i) := fun i hi' =>
    f₁.word_below (fun r hr' => (hr r hr').2) (by omega) ho64 (by omega)
  refine ⟨minv, bs, hc.of_frm f₁ hr k₁.2.2 (k₁.gpr (by decide)), hw2, hwx, hw30, hj, hsp, hsl,
    (hb sp hsp).trans hp, (hb sl hsl).trans hl, hbl, hsrc.congrK ?_ k₁, hk1, hk', hkw⟩
  exact InScr.of_frm (f₁.rebase ho64 fun r hr' => by have := (hr r hr').2; omega) fun r hr' => by
    simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr'
    subst hr'; simp only; omega

theorem pins_lpre {j sp sl : Nat} : Pins (VG.Proof.Bignum.X86_64.LPre j sp sl) [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_of (fun p _ => VG.Proof.Bignum.X86_64.off p.x.B p.x.o) fun _ _ ⟨_, _, hc, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi

/-- The registers of `loadBE`. -/
def LRegs (j : Nat) (p : VG.Proof.Bignum.X86_64.BPub) (t : State) : Prop :=
  t.gpr .rsi = p.ptr ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx j)

/-- `loadArr j sp sl`, given that the taint analysis checks its header loads. -/
theorem loadArr_ct {j sp sl : Nat} (hj : j < 8) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hZ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc₁).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sp)),
      .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sl)), .mov .rbx (.mem (hdr (sArr j)))]) hc₂).isSome = true) :
    VG.Proof.Bignum.X86_64.LoadCT j sp sl := by
  unfold VG.Proof.Bignum.X86_64.LoadCT loadArr
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : VG.Proof.Bignum.X86_64.BPub => (⟨VG.Proof.Bignum.X86_64.off p.x.B p.x.o, VG.Proof.Bignum.X86_64.slot p.x.wx 8, p.x.wx⟩ : Ws))
    (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (VG.Proof.Bignum.X86_64.zeroArr_ct hj hZ)) fun p s h => h.zero) ?_
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.LPre j sp sl p t ∧ t.gpr .rax = p.x.B) [.rdi]
      (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_lpre p s₁ s₂ h₁ h₂) (by taint_decide) ?_)
    (two_piece (Ψ := VG.Proof.Bignum.X86_64.LRegs j) [.rdi, .rax]
      (VG.Proof.Bignum.X86_64.pins_of (fun (p : VG.Proof.Bignum.X86_64.BPub) r => if r = .rdi then VG.Proof.Bignum.X86_64.off p.x.B p.x.o else p.x.B) fun p s ⟨⟨_, _, hc, _⟩, hax⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hax) hT ?_)))
    (two_taint [.rsi, .rcx, .rbx] (VG.Proof.Bignum.X86_64.pins_of (fun (p : VG.Proof.Bignum.X86_64.BPub) r => if r = .rsi then p.ptr else if r = .rcx then
        BitVec.ofNat 64 p.len else VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx j)) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2) (by taint_decide))
  · intro p s h
    have h' := h
    obtain ⟨_, _, hc, -⟩ := h'
    have hn := hc.scr.nowrap
    have hi := hc.hi
    have hl₁ : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (8 * sLink)) 8 :=
      hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 (show sLink < 32 by decide); omega)
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.x.B ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.link]) rfl)
      fun t ⟨⟨hax, hm⟩, k⟩ => ⟨h.mem hm k (by decide), hax⟩
  · rintro p s ⟨⟨_, bs, hc, -, -, -, hj, hsp, hsl, hp, hl, hbl, -⟩, hax⟩
    have hn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
    have hl₁ : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (8 * i)) 8 := fun i hi' =>
      hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 hi'; omega)
    have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.x.B (8 * i)) 8 := fun i hi' =>
      hc.scr.ld (by omega)
    unfold VG.Proof.Bignum.X86_64.LRegs; rw [← hbl]
    exact WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ptr ∧
        t.gpr .rcx = BitVec.ofNat 64 bs.length ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.x.B p.x.o) (VG.Proof.Bignum.X86_64.slot p.x.wx j))
      (by xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hc.rdi, hax, hdrOff, hln sp hsp, hp, hln sl hsl, hl,
        hl₁ (sArr j) (by unfold sArr; omega), hc.hdr.harr j hj]) rfl) fun t h => h.1

theorem loadArr_ct_pN : VG.Proof.Bignum.X86_64.LoadCT Public.aN sP sPlen := VG.Proof.Bignum.X86_64.loadArr_ct (by decide) (by taint_decide) (by taint_decide)

theorem loadArr_ct_pI : VG.Proof.Bignum.X86_64.LoadCT aChunk sQinv sPlen := VG.Proof.Bignum.X86_64.loadArr_ct (by decide) (by taint_decide) (by taint_decide)

theorem loadArr_ct_qN : VG.Proof.Bignum.X86_64.LoadCT Public.aN sQ sQlen := VG.Proof.Bignum.X86_64.loadArr_ct (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupFix`. -/
section

/-!
# RSA with the CRT on x86-64: constant time of a prime's fixes

`primeFix` in a prime's workspace (`primeFix_ct`): the mask's load reads
`n`'s header through the workspace's link, pinned by correctness; the
masking loop, the low word's fix, `-X⁻¹` and the number 1 then run from
registers that correctness pins (the array's base and `w_X`). What each
piece keeps and changes (`pf1_ok` to `pf4_ok`) gives `primeFix_frm`, what
`primeFix` changes whatever the mask and the prime.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `minv` changes only its registers, whatever `rbx`. -/
theorem minv_keep (s : State) :
    WP isa (.block minv) s fun t => VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem :=
  WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .r15] (Q := fun t => t.mem = s.mem) (by unfold minv newton; simp only [List.cons_append, List.nil_append]; xrun) rfl)
    fun _ ⟨h, k⟩ => ⟨k, h⟩

/-! ## The pieces' correctness -/

theorem pf1_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block fixMask) s fun t => SubCtx t B Z o w wx minv ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) [(8 * sMaskX, 8)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s t := by
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  refine WP.mono (fixMask_ok hc hM) fun t ⟨hm, k⟩ => ?_
  have o₁ := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sMaskX) (VG.Proof.Bignum.X86_64.mask c) (by decide)
  rw [← hm] at o₁
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) [(8 * sMaskX, 8)] s.mem t.mem := Frm.of_outside o₁ (by simp)
  exact ⟨hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMaskX sFn; omega) k.2.2
    (k.gpr (by decide)), by rw [hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _, f₁, k⟩

/-- `maskArr_ok`, with the registers it leaves. -/
theorem maskArr_regs {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (seqs (maskArr j)) s fun t => VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) (8 * w) s.mem t.mem ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sj := (slot_le (w := w) hj).trans hZ
  unfold maskArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sMaskX (by decide),
      hl (sArr j) (by unfold sArr; omega), hl sW (by decide), hm, hg.hdr.harr j hj,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h15, h12, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      MaskInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w j) c 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (MaskInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w j) c) h0
    (fun i _ hi t hI => maskStep_ok hbx h15 h12 (by omega) (by omega) hi hI)) fun t hI => ?_
  have ho := hI.out
  rw [hm₁] at ho
  exact ⟨ho, (hI.keep.gpr (by decide)).trans hbx, (hI.keep.gpr (by decide)).trans h12,
    (k₁.trans hI.keep).mono (by decide)⟩

theorem pf2_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hm : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (seqs (maskArr Public.aN)) s fun t => SubCtx t B Z o w wx minv ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  refine WP.mono (VG.Proof.Bignum.X86_64.maskArr_regs hc.good (Nat.le_refl _) hw hw' (by decide) hm) fun t ⟨ho, hbx, h12, k⟩ => ?_
  have f : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := VG.Proof.Bignum.X86_64.slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k.2.2 (k.gpr (by decide)),
    hbx, h12, f, k⟩

/-- A prime's workspace context after a store of its `-X⁻¹`. -/
theorem SubCtx.setMinv {s t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sMinv)) v)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx v := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8x := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hh : ∀ k < 32, k ≠ sMinv → VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * k) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * k) := fun k hk hne => by
    rw [hm]; exact hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hne)
  have hb : ∀ k < 32, VG.Proof.Bignum.X86_64.word t.mem B (8 * k) = VG.Proof.Bignum.X86_64.word s.mem B (8 * k) := fun k hk => by
    rw [hm, off_off]
    exact (VG.Proof.Bignum.X86_64.writeW_outside s.mem B (d := o + 8 * sMinv) v (by unfold sMinv; omega)).word
      (Or.inl (by unfold sMinv; omega)) (by omega)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi, ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw,
    by rw [hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _,
    fun j hj => (hh _ (by unfold sArr; omega) (by unfold sArr sMinv; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), hlo, hi⟩

theorem pf3_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aN))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wx) :
    WP isa (.block (fixLow ++ VG.Impl.Bignum.X86_64.minv ++ fixTail)) s fun t =>
      SubCtx t B Z o w wx (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMinv)) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hg := hc.good
  have hn := hg.scr.nowrap
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hd : VG.Proof.Bignum.X86_64.slot wx Public.aN + 8 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by omega
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbx] (c := .block fixLow) (Q := fun t =>
      ∃ v : BitVec 64, t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aN)) v) (by
    unfold fixLow
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hg.scr.ld hd,
      hg.scr.st hd]
    exact ⟨_, rfl⟩) rfl) fun s₁ ⟨⟨v, hm₁⟩, k₁⟩ => ?_
  have o₁ := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off B o) (d := VG.Proof.Bignum.X86_64.slot wx Public.aN) v (by omega)
  rw [← hm₁] at o₁
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := VG.Proof.Bignum.X86_64.slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k₁.2.2
    (k₁.gpr (by decide))
  refine WP.mono (VG.Proof.Bignum.X86_64.minv_keep s₁) fun s₂ ⟨k₂, hm₂⟩ => ?_
  have hc₂ := hc₁.mem hm₂ k₂ (by decide)
  have hs₂ := hc₂.good.scr
  refine WP.mono (WP.keep [.rdx, .rcx] (c := .block fixTail) (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 0 ∧
      t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sMinv)) (s₂.gpr .r15)) (by
    unfold fixTail
    xrun [State.ea, hdr, hc₂.rdi, hdrOff, hs₂.st (d := 8 * sMinv) (by unfold sMinv; omega)]) rfl)
    fun t ⟨⟨hcx, hm₃⟩, k₃⟩ => ?_
  have o₃ := VG.Proof.Bignum.X86_64.writeW_outside s₂.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sMinv) (s₂.gpr .r15) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm (VG.Proof.Bignum.X86_64.off B o) [(8 * sMinv, 8)] s₂.mem t.mem := Frm.of_outside o₃ (by simp)
  have K := (k₁.trans k₂).trans k₃
  refine ⟨hc₂.setMinv (by rw [hm₃, VG.Proof.Bignum.X86_64.word_writeW_self]) k₃.2.2 (k₃.gpr (by decide)), ?_, hcx, ?_,
    K.mono (by decide)⟩
  · exact ((k₂.trans k₃).gpr (by decide)).trans ((k₁.gpr (by decide)).trans h12)
  · rw [hm₂] at f₃
    exact (f₁.append f₃).mono fun r hr => by simpa using hr

theorem pf4_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31) (h12 : s.gpr .r12 = BitVec.ofNat 64 wx)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 0) :
    WP isa (setWord Public.aOne .rcx) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r8, .r14] s t := by
  have h0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aOne < 8 by decide)
  refine WP.mono (setWord_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) h12 hw hw' (o := Public.aOne) (by decide)
    (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k.2.2 (k.gpr (by decide)),
    f, k⟩

/-- What `primeFix` changes, whatever the mask and the prime. -/
def pfRanges (wx : Nat) : List (Nat × Nat) :=
  [(8 * sMaskX, 8), (VG.Proof.Bignum.X86_64.slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8), (VG.Proof.Bignum.X86_64.slot wx Public.aOne, 8 * (wx + 2))]

theorem primeFix_frm {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask c) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 31) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.pfRanges wx) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  rw [primeFix_eq]
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.pf1_ok hc hM) fun s₁ ⟨hc₁, hm₁, f₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.pf2_ok hc₁ hw hw' hm₁) fun s₂ ⟨hc₂, hbx₂, h12₂, f₂, k₂⟩ => ?_
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.pf3_ok hc₂ hbx₂ h12₂) fun s₃ ⟨hc₃, h12₃, hcx₃, f₃, k₃⟩ => ?_)
  refine WP.mono (VG.Proof.Bignum.X86_64.pf4_ok hc₃ hw hw' h12₃ hcx₃) fun t ⟨hc₄, f₄, k₄⟩ => ⟨_, hc₄, ?_,
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  exact (((f₁.append f₂).append f₃).append f₄).mono fun r hr => by
    simp only [VG.Proof.Bignum.X86_64.pfRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h]

/-! ## Constant time -/

/-- `primeFix`'s hypotheses: a prime's workspace (some `-X⁻¹`), and the
modulus' mask (some value). -/
def PF (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the mask's load. -/
def PF1 (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the masking. -/
def PF2 (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 31

/-- After `-X⁻¹`. -/
def PF3 (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rcx = BitVec.ofNat 64 0

/-- `setWord`'s registers. -/
def PF4 (p : VG.Proof.Bignum.X86_64.XPub) (s : State) : Prop :=
  s.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aOne) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rcx = BitVec.ofNat 64 0

theorem fixMask_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.PF) (.block fixMask) fun _ _ => True := by
  unfold fixMask
  refine RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => VG.Proof.Bignum.X86_64.PF p t ∧ t.gpr .rax = p.B) [.rdi]
      (VG.Proof.Bignum.X86_64.pins_of (fun p _ => VG.Proof.Bignum.X86_64.off p.B p.o) fun p s ⟨_, _, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide) ?_)
    (two_taint [.rdi, .rax] (VG.Proof.Bignum.X86_64.pins_of (fun (p : VG.Proof.Bignum.X86_64.XPub) r => if r = .rdi then VG.Proof.Bignum.X86_64.off p.B p.o else p.B)
      fun p s ⟨⟨_, _, hc, _⟩, hax⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hax) (by taint_decide)))
  rintro p s ⟨minv, c, hc, hM, h1, h2⟩
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hl₁ : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sLink < 32 by decide); omega)
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.link]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ⟨⟨minv, c, hc.mem hm k (by decide), hm ▸ hM, h1, h2⟩, hax⟩

/-- `primeFix` is constant time. -/
theorem primeFix_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.PF) (seqs primeFix) fun _ _ => True := by
  rw [primeFix_eq]
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [maskArr]) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.PF1) VG.Proof.Bignum.X86_64.fixMask_ct
    fun p s ⟨minv, c, hc, hM, h1, h2⟩ => WP.mono (VG.Proof.Bignum.X86_64.pf1_ok hc hM) fun t ⟨hc', hm, _⟩ =>
      ⟨minv, c, hc', hm, h1, h2⟩) ?_)
  refine RelCT.seqs_append (by simp [maskArr]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.PF2)
    (two_map (fun p : VG.Proof.Bignum.X86_64.XPub => (⟨VG.Proof.Bignum.X86_64.off p.B p.o, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩ : Ws))
      (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (VG.Proof.Bignum.X86_64.maskArr_ct (by decide) (by taint_decide)))
    fun p s ⟨minv, c, hc, hm, h1, h2⟩ => WP.mono (VG.Proof.Bignum.X86_64.pf2_ok hc (by omega) h2 hm) fun t ⟨hc', hbx, h12, _⟩ =>
      ⟨minv, hc', hbx, h12, h1, h2⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.PF3) [.rdi, .rbx]
    (VG.Proof.Bignum.X86_64.pins_of (fun (p : VG.Proof.Bignum.X86_64.XPub) r => if r = .rdi then VG.Proof.Bignum.X86_64.off p.B p.o else VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aN))
      fun p s ⟨_, hc, hbx, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hbx) (by taint_decide)
    fun p s ⟨_, hc, hbx, h12, _⟩ => WP.mono (VG.Proof.Bignum.X86_64.pf3_ok hc hbx h12) fun t ⟨hc', h12', hcx, _⟩ =>
      ⟨_, hc', h12', hcx⟩) ?_
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.PF4) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_of (fun p _ => VG.Proof.Bignum.X86_64.off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (VG.Proof.Bignum.X86_64.pins_of (fun (p : VG.Proof.Bignum.X86_64.XPub) r => if r = .r8 then
      VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aOne) else if r = .r12 then BitVec.ofNat 64 p.wx else BitVec.ofNat 64 0)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨_, hc, h12, hcx⟩
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hl₁ : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (8 * sArr Public.aOne)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sArr Public.aOne < 32 by decide); omega)
  exact WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.o) (VG.Proof.Bignum.X86_64.slot p.wx Public.aOne))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.hdr.harr Public.aOne (by decide)]) rfl)
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs`. -/
section

/-!
# RSA with the CRT on x86-64: constant time of the primes' setup

`wsNew` branches on the prime's length, which is public (`wsNew_ct`).
`primesSetup` (`setup_ct`) runs in the modulus' workspace, then in the
primes'; between its pieces, what the next one reads from the headers
(`SSt`, the primes' links, sizes and bases `WsF`) is kept by the frames of
the pieces before it.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## A new workspace -/

/-- `wsNew`'s first block. -/
def wsB1 (slotWs slotLen : Nat) : List Instr :=
  [.store (hdr slotWs) .rax, .mov .r12 (.mem (hdr slotLen)), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .alu .cmp .r12 (.imm 2)]

/-- `wsNew`'s last block. -/
def wsB3 : List Instr :=
  ([.mov .rsi (.reg .rdi), .mov .rdi (.reg .rax), .store (hdr sLink) .rsi, .store (hdr sW) .r12] : List Instr) ++
    setBases ++ ([.mov .rdi (.reg .rsi)] : List Instr)

theorem wsNew_eq (slotWs slotLen : Nat) : wsNew slotWs slotLen =
    [.block (VG.Proof.Bignum.X86_64.wsB1 slotWs slotLen), .ite .b (.block [.mov32 .r12 (.imm 2)]) (.block []), .block VG.Proof.Bignum.X86_64.wsB3] := rfl

/-- The public data of `wsNew`: the modulus' working space, the new
workspace's offset and the length. -/
structure WPub where
  B : Addr
  Z : Nat
  o : Nat
  len : Nat

/-- `wsNew_ok`'s hypotheses. -/
def WN (slotWs slotLen : Nat) (p : VG.Proof.Bignum.X86_64.WPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ s.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.o ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * slotLen) = BitVec.ofNat 64 p.len ∧ slotWs < 32 ∧ slotLen < 32 ∧ slotWs ≠ slotLen ∧
    p.len < 2 ^ 32 ∧ 8 * 32 ≤ p.o ∧ p.o + VG.Proof.Bignum.X86_64.slot (wsWords p.len) 8 ≤ p.Z

/-- After `wsNew`'s first block. -/
def W1 (p : VG.Proof.Bignum.X86_64.WPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.o ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.len + 7) / 8) ∧
    t.cf = some (decide ((p.len + 7) / 8 < 2))

/-- After `wsNew`'s branch. -/
def W3 (p : VG.Proof.Bignum.X86_64.WPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.o ∧ t.gpr .r12 = BitVec.ofNat 64 (wsWords p.len)

theorem wsB1_ok {slotWs slotLen : Nat} {p : VG.Proof.Bignum.X86_64.WPub} {s : State} (h : VG.Proof.Bignum.X86_64.WN slotWs slotLen p s) :
    WP isa (.block (VG.Proof.Bignum.X86_64.wsB1 slotWs slotLen)) s (VG.Proof.Bignum.X86_64.W1 p) := by
  obtain ⟨hs, hdi, hax, hlen, hws, hsl, hne, hlen', ho, hZ⟩ := h
  have hn := hs.nowrap
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.len) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hX : ∀ v : BitVec 64, (s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * slotWs)) v).readW (VG.Proof.Bignum.X86_64.off p.B (8 * slotLen)) 64 =
      BitVec.ofNat 64 p.len := fun v => (hdrStore_hdr s.mem p.B v hws hsl hne).trans hlen
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((p.len + 7) / 8) ∧
      t.cf = some (decide ((p.len + 7) / 8 < 2)))
    (by
      unfold VG.Proof.Bignum.X86_64.wsB1
      xrun [State.ea, hdr, hdi, hdrOff, hs.st (d := 8 * slotWs) (by omega), hax,
        hs.ld (d := 8 * slotLen) (by omega), hX, shr3_w p.len hlen', sx2,
        cf_lt2 (show (p.len + 7) / 8 < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨h12, hcf⟩, k⟩ => ⟨(k.gpr (by decide)).trans hdi, (k.gpr (by decide)).trans hax, h12, hcf⟩

theorem pins_w3 : Pins VG.Proof.Bignum.X86_64.W3 [.rdi, .rax, .r12] :=
  VG.Proof.Bignum.X86_64.pins_of (fun p r => if r = .rdi then p.B else if r = .rax then VG.Proof.Bignum.X86_64.off p.B p.o else
      BitVec.ofNat 64 (wsWords p.len)) fun p s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2

theorem pins_nil {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr (by simp)

/-- `wsNew`, given that the taint analysis checks its first block. -/
theorem wsNew_ct {slotWs slotLen : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Proof.Bignum.X86_64.wsB1 slotWs slotLen)) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.WN slotWs slotLen)) (seqs (wsNew slotWs slotLen)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.wsNew_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.W1) [.rdi] (VG.Proof.Bignum.X86_64.pins_of (fun p _ => p.B) fun p s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.2.1) h1 fun p s h => VG.Proof.Bignum.X86_64.wsB1_ok h) ?_
  refine RelCT.seq (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2.2.2, h₂.2.2.2]) ?_ ?_)
    (two_taint _ VG.Proof.Bignum.X86_64.pins_w3 (by taint_decide))
  · refine two_piece (Ψ := VG.Proof.Bignum.X86_64.W3) [] VG.Proof.Bignum.X86_64.pins_nil (by taint_decide) fun p s ⟨h, hb⟩ => ?_
    have h2 : (p.len + 7) / 8 < 2 := by
      simp only [VG.X86_64.eval, h.2.2.2, Option.some.injEq, decide_eq_true_eq] at hb; exact hb
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (wsWords p.len)) (by
      xrun
      unfold wsWords; rw [Nat.max_eq_left (by omega)]; rfl) rfl)
      fun t ⟨h12, k⟩ => ⟨(k.gpr (by decide)).trans h.1, (k.gpr (by decide)).trans h.2.1, h12⟩
  · refine two_piece (Ψ := VG.Proof.Bignum.X86_64.W3) [] VG.Proof.Bignum.X86_64.pins_nil (by taint_decide) fun p s ⟨h, hb⟩ => ?_
    have h2 : ¬ (p.len + 7) / 8 < 2 := by
      simp only [VG.X86_64.eval, h.2.2.2, Option.some.injEq, decide_eq_false_iff_not] at hb; exact hb
    refine WP.block_nil ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2.1]; unfold wsWords; rw [Nat.max_eq_right (by omega)]

/-! ## The setup's states -/

/-- What the setup keeps: the modulus' working space and header, its
arguments, and the byte strings. -/
def SSt (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop :=
  ∃ pb qb ib : List Byte, VG.Proof.Bignum.X86_64.Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sP) = p.pp ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sQ) = p.qp ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sQinv) = p.ip ∧
    Src t p.B p.Z p.pp pb ∧ Src t p.B p.Z p.qp qb ∧ Src t p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

theorem SSt.frm {p : VG.Proof.Bignum.X86_64.SetupPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.SSt p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 8 * 29 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.SSt p t' := by
  obtain ⟨pb, qb, ib, hs, hH, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ offQ p.w p.pl := by unfold offQ VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hw : ∀ i < 29, VG.Proof.Bignum.X86_64.word t'.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega)) (by omega)
  have hi := InScr.of_frm hf fun r hr' => (hr r hr').2
  exact ⟨pb, qb, ib, hs.congr k.2.2, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩, a1, a2, hZ, (hw _ (by decide)).trans b1,
    (hw _ (by decide)).trans b2, (hw _ (by decide)).trans b3, (hw _ (by decide)).trans b4,
    (hw _ (by decide)).trans b5, c1.congrK hi k, c2.congrK hi k, c3.congrK hi k, d⟩

theorem SSt.mem {p : VG.Proof.Bignum.X86_64.SetupPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.SSt p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.SSt p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem SSt.nowrap {p : VG.Proof.Bignum.X86_64.SetupPub} {t : State} (h : VG.Proof.Bignum.X86_64.SSt p t) : p.B.toNat + p.Z ≤ 2 ^ 64 :=
  let ⟨_, _, _, hs, _⟩ := h; hs.nowrap

theorem SSt.scr {p : VG.Proof.Bignum.X86_64.SetupPub} {t : State} (h : VG.Proof.Bignum.X86_64.SSt p t) : VG.Proof.Bignum.X86_64.Scr t p.B p.Z :=
  let ⟨_, _, _, hs, _⟩ := h; hs

theorem SSt.bounds {p : VG.Proof.Bignum.X86_64.SetupPub} {t : State} (h : VG.Proof.Bignum.X86_64.SSt p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧
      1 ≤ p.ql ∧ p.ql < 8 * p.w :=
  let ⟨_, _, _, _, _, a1, a2, hZ, _, _, _, _, _, _, _, _, _, _, _, d1, d2, d3, d4⟩ := h
  ⟨a1, a2, hZ, d1, d2, d3, d4⟩

/-- A prime's workspace at `off B o`: its link, size and bases. -/
def WsF (m : Mem) (B : Addr) (o wx : Nat) : Prop :=
  VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B ∧ VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sW) = BitVec.ofNat 64 wx ∧
    ∀ j < 8, VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sArr j) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j)

theorem WsF.frm {m m' : Mem} {B : Addr} {o wx : Nat} (h : VG.Proof.Bignum.X86_64.WsF m B o wx) {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, o + 8 * 17 ≤ r.1 ∨ r.1 + r.2 ≤ o) (ho : o + 8 * 17 ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.WsF m' B o wx := by
  have hw : ∀ i < 17, VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact hf.word_eq (fun r hr' => by have := hr r hr'; omega) (by omega)
  exact ⟨(hw _ (by decide)).trans h.1, (hw _ (by decide)).trans h.2.1,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (h.2.2 j hj)⟩

/-- After `p`'s workspace. -/
def SA (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.SSt p t ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.B (offP p.w) ∧ VG.Proof.Bignum.X86_64.WsF t.mem p.B (offP p.w) (wsWords p.pl)

/-- After `q`'s workspace. -/
def SB (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.SA p t ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl) ∧ VG.Proof.Bignum.X86_64.WsF t.mem p.B (offQ p.w p.pl) (wsWords p.ql)

theorem SB.frm {p : VG.Proof.Bignum.X86_64.SetupPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.SB p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, offP p.w + 8 * 17 ≤ r.1 ∧ (r.1 + r.2 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ r.1) ∧
      r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.SB p t' := by
  obtain ⟨⟨hS, hP, hFP⟩, hQ, hFQ⟩ := h
  have hn := hS.nowrap
  obtain ⟨a1, -, hZ, -, -, -, -⟩ := hS.bounds
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hPQ : offP p.w + 256 ≤ offQ p.w p.pl := by unfold offP offQ VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hP0 : offP p.w = VG.Proof.Bignum.X86_64.slot p.w 8 := rfl
  have hQZ : offQ p.w p.pl + 256 ≤ p.Z := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hZ; omega
  refine ⟨⟨hS.frm hf (fun r hr' => by have := hr r hr'; omega) k, ?_, hFP.frm hf (fun r hr' => by
    have := hr r hr'; omega) (by omega)⟩, ?_, hFQ.frm hf (fun r hr' => by have := hr r hr'; omega) (by omega)⟩
  · rw [hf.word_eq (fun r hr' => by have := hr r hr'; unfold sWsP sFn; omega) (by unfold sWsP sFn; omega)]
    exact hP
  · rw [hf.word_eq (fun r hr' => by have := hr r hr'; unfold sWsQ sFn; omega) (by unfold sWsQ sFn; omega)]
    exact hQ

theorem SA.frm' {p : VG.Proof.Bignum.X86_64.SetupPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.SA p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.SA p t' :=
  ⟨h.1.mem hm k, hm ▸ h.2.1, hm ▸ h.2.2⟩

/-- `SB` with `rdi` at `f p`. -/
def SBr (f : VG.Proof.Bignum.X86_64.SetupPub → Addr) (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop := VG.Proof.Bignum.X86_64.SB p t ∧ t.gpr .rdi = f p

theorem pins_sbr (f : VG.Proof.Bignum.X86_64.SetupPub → Addr) : Pins (VG.Proof.Bignum.X86_64.SBr f) [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem SetupPre.sst {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SetupPre p s) : VG.Proof.Bignum.X86_64.SSt p s ∧ s.gpr .rdi = p.B :=
  let ⟨pb, qb, ib, hg, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩ := h
  ⟨⟨pb, qb, ib, hg.scr, hg.hdr, a1, a2, hZ, b1, b2, b3, b4, b5, c1, c2, c3, d⟩, hg.rdi⟩

/-- Before `p`'s workspace: its offset in `rax`. -/
def SS1 (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop := VG.Proof.Bignum.X86_64.SSt p t ∧ t.gpr .rdi = p.B ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B (offP p.w)

/-- Before `q`'s workspace: its offset in `rax`. -/
def SS3 (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop := VG.Proof.Bignum.X86_64.SA p t ∧ t.gpr .rdi = p.B ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl)

theorem stage1_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SetupPre p s) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ wsEnd)) s (VG.Proof.Bignum.X86_64.SS1 p) := by
  obtain ⟨hS, hdi⟩ := h.sst
  have hS' := hS
  obtain ⟨_, _, _, hs, hH, a1, -, hZ, -⟩ := hS'
  have : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ offQ p.w p.pl := by unfold offQ; omega
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = p.B ∧ t.mem = s.mem) (by xrun [hdi]) rfl)
    fun s₁ ⟨⟨hdx₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (wsEnd_ok (wx := p.w) (hs.congr k₁.2.2) hdx₁ (by rw [hm₁]; exact hH.hw)
    (by rw [hm₁]; exact hH.harr _ (by decide)) (by omega)) fun t ⟨hax, hm₂, k₂⟩ =>
    ⟨hS.mem (hm₂.trans hm₁) (k₁.trans k₂), (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi), hax⟩

theorem SB.mem {p : VG.Proof.Bignum.X86_64.SetupPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.SB p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.SB p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k

theorem wsP_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SS1 p s) :
    WP isa (seqs (wsNew sWsP sPlen)) s fun t => VG.Proof.Bignum.X86_64.SA p t ∧ t.gpr .rdi = p.B := by
  obtain ⟨hS, hdi, hax⟩ := h
  have hS' := hS
  obtain ⟨_, _, _, hs, -, a1, a2, hZ, hpl, -, -, -, -, -, -, -, -, -, -, d1, d2, -, -⟩ := hS'
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold offQ at hZ
  exact WP.mono (wsNew_ok (o := offP p.w) (len := p.pl) hs hdi hax (by decide) (by decide) (by decide) hpl
    (by omega) (by unfold offP; omega) (by unfold offP; omega))
    fun t ⟨hWs, hl, hw, ha, hdi', f, k⟩ => ⟨⟨hS.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsP, sFn, offP] <;> omega) k, hWs, hl, hw, ha⟩, hdi'⟩

/-- `q`'s workspace's base: `p`'s end. -/
def SS2 (p : VG.Proof.Bignum.X86_64.SetupPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.SA p t ∧ t.gpr .rdi = p.B ∧ t.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B (offP p.w)

theorem stage2_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SA p s ∧ s.gpr .rdi = p.B) :
    WP isa (.block [.mov .rdx (.mem (hdr sWsP))]) s (VG.Proof.Bignum.X86_64.SS2 p) := by
  obtain ⟨hA, hdi⟩ := h
  have hs := hA.1.scr
  have hWsP := hA.2.1
  have := hA.1.bounds
  have hn := hs.nowrap
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold offQ at this
  exact WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B (offP p.w) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hWsP]) rfl)
    fun t ⟨⟨hdx, hm⟩, k⟩ => ⟨hA.frm' hm k, (k.gpr (by decide)).trans hdi, hdx⟩

theorem stage3_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SS2 p s) : WP isa (.block wsEndT) s (VG.Proof.Bignum.X86_64.SS3 p) := by
  obtain ⟨hA, hdi, hdx⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, -, hZ, -⟩, -, -, hw, ha⟩ := hA'
  have hn := hs.nowrap
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold offQ at hZ
  refine WP.mono (wsEndT_ok (wx := wsWords p.pl) (hs.sub (o := offP p.w)
    (n := VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8) (by unfold offP; omega) (by omega)) hdx hw
    (ha _ (by decide)) (Nat.le_refl _)) fun t ⟨hax, hm, k⟩ => ?_
  rw [off_off] at hax
  exact ⟨hA.frm' hm k, (k.gpr (by decide)).trans hdi, by rw [hax]; exact congrArg (VG.Proof.Bignum.X86_64.off p.B) (by unfold offQ offP; omega)⟩

theorem wsQ_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SS3 p s) :
    WP isa (seqs (wsNew sWsQ sQlen)) s (VG.Proof.Bignum.X86_64.SBr (·.B) p) := by
  obtain ⟨hA, hdi, hax⟩ := h
  have hA' := hA
  obtain ⟨⟨_, _, _, hs, -, a1, a2, hZ, -, hql, -, -, -, -, -, -, -, -, -, d1, d2, d3, d4⟩, hWsP, hF⟩ := hA'
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hn := hs.nowrap
  unfold offQ at hZ
  refine WP.mono (wsNew_ok (o := offQ p.w p.pl) (len := p.ql) hs hdi hax (by decide) (by decide) (by decide) hql
    (by omega) (by unfold offQ; omega) (by unfold offQ; omega))
    fun t ⟨hWs, hl, hw, ha, hdi', f, k⟩ => ⟨⟨⟨hA.1.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ] <;> omega) k, ?_, hF.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sWsQ, sFn, offQ, offP] <;> omega) (by unfold offP; omega)⟩,
      hWs, hl, hw, ha⟩, hdi'⟩
  rw [f.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sWsQ, sWsP, sFn, offQ] <;> omega) (by unfold sWsP sFn; omega)]
  exact hWsP

theorem SB.scr {p : VG.Proof.Bignum.X86_64.SetupPub} {t : State} (h : VG.Proof.Bignum.X86_64.SB p t) : VG.Proof.Bignum.X86_64.Scr t p.B p.Z := let ⟨⟨⟨_, _, _, hs, _⟩, _⟩, _⟩ := h; hs

theorem SB.bounds {p : VG.Proof.Bignum.X86_64.SetupPub} {t : State} (h : VG.Proof.Bignum.X86_64.SB p t) :
    8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ offQ p.w p.pl + VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 + tabBytes (wsWords p.ql) ≤ p.Z ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧
      1 ≤ p.ql ∧ p.ql < 8 * p.w := h.1.1.bounds

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem SB.move {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SB p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .rdi = X) (hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off X (8 * i)) 8) (hw : VG.Proof.Bignum.X86_64.word s.mem X (8 * i) = A') :
    WP isa (.block [.mov .rdi (.mem (hdr i))]) s (VG.Proof.Bignum.X86_64.SBr (fun _ => A') p) :=
  WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = A' ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hw]) rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

/-- A prime's workspace context from `SB`. -/
theorem SB.sub {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SB p s) {o wx : Nat} (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B o)
    (hF : VG.Proof.Bignum.X86_64.WsF s.mem p.B o wx) (hlo : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ p.Z) :
    SubCtx s p.B p.Z o p.w wx (VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B o) (8 * sMinv)) :=
  let ⟨⟨⟨_, _, _, hs, hH, _⟩, _⟩, _⟩ := h
  ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hhi⟩

/-- A load into a prime's workspace keeps `SB`. -/
theorem SB.load {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} {o wx j sp sl len : Nat} {ptr : Addr} (h : VG.Proof.Bignum.X86_64.SB p s)
    (hL : VG.Proof.Bignum.X86_64.LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s)
    (hr : offP p.w + 8 * 17 ≤ o + 256 ∧ (o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ offQ p.w p.pl ∨ offQ p.w p.pl + 8 * 17 ≤ o + 256)) :
    WP isa (seqs (loadArr j sp sl)) s fun t => VG.Proof.Bignum.X86_64.SB p t ∧ t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B o := by
  simp only [VG.Proof.Bignum.X86_64.LPre] at hL
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := hL
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hc.scr.nowrap
  have hi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ p.Z := hc.hi
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact WP.mono (primeLoad_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw) fun t ⟨hc', _, ho, k⟩ =>
    ⟨h.frm (Frm.of_load ho hj (by omega) (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only; omega) k, hc'.rdi⟩

/-- `LPre` from `SB`, in the workspace at `off B o` (`rdi`). -/
theorem SB.lpre {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SB p s) {o wx j sp sl len : Nat} {ptr : Addr} {bs : List Byte}
    (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B o) (hF : VG.Proof.Bignum.X86_64.WsF s.mem p.B o wx) (hlo : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ p.Z)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ p.w) (hj : j < 8) (hsp : sp < 32) (hsl : sl < 32)
    (hp : VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sp) = ptr) (hl : VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hbl : bs.length = len) (hsrc : Src s p.B p.Z ptr bs) (hk1 : 1 ≤ bs.length) (hk' : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ wx) : VG.Proof.Bignum.X86_64.LPre j sp sl ⟨⟨p.B, p.Z, o, p.w, wx⟩, ptr, len⟩ s :=
  ⟨_, bs, h.sub hdi hF hlo hhi, hw2, hwx, by have := h.bounds; show p.w < 2 ^ 30; omega, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk',
    hkw⟩

theorem lpreP {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p s) :
    VG.Proof.Bignum.X86_64.LPre Public.aN sP sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ s ∧
      VG.Proof.Bignum.X86_64.LPre aChunk sQinv sPlen ⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ s := by
  obtain ⟨hB, hdi⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, hpl, -, hpp, -, hip, c1, -, c3, l1, -, l3, d1, d2, -, -⟩, -, hF⟩, -⟩ := hB'
  unfold offQ at hZ
  have hw := wsWords_le d2 (by omega)
  exact ⟨hB.lpre hdi hF (Nat.le_refl _) (by unfold offP; omega) (by unfold wsWords; omega) hw (by decide)
    (by decide) (by decide) hpp (by rw [l1]; exact hpl) l1 c1 (by omega) (by omega) (by unfold wsWords; omega),
    hB.lpre hdi hF (Nat.le_refl _) (by unfold offP; omega) (by unfold wsWords; omega) hw (by decide)
    (by decide) (by decide) hip (by rw [l3]; exact hpl) l3 c3 (by omega) (by omega) (by unfold wsWords; omega)⟩

theorem lpreQ {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl)) p s) :
    VG.Proof.Bignum.X86_64.LPre Public.aN sQ sQlen ⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ s := by
  obtain ⟨hB, hdi⟩ := h
  have hB' := hB
  obtain ⟨⟨⟨pb, qb, ib, hs, -, a1, a2, hZ, -, hql, -, hqp, -, -, c2, -, -, l2, -, -, -, d3, d4⟩, -, -⟩, -, hF⟩ := hB'
  exact hB.lpre hdi hF (by unfold offQ; omega) hZ (by unfold wsWords; omega) (wsWords_le d4 (by omega))
    (by decide) (by decide) (by decide) hqp (by rw [l2]; exact hql) l2 c2 (by omega) (by omega)
    (by unfold wsWords; omega)

theorem SS1.wn {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SS1 p s) :
    VG.Proof.Bignum.X86_64.WN sWsP sPlen ⟨p.B, p.Z, offP p.w, p.pl⟩ s := by
  obtain ⟨⟨_, _, _, hs, -, a1, a2, hZ, hpl, -, -, -, -, -, -, -, -, -, -, d1, d2, -, -⟩, hdi, hax⟩ := h
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold offQ at hZ
  exact ⟨hs, hdi, hax, hpl, by decide, by decide, by decide, by simp only; omega, by simp only; unfold offP; omega,
    by simp only; unfold offP; omega⟩

theorem SS3.wn {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SS3 p s) :
    VG.Proof.Bignum.X86_64.WN sWsQ sQlen ⟨p.B, p.Z, offQ p.w p.pl, p.ql⟩ s := by
  obtain ⟨⟨⟨_, _, _, hs, -, a1, a2, hZ, -, hql, -, -, -, -, -, -, -, -, -, -, -, d3, d4⟩, -⟩, hdi, hax⟩ := h
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact ⟨hs, hdi, hax, hql, by decide, by decide, by decide, by simp only; omega, by simp only; unfold offQ; omega,
    by simp only; omega⟩

theorem enterP_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (·.B) p s) :
    WP isa (.block [enterP]) s (VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p) := by
  obtain ⟨h, hdi⟩ := h
  have := h.bounds
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact h.move (X := p.B) (i := sWsP) hdi (h.scr.ld (by unfold sWsP sFn offQ at *; omega)) h.1.2.1

theorem leaveP_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p s) :
    WP isa (.block [leave]) s (VG.Proof.Bignum.X86_64.SBr (·.B) p) := by
  obtain ⟨h, hdi⟩ := h
  have hF := h.1.2.2
  have := h.bounds
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact h.move (X := VG.Proof.Bignum.X86_64.off p.B (offP p.w)) (i := sLink) hdi ((h.scr.sub (o := offP p.w)
    (n := VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8) (by unfold offQ offP at *; omega) (by omega)).ld (by unfold sLink sFn; omega)) hF.1

theorem enterQ_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (·.B) p s) :
    WP isa (.block [enterQ]) s (VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl)) p) := by
  obtain ⟨h, hdi⟩ := h
  have := h.bounds
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  exact h.move (X := p.B) (i := sWsQ) hdi (h.scr.ld (by unfold sWsQ sFn offQ at *; omega)) h.2.1

theorem loadP1_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p s) :
    WP isa (seqs (loadArr Public.aN sP sPlen)) s (VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p) :=
  SB.load (o := offP p.w) (wx := wsWords p.pl) h.1 (VG.Proof.Bignum.X86_64.lpreP h).1
    ⟨by omega, Or.inl (by unfold offQ offP; omega)⟩

theorem loadP2_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p s) :
    WP isa (seqs (loadArr aChunk sQinv sPlen)) s (VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) p) :=
  SB.load (o := offP p.w) (wx := wsWords p.pl) h.1 (VG.Proof.Bignum.X86_64.lpreP h).2
    ⟨by omega, Or.inl (by unfold offQ offP; omega)⟩

theorem loadQ_ok {p : VG.Proof.Bignum.X86_64.SetupPub} {s : State} (h : VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl)) p s) :
    WP isa (seqs (loadArr Public.aN sQ sQlen)) s (VG.Proof.Bignum.X86_64.SBr (fun p => VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl)) p) :=
  SB.load (o := offQ p.w p.pl) (wx := wsWords p.ql) h.1 (VG.Proof.Bignum.X86_64.lpreQ h) ⟨by unfold offQ offP; omega, Or.inr (by omega)⟩

theorem leaveEnterQ_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.SBr fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w))) (.block [leave, enterQ])
    (Two (VG.Proof.Bignum.X86_64.SBr fun p => VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl))) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.SBr (·.B)) [.rdi] (VG.Proof.Bignum.X86_64.pins_sbr _) (by taint_decide) fun p s h => VG.Proof.Bignum.X86_64.leaveP_ok h)
      (two_piece [.rdi] (VG.Proof.Bignum.X86_64.pins_sbr _) (by taint_decide) fun p s h => VG.Proof.Bignum.X86_64.enterQ_ok h))

theorem setup_ct : VG.Proof.Bignum.X86_64.SetupCT := by
  unfold VG.Proof.Bignum.X86_64.SetupCT primesSetup
  simp only [List.append_assoc]
  -- `p`'s workspace.
  refine RelCT.seqs_append (by simp) (by simp [wsNew]) (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.SS1) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sst.2) (by taint_decide)
    fun p s h => VG.Proof.Bignum.X86_64.stage1_ok h) ?_)
  refine RelCT.seqs_append (by simp [wsNew]) (by simp) (RelCT.seq (two_post (two_map
    (fun p : VG.Proof.Bignum.X86_64.SetupPub => (⟨p.B, p.Z, offP p.w, p.pl⟩ : VG.Proof.Bignum.X86_64.WPub)) (fun p s h => h.wn) (VG.Proof.Bignum.X86_64.wsNew_ct (by taint_decide)))
    fun p s h => VG.Proof.Bignum.X86_64.wsP_ok h) ?_)
  -- `q`'s workspace.
  refine RelCT.seqs_append (by simp) (by simp [wsNew]) (RelCT.seq (RelCT.block_append
    (l₁ := ([.mov .rdx (.mem (hdr sWsP))] : List Instr)) (l₂ := wsEndT) (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.SS2) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_of (fun p _ => p.B) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
    fun p s h => VG.Proof.Bignum.X86_64.stage2_ok h) (two_piece (Ψ := VG.Proof.Bignum.X86_64.SS3) [.rdx]
    (VG.Proof.Bignum.X86_64.pins_of (fun p _ => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.2.2) (by taint_decide)
    fun p s h => VG.Proof.Bignum.X86_64.stage3_ok h))) ?_)
  refine RelCT.seqs_append (by simp [wsNew]) (by simp) (RelCT.seq (two_post (two_map
    (fun p : VG.Proof.Bignum.X86_64.SetupPub => (⟨p.B, p.Z, offQ p.w p.pl, p.ql⟩ : VG.Proof.Bignum.X86_64.WPub)) (fun p s h => h.wn) (VG.Proof.Bignum.X86_64.wsNew_ct (by taint_decide)))
    fun p s h => VG.Proof.Bignum.X86_64.wsQ_ok h) ?_)
  -- Into `p`'s workspace: `p` and `qInv`.
  refine RelCT.seqs_append (by simp) (by simp [loadArr]) (RelCT.seq (two_piece
    (Ψ := VG.Proof.Bignum.X86_64.SBr fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) [.rdi] (VG.Proof.Bignum.X86_64.pins_sbr _) (by taint_decide) fun p s h => VG.Proof.Bignum.X86_64.enterP_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp [loadArr]) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.SBr fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) (two_map
    (fun p : VG.Proof.Bignum.X86_64.SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.pp, p.pl⟩ : VG.Proof.Bignum.X86_64.BPub)) (fun p s h => (VG.Proof.Bignum.X86_64.lpreP h).1)
    VG.Proof.Bignum.X86_64.loadArr_ct_pN) fun p s h => VG.Proof.Bignum.X86_64.loadP1_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.SBr fun p => VG.Proof.Bignum.X86_64.off p.B (offP p.w)) (two_map
    (fun p : VG.Proof.Bignum.X86_64.SetupPub => (⟨⟨p.B, p.Z, offP p.w, p.w, wsWords p.pl⟩, p.ip, p.pl⟩ : VG.Proof.Bignum.X86_64.BPub)) (fun p s h => (VG.Proof.Bignum.X86_64.lpreP h).2)
    VG.Proof.Bignum.X86_64.loadArr_ct_pI) fun p s h => VG.Proof.Bignum.X86_64.loadP2_ok h) ?_)
  -- Into `q`'s workspace: `q`.
  refine RelCT.seqs_append (by simp) (by simp [loadArr]) (RelCT.seq VG.Proof.Bignum.X86_64.leaveEnterQ_ct ?_)
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.SBr fun p => VG.Proof.Bignum.X86_64.off p.B (offQ p.w p.pl)) (two_map
    (fun p : VG.Proof.Bignum.X86_64.SetupPub => (⟨⟨p.B, p.Z, offQ p.w p.pl, p.w, wsWords p.ql⟩, p.qp, p.ql⟩ : VG.Proof.Bignum.X86_64.BPub))
    (fun p s h => VG.Proof.Bignum.X86_64.lpreQ h) VG.Proof.Bignum.X86_64.loadArr_ct_qN)
    fun p s h => VG.Proof.Bignum.X86_64.loadQ_ok h) ?_)
  exact two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_sbr _) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtContract`. -/
section

/-!
# RSA with the CRT on x86-64: the contract on the registers

`crtContract` states the shared contract of `vg_rsa_private_crt` on the
registers and the stack, apart from its proofs, for its callers.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_private_crt(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
input = r8, input_len = r9, p = [rsp + 8], p_len = [rsp + 16],
q = [rsp + 24], q_len = [rsp + 32], dp = [rsp + 40], dp_len = [rsp + 48],
dq = [rsp + 56], dq_len = [rsp + 64], qinv = [rsp + 72],
qinv_len = [rsp + 80], scratch = [rsp + 88], scratch_len = [rsp + 96])`. -/
def crtContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let inp : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let scr : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 96⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64 ∧
      s.rd = [n, inp, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint inp ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      (s.gpr .r9).toNat = (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 11).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧ stackArg s₁ 8 = stackArg s₂ 8 ∧
      stackArg s₁ 9 = stackArg s₂ 9 ∧ stackArg s₁ 10 = stackArg s₂ 10 ∧ stackArg s₁ 11 = stackArg s₂ 11 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-- Stack argument `j` is `8 j` bytes after the first. -/
theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtHdr`. -/
section

/-!
# RSA with the CRT on x86-64: the header's arguments

The modulus' header slots that `entry` fills and nothing else writes: the
saved registers, `out`, `n`, `k`, the input and the private key's pointers
and lengths (`hFixed`). Each part's changes keep them (`HFix`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The header slots of the arguments. -/
def hFixed (i : Nat) : Bool :=
  i < 6 || (16 ≤ i && i ≤ 21) || i == 23 || i == 24 || i == 25 || i == 27 || i == 28

/-- A range that keeps the arguments' slots. -/
def KeepsHdr (r : Nat × Nat) : Prop := ∀ i < 32, VG.Proof.Bignum.X86_64.hFixed i = true → 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i

theorem keepsHdr_ge {r : Nat × Nat} (h : 8 * 32 ≤ r.1) : VG.Proof.Bignum.X86_64.KeepsHdr r := fun _ hi _ => Or.inl (by omega)

theorem keepsHdr_slot {j : Nat} (hj : j < 32) (hf : VG.Proof.Bignum.X86_64.hFixed j = false) : VG.Proof.Bignum.X86_64.KeepsHdr (8 * j, 8) := by
  intro i _ hfi
  have : i ≠ j := by rintro rfl; rw [hf] at hfi; exact absurd hfi (by decide)
  simp only; omega

/-- The arguments' slots, unchanged. -/
def HFix (B : Addr) (m m' : Mem) : Prop := ∀ i < 32, VG.Proof.Bignum.X86_64.hFixed i = true → VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i)

theorem HFix.refl (B : Addr) (m : Mem) : VG.Proof.Bignum.X86_64.HFix B m m := fun _ _ _ => rfl

theorem HFix.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Bignum.X86_64.HFix B m₁ m₂) (h₂ : VG.Proof.Bignum.X86_64.HFix B m₂ m₃) : VG.Proof.Bignum.X86_64.HFix B m₁ m₃ :=
  fun i hi hf => (h₂ i hi hf).trans (h₁ i hi hf)

theorem HFix.of_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, VG.Proof.Bignum.X86_64.KeepsHdr r) : VG.Proof.Bignum.X86_64.HFix B m m' := fun i hi hf =>
  h.word_eq (fun r hr' => hr r hr' i hi hf) (by omega)

theorem keepsHdr_gRanges (w : Nat) : ∀ r ∈ gRanges w, VG.Proof.Bignum.X86_64.KeepsHdr r := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_slot (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_slot (by decide) (by decide)

theorem keepsHdr_setupRanges (w : Nat) : ∀ r ∈ setupRanges w, VG.Proof.Bignum.X86_64.KeepsHdr r := by
  have := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aOne (show 31 < 32 by decide)
  simp only [setupRanges, loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_slot (by decide) (by decide)
  · intro i _ hf; simp only [VG.Proof.Bignum.X86_64.hFixed, sArr] at hf ⊢; revert hf; revert i; decide
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_slot (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_slot (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)

theorem keepsHdr_r2Ranges (w : Nat) : ∀ r ∈ r2Ranges w, VG.Proof.Bignum.X86_64.KeepsHdr r := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aR2 (show 31 < 32 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_ge (by simp only; omega)
  · exact VG.Proof.Bignum.X86_64.keepsHdr_slot (by decide) (by decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaComp`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: `ifma`

`ifma_ok`: the IFMA area after `q`'s workspace, both regions, the vector
code, and the results back in the primes' workspaces.

`IMem` gathers what holds throughout: `n`'s header, the primes' headers
(their workspace slots, `sMaskX` and `sIfma`), moduli and ones, and `n`'s
slots for the exponents; `IMem.of_frm` keeps it across any change within
`ifmaR`, the ranges `ifma` writes.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-- The ranges `ifma` writes, but its first two stores. -/
def ifmaR (op oq a : Nat) : List (Nat × Nat) :=
  shiftRanges op (k1Ranges 16 ++ resRanges) ++ shiftRanges oq (k1Ranges 16 ++ resRanges) ++ [(a, 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8)]

/-- What `ifma` keeps, but the area's base in the primes' headers. -/
structure IPre (m : Mem) (B : Addr) (w op oq : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop where
  nh : Hdr m B w minv
  wsP : VG.Proof.Bignum.X86_64.word m B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B op
  wsQ : VG.Proof.Bignum.X86_64.word m B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq
  pws : WsAt m B op 16 mp
  qws : WsAt m B oq 16 mq
  pn : wv m (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16 = P
  pinv : ((VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aN)).toNat * mp.toNat + 1) % 2 ^ 64 = 0
  pone : wv m (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aOne) 16 = 1
  qn : wv m (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16 = Q
  qinv : ((VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aN)).toNat * mq.toNat + 1) % 2 ^ 64 = 0
  qone : wv m (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aOne) 16 = 1
  pmk : VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX) = mk
  dp : VG.Proof.Bignum.X86_64.word m B (8 * sDp) = ep
  pl : VG.Proof.Bignum.X86_64.word m B (8 * sPlen) = BitVec.ofNat 64 lp
  dq : VG.Proof.Bignum.X86_64.word m B (8 * sDq) = eq
  ql : VG.Proof.Bignum.X86_64.word m B (8 * sQlen) = BitVec.ofNat 64 lq

/-- What `ifma` keeps. -/
structure IMem (m : Mem) (B : Addr) (w op oq a : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop extends VG.Proof.Bignum.X86_64.IPre m B w op oq minv mp mq mk P Q ep eq lp lq where
  pia : VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B op) (8 * sIfma) = VG.Proof.Bignum.X86_64.off B a
  qia : VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B oq) (8 * sIfma) = VG.Proof.Bignum.X86_64.off B a

/-- What `IPre` reads: below `p`'s workspace, the first 29 slots of a
prime's header, and its modulus and one. -/
def IKept (op oq d n : Nat) : Prop :=
  d + n ≤ op ∨ (op ≤ d ∧ d + n ≤ op + 8 * 29) ∨ (d = op + VG.Proof.Bignum.X86_64.slot 16 Public.aN ∧ n ≤ 128) ∨
    (d = op + VG.Proof.Bignum.X86_64.slot 16 Public.aOne ∧ n ≤ 128) ∨ (oq ≤ d ∧ d + n ≤ oq + 8 * 29) ∨
    (d = oq + VG.Proof.Bignum.X86_64.slot 16 Public.aN ∧ n ≤ 128) ∨ (d = oq + VG.Proof.Bignum.X86_64.slot 16 Public.aOne ∧ n ≤ 128)

theorem ifmaR_disj {op oq a d n : Nat} (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ a)
    (h : VG.Proof.Bignum.X86_64.IKept op oq d n ∨ (d = op + 8 * sIfma ∧ n = 8) ∨ (d = oq + 8 * sIfma ∧ n = 8)) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.ifmaR op oq a, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have hT : tabBytes 16 = 2304 := rfl
  have hs : ∀ j, VG.Proof.Bignum.X86_64.slot 16 j = 256 + j * 144 := fun j => by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  simp only [VG.Proof.Bignum.X86_64.IKept, Public.aN, Public.aOne, hs, sIfma, sFn] at h
  simp only [VG.Proof.Bignum.X86_64.ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, CrtIfma.sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

theorem ifmaR_le {op oq a : Nat} (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ a) : ∀ r ∈ VG.Proof.Bignum.X86_64.ifmaR op oq a, r.1 + r.2 ≤ a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 := by
  have hT : tabBytes 16 = 2304 := rfl
  have hs : ∀ j, VG.Proof.Bignum.X86_64.slot 16 j = 256 + j * 144 := fun j => by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  simp only [VG.Proof.Bignum.X86_64.ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, CrtIfma.sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

theorem IPre.of_frm {m m' : Mem} {B : Addr} {w op oq : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : VG.Proof.Bignum.X86_64.IPre m B w op oq minv mp mq mk P Q ep eq lp lq) {rs : List (Nat × Nat)}
    (hf : Frm B rs m m') (hr : ∀ d n, VG.Proof.Bignum.X86_64.IKept op oq d n → ∀ r ∈ rs, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq) (hz : oq + VG.Proof.Bignum.X86_64.slot 16 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.IPre m' B w op oq minv mp mq mk P Q ep eq lp lq := by
  have hT : tabBytes 16 = 2304 := rfl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have := slot_le (w := 16) (show Public.aN < 8 by decide)
  have := slot_le (w := 16) (show Public.aOne < 8 by decide)
  have hW : ∀ d, VG.Proof.Bignum.X86_64.IKept op oq d 8 → VG.Proof.Bignum.X86_64.word m' B d = VG.Proof.Bignum.X86_64.word m B d := fun d hk =>
    hf.word_eq (hr d 8 hk) (by unfold VG.Proof.Bignum.X86_64.IKept at hk; omega)
  have hV : ∀ d, VG.Proof.Bignum.X86_64.IKept op oq d 128 → wv m' B d 16 = wv m B d 16 := fun d hk =>
    hf.wv_eq (hr d 128 hk) (by unfold VG.Proof.Bignum.X86_64.IKept at hk; omega)
  have hn : ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := fun i hi => hW _ (.inl (by omega))
  have hp : ∀ i < 29, VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B op) (8 * i) = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inl ⟨by omega, by omega⟩))
  have hq : ∀ i < 29, VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B oq) (8 * i) = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))
  refine ⟨⟨(hn _ (by decide)).trans h.nh.hw, (hn _ (by decide)).trans h.nh.hminv,
      fun j hj => (hn _ (by unfold sArr; omega)).trans (h.nh.harr j hj)⟩,
    (hn _ (by decide)).trans h.wsP, (hn _ (by decide)).trans h.wsQ,
    h.pws.of_words fun i hi => hp i (by omega), h.qws.of_words fun i hi => hq i (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, (hp _ (by decide)).trans h.pmk, (hn _ (by decide)).trans h.dp,
    (hn _ (by decide)).trans h.pl, (hn _ (by decide)).trans h.dq, (hn _ (by decide)).trans h.ql⟩
  · rw [wv_off, hV _ (.inr (.inr (.inl ⟨rfl, le_refl _⟩))), ← wv_off]; exact h.pn
  · rw [word_off, hW _ (.inr (.inr (.inl ⟨rfl, by decide⟩))), ← word_off]; exact h.pinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inl ⟨rfl, le_refl _⟩)))), ← wv_off]; exact h.pone
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, le_refl _⟩)))))), ← wv_off]; exact h.qn
  · rw [word_off, hW _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, by decide⟩)))))), ← word_off]; exact h.qinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, le_refl _⟩)))))), ← wv_off]; exact h.qone

theorem IMem.of_frm {m m' : Mem} {B : Addr} {w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : VG.Proof.Bignum.X86_64.IMem m B w op oq a minv mp mq mk P Q ep eq lp lq)
    (hf : Frm B (VG.Proof.Bignum.X86_64.ifmaR op oq a) m m') (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq)
    (hqa : oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ a) (hz : a ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.IMem m' B w op oq a minv mp mq mk P Q ep eq lp lq := by
  have hT : tabBytes 16 = 2304 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  refine ⟨h.toIPre.of_frm hf (fun d n hk => VG.Proof.Bignum.X86_64.ifmaR_disj hpq hqa (.inl hk)) hlo hpq (by omega), ?_, ?_⟩
  · rw [word_off, hf.word_eq (VG.Proof.Bignum.X86_64.ifmaR_disj hpq hqa (.inr (.inl ⟨rfl, rfl⟩))) (by unfold sIfma sFn; omega), ← word_off]
    exact h.pia
  · rw [word_off, hf.word_eq (VG.Proof.Bignum.X86_64.ifmaR_disj hpq hqa (.inr (.inr ⟨rfl, rfl⟩))) (by unfold sIfma sFn; omega), ← word_off]
    exact h.qia

/-! ## `ifma`'s first half: the regions -/

/-- `ifma`'s first block, from `n`'s workspace to `p`'s. -/
theorem headI_ok {s : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : VG.Proof.Bignum.X86_64.IPre s.mem B w op oq minv mp mq mk P Q ep eq lp lq) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op)
    (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq) (ha : a = oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z) :
    WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))) s fun u =>
      VG.Proof.Bignum.X86_64.IMem u.mem B w op oq a minv mp mq mk P Q ep eq lp lq ∧
      Frm B [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] s.mem u.mem ∧ u.gpr .rdi = VG.Proof.Bignum.X86_64.off B op ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rdi] s u := by
  have hn := hs.nowrap
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  subst ha
  refine WP.mono (ifmaHead_ok ⟨hs, hdi, h.nh⟩ hlo hpq (by omega) h.wsP h.wsQ h.qws) fun u ⟨me, di, k⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem B (d := op + 8 * sIfma) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16))
    (by unfold sIfma sFn; omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (op + 8 * sIfma)) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16))) B
    (d := oq + 8 * sIfma) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16)) (by unfold sIfma sFn; omega)
  rw [off_off B op, off_off B oq (8 * sIfma)] at me
  have f : Frm B [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] s.mem u.mem := by
    rw [me]
    exact (Frm.of_outside o1 (List.mem_cons_self ..)).trans
      (Frm.of_outside o2 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hia : VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) := by
    rw [off_off, Nat.add_assoc]
  refine ⟨⟨h.of_frm f (fun d n hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hs : ∀ j, VG.Proof.Bignum.X86_64.slot 16 j = 256 + j * 144 := fun j => by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
      simp only [VG.Proof.Bignum.X86_64.IKept, hs, Public.aN, Public.aOne] at hk
      rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega) hlo hpq
      (by omega), ?_, ?_⟩, f, di, k⟩
  · rw [word_off, me, o2.word (.inl (by unfold sIfma sFn; omega)) (by unfold sIfma sFn; omega), ← hia]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [word_off, me, ← hia]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _

/-- From one workspace (`rdi = off B o`, linked to `B`) to the one in `n`'s slot `sl`. -/
theorem swapWs_ok {u : State} {B : Addr} {Z o o' sl : Nat} (hs : VG.Proof.Bignum.X86_64.Scr u B Z) (hdi : u.gpr .rdi = VG.Proof.Bignum.X86_64.off B o)
    (hlk : VG.Proof.Bignum.X86_64.word u.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B) (hsl : VG.Proof.Bignum.X86_64.word u.mem B (8 * sl) = VG.Proof.Bignum.X86_64.off B o') (hsl' : sl < 32)
    (ho : o + 8 * 32 ≤ Z) :
    WP isa (.block [leave, .mov .rdi (.mem (hdr sl))]) u fun u' =>
      u'.gpr .rdi = VG.Proof.Bignum.X86_64.off B o' ∧ u'.mem = u.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdi] u u' := by
  have hl : InRegions (u.rd ++ u.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sLink)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  have hl' : InRegions (u.rd ++ u.wr) (VG.Proof.Bignum.X86_64.off B (8 * sl)) 8 := hs.ld (by omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun u' => u'.gpr .rdi = VG.Proof.Bignum.X86_64.off B o' ∧ u'.mem = u.mem) (by
    xrun [leave, State.ea, hdr, hdi, hdrOff, hl, hlk, hl', hsl]) rfl) fun u' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

theorem k1sh_lt (o : Nat) : ∀ r ∈ shiftRanges o (k1Ranges 16), o + 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ o + VG.Proof.Bignum.X86_64.slot 16 8 := by
  have hs : ∀ j, VG.Proof.Bignum.X86_64.slot 16 j = 256 + j * 144 := fun j => by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  simp only [shiftRanges, k1Ranges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    CrtIfma.sCtr, sFn, hs, Public.aAcc, Public.aTmp, aT]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem k1sh_ifmaR (op oq a : Nat) {o : Nat} (ho : o = op ∨ o = oq) :
    ∀ r ∈ shiftRanges o (k1Ranges 16), r ∈ VG.Proof.Bignum.X86_64.ifmaR op oq a := fun r hr => by
  simp only [VG.Proof.Bignum.X86_64.ifmaR, shiftRanges, List.map_append, List.mem_append] at hr ⊢
  rcases ho with rfl | rfl
  · exact .inl (.inl (.inl hr))
  · exact .inl (.inr (.inl hr))

theorem regFr_ifmaR {op oq a o p : Nat} (ho : o = op ∨ o = oq) (hp : p < 2) :
    ∀ r ∈ shiftRanges o (k1Ranges 16) ++ [(a + VG.Impl.Rsa.X86_64.CrtIfma.D * p, VG.Impl.Rsa.X86_64.CrtIfma.D)], ∃ r' ∈ VG.Proof.Bignum.X86_64.ifmaR op oq a,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun r hr => by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have hDp : VG.Impl.Rsa.X86_64.CrtIfma.D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, VG.Proof.Bignum.X86_64.k1sh_ifmaR op oq a ho r hr, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(a, 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8), List.mem_append_right _ (List.mem_singleton_self _),
      by rw [List.mem_singleton.mp hr]; simp only; omega⟩

/-- `ifma`'s first half: the area's base, and both regions. -/
theorem ifmaA_ok {s : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : VG.Proof.Bignum.X86_64.IPre s.mem B w op oq minv mp mq mk P Q ep eq ebp.length ebq.length) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op)
    (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq) (ha : a = oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z)
    (hYp : wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < P) (hYq : wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < Q)
    (hep : Src s B Z ep ebp) (heq : Src s B Z eq ebq) (hLp1 : 1 ≤ ebp.length) (hLp2 : ebp.length ≤ 128)
    (hLq1 : 1 ≤ ebq.length) (hLq2 : ebq.length ≤ 128) :
    WP isa (seqs (([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (CrtIfma.region 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ CrtIfma.region 1 sDq sQlen)))) s fun t =>
      VG.Proof.Bignum.X86_64.IMem t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length ∧
      RegOut t.mem (VG.Proof.Bignum.X86_64.off B a) 0 P (2 ^ 32 * wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 % P)
        (wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16) (wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16)
        (wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16) (mp &&& mask52) ebp ∧
      RegOut t.mem (VG.Proof.Bignum.X86_64.off B a) 1 Q (2 ^ 32 * wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 % Q)
        (wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16) (wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16) 1
        (mq &&& mask52) ebq ∧
      Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ VG.Proof.Bignum.X86_64.ifmaR op oq a) s.mem t.mem ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ t.gpr .rdi = VG.Proof.Bignum.X86_64.off B oq ∧ VG.Proof.MlKem.X86_64.Keep (mmRegs ++ ([.rdi] : List Reg)) s t := by
  have hn := hs.nowrap
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have lY := slot_le (w := 16) (show Public.aY < 8 by decide)
  have lC := slot_le (w := 16) (show aXc < 8 by decide)
  have hY0 := hdr_lt_slot 16 Public.aY (show 31 < 32 by decide)
  have hC0 := hdr_lt_slot 16 aXc (show 31 < 32 by decide)
  -- The head.
  refine wp_seqs_append (by simp) (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (WP.mono
    (VG.Proof.Bignum.X86_64.headI_ok hs hdi h hlo hpq ha haZ) fun u₁ ⟨m₁, f₁, d₁, k₁⟩ => ?_)
  have hf₁ : ∀ {d n}, d + n ≤ op + 8 * sIfma ∨ (op + 8 * sIfma + 8 ≤ d ∧ d + n ≤ oq + 8 * sIfma) ∨
      oq + 8 * sIfma + 8 ≤ d → ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
  have hYp₁ : wv u₁.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 = wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hCp₁ : wv u₁.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 = wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hZ₁ : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], r.1 + r.2 ≤ Z := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega
  -- `p`'s region.
  refine wp_seqs_append (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (by simp) (WP.mono
    (region_ok (p := 0) (SubCtx.mk' (hs.congr k₁.2.2) m₁.nh m₁.pws d₁ hlo (by omega)) m₁.pia (by omega) haZ
      (by decide) m₁.pn (by rw [hYp₁]; exact hYp) (by decide) (by decide) m₁.dp m₁.pl
      (hep.congr (InScr.of_frm f₁ hZ₁) k₁.2.1 k₁.2.2) hLp1 hLp2) fun u₂ ⟨rp, f₂, w₂, d₂, k₂⟩ => ?_)
  have f₂' := f₂.widen (VG.Proof.Bignum.X86_64.regFr_ifmaR (oq := oq) (.inl rfl) (by decide))
  have m₂ := m₁.of_frm f₂' hlo hpq (by omega) (by omega)
  have F₂ : Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ VG.Proof.Bignum.X86_64.ifmaR op oq a) s.mem u₂.mem :=
    (f₁.mono fun r hr => List.mem_append_left _ hr).trans (f₂'.mono fun r hr => List.mem_append_right _ hr)
  have hZF : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ VG.Proof.Bignum.X86_64.ifmaR op oq a, r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hZ₁ r hr
    · have := VG.Proof.Bignum.X86_64.ifmaR_le hpq (by omega) r hr; omega
  -- To `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (WP.mono
    (VG.Proof.Bignum.X86_64.swapWs_ok (o' := oq) (hs.congr (w₂.trans k₁.2.2)) d₂ m₂.pws.link m₂.wsQ (by decide) (by omega))
    fun u₃ ⟨d₃, me₃, k₃⟩ => ?_)
  rw [← me₃] at m₂ F₂
  have hq₃ : ∀ j, j < 8 → j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv u₃.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 j) 16 = wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 j) 16 := fun j hj h1 h2 h3 => by
    have := slot_le (w := 16) hj
    have := hdr_lt_slot 16 j (show 31 < 32 by decide)
    rw [wv_off, wv_off, me₃, f₂.wv_eq (fun r hr => ?_) (by omega),
      f₁.wv_eq (hf₁ (.inr (.inr (by unfold sIfma sFn; omega)))) (by omega)]
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := VG.Proof.Bignum.X86_64.k1sh_lt op r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  have k₁₃ := (k₁.trans k₂).trans k₃
  -- `q`'s region.
  refine WP.mono (region_ok (p := 1) (SubCtx.mk' (hs.congr k₁₃.2.2) m₂.nh m₂.qws d₃ (by omega) (by omega)) m₂.qia
    (by omega) haZ (by decide) m₂.qn (by rw [hq₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hYq)
    (by decide) (by decide) m₂.dq m₂.ql (heq.congr (InScr.of_frm F₂ hZF) k₁₃.2.1 k₁₃.2.2) hLq1 hLq2)
    fun t ⟨rq, f₄, w₄, d₄, k₄⟩ => ?_
  have f₄' := f₄.widen (VG.Proof.Bignum.X86_64.regFr_ifmaR (op := op) (.inr rfl) (by decide))
  rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0)), hYp₁, hCp₁, ← me₃] at rp
  simp only [Nat.one_ne_zero, ↓reduceIte] at rq
  rw [hq₃ _ (by decide) (by decide) (by decide) (by decide),
    hq₃ _ (by decide) (by decide) (by decide) (by decide)] at rq
  refine ⟨m₂.of_frm f₄' hlo hpq (by omega) (by omega), rp.of_frm f₄ (fun r hr => ?_) (by omega), rq,
    F₂.trans (f₄'.mono fun r hr => List.mem_append_right _ hr), w₄.trans k₁₃.2.2, ?_, d₄,
    k₁₃.trans k₄ |>.mono (by simp [mmRegs])⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := VG.Proof.Bignum.X86_64.k1sh_lt oq r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  · rw [k₄.2.1, k₁₃.2.1]

/-! ## `ifma`'s second half: the vector code and the results -/

/-- `p`'s value for prime 0, `q`'s for prime 1. -/
def two {α : Type} (x y : α) (p : Nat) : α := if p = 0 then x else y

/-- The vector code, from `q`'s workspace: the base of the area into `rbx`. -/
theorem vecI_ok {t : State} {B : Addr} {Z w op oq a wp : Nat} {minv mp mq mk : BitVec 64} {P Q C : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} {K : Prop} {Yp Xcp Yq Xcq : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z)
    (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off B oq) (hm : VG.Proof.Bignum.X86_64.IMem t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length)
    (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z) (hqa : oq + VG.Proof.Bignum.X86_64.slot 16 8 ≤ a)
    (rp : RegOut t.mem (VG.Proof.Bignum.X86_64.off B a) 0 P (2 ^ 32 * Yp % P) Xcp Yp Yp (mp &&& mask52) ebp)
    (rq : RegOut t.mem (VG.Proof.Bignum.X86_64.off B a) 1 Q (2 ^ 32 * Yq % Q) Xcq Yq 1 (mq &&& mask52) ebq)
    (hwp : wp = 16) (hPo : P % 2 = 1) (hQo : Q % 2 = 1) (hYp : Yp < P) (hYq : Yq < Q) (hXp : Xcp < P)
    (hXq : Xcq < Q) (vxp : K → Xcp % P = C * 2 ^ (64 * wp) % P) (vxq : K → Xcq % Q = C * 2 ^ (64 * wp) % Q)
    (vyp : K → Yp % P = 2 ^ (64 * wp) % P) (vyq : K → Yq % Q = 2 ^ (64 * wp) % Q)
    (hLp : ebp.length ≤ 128) (hLq : ebq.length ≤ 128) :
    WP isa (seqs [.block [.mov .rbx (.mem (hdr sIfma))], CrtIfma.vec]) t fun t' =>
      (AmmSym.Good t'.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Proof.Bignum.X86_64.two P Q) oY 0 ∧
        (K → AmmSym.val52 t'.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 0 + oY) % P = C ^ Spec.Rsa.os2ip ebp * Yp % P)) ∧
      (AmmSym.Good t'.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Proof.Bignum.X86_64.two P Q) oY 1 ∧
        (K → AmmSym.val52 t'.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1 + oY) % Q = C ^ Spec.Rsa.os2ip ebq * 1 % Q)) ∧
      VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B a) 0 (2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8) t.mem t'.mem ∧ t'.gpr .rdi = t.gpr .rdi ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr &&& 0xFFFF ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hs.nowrap
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h01 : ∀ p, p < 2 → p = 0 ∨ p = 1 := fun p hp => by omega
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = VG.Proof.Bignum.X86_64.off B a ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr) (by
    have hl : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (8 * sIfma)) 8 := by
      rw [off_off]; exact hs.ld (by unfold sIfma sFn; omega)
    xrun [State.ea, hdr, hdi, hdrOff, hl, hm.qia]; and_intros; all_goals rfl) rfl) fun u ⟨⟨bx, me, mx⟩, k⟩ => ?_)
  have hmP := VG.Proof.Bignum.X86_64.wv_lt t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16
  have hmQ := VG.Proof.Bignum.X86_64.wv_lt t.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16
  rw [hm.pn, ← hwp] at hmP
  rw [hm.qn, ← hwp] at hmQ
  refine WP.mono (AmmSym.vecR_ok (M := VG.Proof.Bignum.X86_64.two P Q) (K1 := VG.Proof.Bignum.X86_64.two (2 ^ 32 * Yp % P) (2 ^ 32 * Yq % Q))
    (Xc := VG.Proof.Bignum.X86_64.two Xcp Xcq) (Y := VG.Proof.Bignum.X86_64.two Yp Yq) (Fin := VG.Proof.Bignum.X86_64.two Yp 1) (x := fun _ => C) (mi := VG.Proof.Bignum.X86_64.two mp mq) (Q := K)
    (w := wp) (R := 2 ^ (64 * wp)) hwp rfl bx ((hs.congr k.2.2).sub (by omega) (by omega))
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.n; exact rq.n])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.k1; exact rq.k1])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.x; exact rq.x])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.y; exact rq.y])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.fin; exact rq.fin])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.k0; exact rq.k0])
    (fun p hp => by
      rcases h01 p hp with rfl | rfl
      · show (P % 2 ^ 64 * mp.toNat + 1) % 2 ^ 64 = 0
        rw [← hm.pn, VG.Proof.Bignum.X86_64.wv_mod64 _ _ _ (by decide)]; exact hm.pinv
      · show (Q % 2 ^ 64 * mq.toNat + 1) % 2 ^ 64 = 0
        rw [← hm.qn, VG.Proof.Bignum.X86_64.wv_mod64 _ _ _ (by decide)]; exact hm.qinv)
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hmP; exact hmQ])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hPo; exact hQo])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact Nat.mod_lt _ (by omega); exact Nat.mod_lt _ (by omega)])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hXp; exact hXq])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hYp; exact hYq])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [show Yp < 2 * P; show 1 < 2 * Q] <;> omega)
    (fun hK p hp => by rcases h01 p hp with rfl | rfl <;> [exact vxp hK; exact vxq hK])
    (fun hK p hp => by rcases h01 p hp with rfl | rfl <;> [exact vyp hK; exact vyq hK])
    (fun hK p hp => by
      rcases h01 p hp with rfl | rfl
      · show 2 ^ 32 * Yp % P % P = 2 ^ 32 * 2 ^ (64 * wp) % P
        rw [Nat.mod_mod, Nat.mul_mod, vyp hK, ← Nat.mul_mod]
      · show 2 ^ 32 * Yq % Q % Q = 2 ^ 32 * 2 ^ (64 * wp) % Q
        rw [Nat.mod_mod, Nat.mul_mod, vyq hK, ← Nat.mul_mod]))
    fun t' ⟨hy, ho, hr, hrd, hwr, hmx⟩ => ?_
  have evp : AmmSym.ev u.mem (VG.Proof.Bignum.X86_64.off B a) 0 128 = Spec.Rsa.os2ip ebp := ev_padE hLp (by rw [me]; exact rp.e)
  have evq : AmmSym.ev u.mem (VG.Proof.Bignum.X86_64.off B a) 1 128 = Spec.Rsa.os2ip ebq := ev_padE hLq (by rw [me]; exact rq.e)
  refine ⟨⟨(hy 0 (by decide)).1, fun hK => ?_⟩, ⟨(hy 1 (by decide)).1, fun hK => ?_⟩, by rw [← me]; exact ho,
    by rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), k.gpr (by decide)], by rw [hrd, k.2.1],
    by rw [hwr, k.2.2], by rw [hmx, mx], ⟨fun r hrm => ?_, by rw [hrd, k.2.1], by rw [hwr, k.2.2]⟩⟩
  · rw [← evp]; exact (hy 0 (by decide)).2 hK
  · rw [← evq]; exact (hy 1 (by decide)).2 hK
  · have hn : ∀ r', r' ∈ mmRegs → r ≠ r' := fun r' h' h => hrm (h ▸ h')
    rw [hr r (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
      (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
      (hn _ (by decide)) (hn _ (by decide)), k.gpr (fun h => hn .rbx (by decide) (List.mem_singleton.mp h))]

/-- Back to `n`'s workspace. -/
theorem leaveB_ok {u : State} {B : Addr} {Z o : Nat} (hs : VG.Proof.Bignum.X86_64.Scr u B Z) (hdi : u.gpr .rdi = VG.Proof.Bignum.X86_64.off B o)
    (hlk : VG.Proof.Bignum.X86_64.word u.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B) (ho : o + 8 * 32 ≤ Z) :
    WP isa (.block [leave]) u fun u' => u'.gpr .rdi = B ∧ u'.mem = u.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdi] u u' := by
  have hl : InRegions (u.rd ++ u.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sLink)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun u' => u'.gpr .rdi = B ∧ u'.mem = u.mem) (by
    xrun [leave, State.ea, hdr, hdi, hdrOff, hl, hlk]) rfl) fun u' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- A region's `Y` after changes below the area. -/
theorem goodY_below {m m' : Mem} {B : Addr} {a p : Nat} {M : Nat → Nat} {rs : List (Nat × Nat)}
    (g : AmmSym.Good m (VG.Proof.Bignum.X86_64.off B a) M oY p) (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ a) (hp : p < 2)
    (hz : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D ≤ 2 ^ 64) :
    AmmSym.Good m' (VG.Proof.Bignum.X86_64.off B a) M oY p ∧ AmmSym.val52 m' (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) = AmmSym.val52 m (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) := by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have hDp : VG.Impl.Rsa.X86_64.CrtIfma.D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have hl : ∀ l < 20, AmmSym.limb m' (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) l = AmmSym.limb m (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) l :=
    fun l hl => by
      have := off_lt160 hl
      have : oY = 192 := rfl
      simp only [AmmSym.limb]
      rw [word_off, word_off, hf.word_eq (fun r hr' => .inr (by have := hr r hr'; omega)) (by omega)]
  exact ⟨g.of_limbs (c := oY) hl, AmmSym.val52_of_limbs hl⟩

theorem resSh_lt (o : Nat) : ∀ r ∈ shiftRanges o resRanges, o + 8 * 32 ≤ r.1 ∧ r.1 + r.2 ≤ o + VG.Proof.Bignum.X86_64.slot 16 8 := by
  have hs : ∀ j, VG.Proof.Bignum.X86_64.slot 16 j = 256 + j * 144 := fun j => by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  simp only [shiftRanges, resRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, hs,
    Public.aAcc, Public.aTmp, Public.aY]
  rintro _ (rfl | rfl | rfl) <;> simp only <;> omega

theorem resSh_ifmaR (op oq a : Nat) {o : Nat} (ho : o = op ∨ o = oq) :
    ∀ r ∈ shiftRanges o resRanges, r ∈ VG.Proof.Bignum.X86_64.ifmaR op oq a := fun r hr => by
  simp only [VG.Proof.Bignum.X86_64.ifmaR, shiftRanges, List.map_append, List.mem_append] at hr ⊢
  rcases ho with rfl | rfl
  · exact .inl (.inl (.inr hr))
  · exact .inl (.inr (.inr hr))

/-- The results, from `q`'s workspace: `aY := Y mod X` in both, then back to `n`'s. -/
theorem resI_ok {t : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off B oq)
    (hm : VG.Proof.Bignum.X86_64.IMem t.mem B w op oq a minv mp mq mk P Q ep eq lp lq) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op)
    (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq) (hqa : oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z)
    (gp : AmmSym.Good t.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Proof.Bignum.X86_64.two P Q) oY 0) (gq : AmmSym.Good t.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Proof.Bignum.X86_64.two P Q) oY 1) :
    WP isa (seqs (CrtIfma.result 1 ++ (([.block [leave, enterP]] : List (Prog isa)) ++
      (CrtIfma.result 0 ++ ([.block [leave]] : List (Prog isa)))))) t fun t' =>
      VG.Proof.Bignum.X86_64.IMem t'.mem B w op oq a minv mp mq mk P Q ep eq lp lq ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 = AmmSym.val52 t.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1 + oY) % Q ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 = AmmSym.val52 t.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 0 + oY) % P ∧
      Frm B (VG.Proof.Bignum.X86_64.ifmaR op oq a) t.mem t'.mem ∧ t'.gpr .rdi = B ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      VG.Proof.MlKem.X86_64.Keep (mmRegs ++ ([.rdi] : List Reg)) t t' := by
  have hn := hs.nowrap
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have lY := slot_le (w := 16) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot 16 Public.aY (show 31 < 32 by decide)
  -- `q`'s result.
  refine wp_seqs_append (by simp [CrtIfma.result]) (by simp) (WP.mono (result_ok (p := 1) hs hdi hm.qws.hdr hm.qia
    (by omega) haZ (by decide) hm.qn gq.lt gq.v) fun t₁ ⟨vq, f₁, d₁, k₁⟩ => ?_)
  have m₁ := hm.of_frm (f₁.mono (VG.Proof.Bignum.X86_64.resSh_ifmaR op oq a (.inr rfl))) hlo hpq hqa (by omega)
  have hs₁ := hs.congr k₁.2.2
  -- To `p`'s workspace.
  refine wp_seqs_append (by simp) (by simp [CrtIfma.result]) (WP.mono (VG.Proof.Bignum.X86_64.swapWs_ok (o' := op) hs₁ (d₁.trans hdi)
    m₁.qws.link m₁.wsP (by decide) (by omega)) fun t₂ ⟨d₂, me₂, k₂⟩ => ?_)
  rw [← me₂] at m₁ vq
  have gp₂ := VG.Proof.Bignum.X86_64.goodY_below gp (show Frm B _ t.mem t₂.mem by rw [me₂]; exact f₁) (fun r hr => by have := VG.Proof.Bignum.X86_64.resSh_lt oq r hr; omega)
    (by decide) (by omega)
  have hs₂ := hs₁.congr k₂.2.2
  -- `p`'s result.
  refine wp_seqs_append (by simp [CrtIfma.result]) (by simp) (WP.mono (result_ok (p := 0) hs₂ d₂ m₁.pws.hdr m₁.pia
    (by omega) haZ (by decide) m₁.pn gp₂.1.lt gp₂.1.v) fun t₃ ⟨vp, f₃, d₃, k₃⟩ => ?_)
  have m₃ := m₁.of_frm (f₃.mono (VG.Proof.Bignum.X86_64.resSh_ifmaR op oq a (.inl rfl))) hlo hpq hqa (by omega)
  -- Back to `n`'s workspace.
  refine WP.mono (VG.Proof.Bignum.X86_64.leaveB_ok (hs₂.congr k₃.2.2) (d₃.trans d₂) m₃.pws.link (by omega)) fun t' ⟨d₄, me₄, k₄⟩ => ?_
  rw [← me₄] at m₃ vp
  refine ⟨m₃, ?_, by rw [vp, gp₂.2], ?_, d₄, ?_, ?_, ?_⟩
  · rw [← vq, me₄, wv_off, wv_off, f₃.wv_eq (fun r hr => .inr (by have := VG.Proof.Bignum.X86_64.resSh_lt op r hr; omega)) (by omega)]
  · rw [me₄]
    exact ((f₁.mono (VG.Proof.Bignum.X86_64.resSh_ifmaR op oq a (.inr rfl))).trans (show Frm B _ t₁.mem t₃.mem by rw [← me₂]; exact f₃.mono (VG.Proof.Bignum.X86_64.resSh_ifmaR op oq a (.inl rfl))))
  · rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [k₄.2.2, k₃.2.2, k₂.2.2, k₁.2.2]
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp [mmRegs])

/-! ## `ifma` -/

theorem ifma_eq : CrtIfma.ifma = (([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (CrtIfma.region 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ CrtIfma.region 1 sDq sQlen))) ++
    (([.block [.mov .rbx (.mem (hdr sIfma))], CrtIfma.vec] : List (Prog isa)) ++
      (CrtIfma.result 1 ++ (([.block [leave, enterP]] : List (Prog isa)) ++
        (CrtIfma.result 0 ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [CrtIfma.ifma, List.append_assoc, List.cons_append, List.nil_append]

theorem ifmaA_mx : (seqs ((([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (CrtIfma.region 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ CrtIfma.region 1 sDq sQlen))))).allInstrs
      (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem resI_mx : (seqs (CrtIfma.result 1 ++ (([.block [leave, enterP]] : List (Prog isa)) ++
      (CrtIfma.result 0 ++ ([.block [leave]] : List (Prog isa)))))).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

/-- `ifma`: `q`'s result `C^dq mod q` in its `aY`, `p`'s `C^dp R_p` in its. -/
theorem ifma_ok {s : State} {B : Addr} {Z w op oq a wp : Nat} {minv mp mq mk : BitVec 64} {P Q C : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} {K : Prop} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : VG.Proof.Bignum.X86_64.IPre s.mem B w op oq minv mp mq mk P Q ep eq ebp.length ebq.length) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op)
    (hpq : op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ oq) (ha : a = oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z)
    (hwp : wp = 16) (hPo : P % 2 = 1) (hQo : Q % 2 = 1)
    (hYp : wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < P) (hYq : wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < Q)
    (hXp : wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 < P) (hXq : wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 < Q)
    (vxp : K → wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 % P = C * 2 ^ (64 * wp) % P)
    (vxq : K → wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 % Q = C * 2 ^ (64 * wp) % Q)
    (vyp : K → wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 % P = 2 ^ (64 * wp) % P)
    (vyq : K → wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 % Q = 2 ^ (64 * wp) % Q)
    (hep : Src s B Z ep ebp) (heq : Src s B Z eq ebq) (hLp1 : 1 ≤ ebp.length) (hLp2 : ebp.length ≤ 128)
    (hLq1 : 1 ≤ ebq.length) (hLq2 : ebq.length ≤ 128) :
    WP isa (seqs CrtIfma.ifma) s fun t =>
      VG.Proof.Bignum.X86_64.IMem t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < Q ∧
      (K → wv t.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 = C ^ Spec.Rsa.os2ip ebq % Q) ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < P ∧
      (K → wv t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 % P = C ^ Spec.Rsa.os2ip ebp * 2 ^ (64 * wp) % P) ∧
      Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ VG.Proof.Bignum.X86_64.ifmaR op oq a) s.mem t.mem ∧ t.gpr .rdi = B ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s t ∧ t.mxcsr = s.mxcsr &&& 0xFFFF := by
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  rw [VG.Proof.Bignum.X86_64.ifma_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono_mx VG.Proof.Bignum.X86_64.ifmaA_mx (VG.Proof.Bignum.X86_64.ifmaA_ok hs hdi h hlo hpq ha haZ hYp hYq hep heq
    hLp1 hLp2 hLq1 hLq2) fun u ⟨mu, rp, rq, fu, wu, rdu, du, ku⟩ mxu => ?_)
  refine wp_seqs_append (by simp) (by simp [CrtIfma.result]) (WP.mono (VG.Proof.Bignum.X86_64.vecI_ok (K := K) (hs.congr wu) du mu haZ
    (by omega) rp rq hwp hPo hQo hYp hYq hXp hXq vxp vxq vyp vyq hLp2 hLq2)
    fun v ⟨⟨gp, vp⟩, ⟨gq, vq⟩, ov, dv, rdv, wrv, mxv, kv⟩ => ?_)
  have fv : Frm B (VG.Proof.Bignum.X86_64.ifmaR op oq a) u.mem v.mem :=
    (Frm.of_outside_off ov (by have := hs.nowrap; omega) (by have := hs.nowrap; omega)).widen fun r hr =>
      ⟨(a, 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8), List.mem_append_right _ (List.mem_singleton_self _),
        by rw [List.mem_singleton.mp hr]; simp only; omega⟩
  have mv := mu.of_frm fv hlo hpq (by omega) (by have := hs.nowrap; omega)
  refine WP.mono_mx VG.Proof.Bignum.X86_64.resI_mx (VG.Proof.Bignum.X86_64.resI_ok ((hs.congr wu).congr wrv) (dv.trans du) mv hlo hpq (by omega) haZ gp gq)
    fun t ⟨mt, vqt, vpt, ft, dt, rdt, wrt, kt⟩ mxt => ?_
  have hQ0 : 0 < Q := by omega
  have hP0 : 0 < P := by omega
  refine ⟨mt, by rw [vqt]; exact Nat.mod_lt _ hQ0, fun hK => by rw [vqt, vq hK, Nat.mul_one],
    by rw [vpt]; exact Nat.mod_lt _ hP0,
    fun hK => by rw [vpt, Nat.mod_mod, vp hK, Nat.mul_mod, vyp hK, ← Nat.mul_mod],
    (fu.trans (fv.mono fun r hr => List.mem_append_right _ hr)).trans (ft.mono fun r hr => List.mem_append_right _ hr),
    dt, ⟨fun r hr => ?_, by rw [rdt, rdv, rdu], by rw [wrt, wrv, wu]⟩, by rw [mxt, mxv, mxu]⟩
  by_cases hrd : r = .rdi
  · subst hrd; rw [dt, hdi]
  · have hr' : r ∉ mmRegs ++ ([.rdi] : List Reg) := fun h =>
      (List.mem_append.mp h).elim hr fun h' => hrd (List.mem_singleton.mp h')
    rw [kt.gpr hr', kv.gpr hr, ku.gpr hr']

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTRegion`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: constant time, a prime's region

`region p` is `k1` (a copy and `doubles`, in the prime's workspace, whose
`-p⁻¹` is secret: `doublesW_ct`), then blocks that convert arrays into the
vector layout and store `k₀`, zeros, the last multiplier and the exponent.
Those blocks read pointers from the headers and `n`'s slots (`TCtx`), which
are the same in two runs with the same public data: each block is checked
by the taint analysis after its loads (`ct_split`), whose results
correctness gives. `region_ct`: `region p` is constant time for
`region_ok`'s hypotheses (`RegPre`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-! ## Helpers -/

/-- A block whose first instructions load what the rest's addresses need. -/
theorem ct_split {α : Type} {Φ Ψ : α → State → Prop} (l₁ l₂ : List Instr) (rs₁ rs₂ : List Reg)
    (hp₁ : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₁ : (taint.check (Taint.ofRegs rs₁) (.block l₁) hc₁).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block l₁) s (Ψ a)) (hp₂ : Pins Ψ rs₂) {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₂ : (taint.check (Taint.ofRegs rs₂) (.block l₂) hc₂).isSome = true) :
    RelCT isa (Two Φ) (.block (l₁ ++ l₂)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece rs₁ hp₁ h₁ hw) (two_taint rs₂ hp₂ h₂))

/-- Pins from equalities to functions of the public data. -/
theorem pins_eqs {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs := VG.Proof.Bignum.X86_64.pins_of f h

/-! ## `doubles` in a prime's workspace -/

/-- `double` leaks the same in runs with the same working space (whatever `-m⁻¹`). -/
theorem doubleW_ct {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Proof.Bignum.X86_64.dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := fun (L : Ws) t => VG.Proof.Bignum.X86_64.DblHeadL mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩ t) _ pins_goodW h
      fun L s ⟨minv, hg, hZ⟩ => VG.Proof.Bignum.X86_64.dblHead_ok (L := ⟨L.B, L.Z, L.w, minv⟩) ⟨hg, hZ⟩ hmo hacc htmp ho)
    (two_taint _ (fun L s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_dblHead mo acc tmp o _ s₁ s₂ h₁ h₂) (by taint_decide))

/-- What `doubles` keeps after `j` doublings, for some `-m⁻¹`. -/
def DblsAtW (mo acc tmp o sl : Nat) (p : Ws × Nat) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (minv : BitVec 64) (O N : Nat), DblsInv σ p.1.B p.1.Z p.1.w minv mo acc tmp o sl p.2 O N j t ∧
    VG.Proof.Bignum.X86_64.slot p.1.w 8 ≤ p.1.Z ∧ 2 ≤ p.1.w ∧ p.1.w < 2 ^ 31 ∧ p.2 < 2 ^ 31 ∧ 0 < N

/-- What `doubles` needs: the working space, the count in `rcx`, and `[o] < [mo]`. -/
def DblPreW (mo o : Nat) (p : Ws × Nat) (s : State) : Prop :=
  GoodW p.1 s ∧ 2 ≤ p.1.w ∧ p.1.w < 2 ^ 31 ∧ 1 ≤ p.2 ∧ p.2 < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.2 ∧
    wv s.mem p.1.B (VG.Proof.Bignum.X86_64.slot p.1.w o) p.1.w < wv s.mem p.1.B (VG.Proof.Bignum.X86_64.slot p.1.w mo) p.1.w

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doublesW_ct {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Proof.Bignum.X86_64.dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.DblPreW mo o)) (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.2 ∧ VG.Proof.Bignum.X86_64.DblsAtW mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_goodW p.1 s₁ s₂ h₁.1 h₂.1) h' ?_) ?_
  · rintro p s ⟨⟨minv, hg, hZ⟩, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.scr hg.rdi hg.hdr hZ hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, minv, _, _, hI, hZ, hw, hw', hc', by omega⟩
  refine (two_loop (Φ := VG.Proof.Bignum.X86_64.DblsAtW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.2) ?_ ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : (Ws × Nat) × Nat) s => GoodW q.1.1 s)
      (two_map (·.1.1) (fun _ _ h => ?_) (VG.Proof.Bignum.X86_64.doubleW_ct hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1.1 s₁ s₂ h₁ h₂) h'')
    · obtain ⟨_, σ, minv, O, N, hI, hZ, _⟩ := h
      exact ⟨minv, ⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩
    rintro ⟨p, j⟩ s ⟨hj, σ, minv, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨minv, ⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, minv, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨VG.Proof.Bignum.X86_64.eval_ne_count hj hz, fun _ => ⟨σ, minv, O, N, hI', hZ, hw, hw', hc', hN0⟩,
        fun _ => trivial⟩

/-! ## The region's public data and what its blocks read -/

/-- The public data of a region: `n`'s workspace `B` (of `Z` bytes), the
prime's at `off B o`, the area at `off B a`, `n`'s slots of the exponent's
pointer `ep` and length `L`. -/
structure RegPub where
  B : Addr
  Z : Nat
  o : Nat
  a : Nat
  ep : Addr
  L : Nat

/-- The prime's workspace. -/
abbrev RegPub.pw (q : VG.Proof.Bignum.X86_64.RegPub) : Ws := ⟨VG.Proof.Bignum.X86_64.off q.B q.o, VG.Proof.Bignum.X86_64.slot 16 8, 16⟩

/-- The layout of region `p`. -/
def RegPub.Ok (q : VG.Proof.Bignum.X86_64.RegPub) (p sp sl : Nat) : Prop :=
  q.o + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ q.a ∧ q.a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ q.Z ∧ p < 2 ∧ sp < 32 ∧ sl < 32 ∧ 1 ≤ q.L ∧ q.L ≤ 128

/-- What the region's blocks read (`TCtx`). -/
def RT (p sp sl : Nat) (q : VG.Proof.Bignum.X86_64.RegPub) (s : State) : Prop :=
  q.Ok p sp sl ∧ ∃ (mx : BitVec 64) (eb : List Byte), TCtx s q.B q.Z q.o q.a mx sp sl q.ep eb ∧ eb.length = q.L

theorem RT.of_frm {p sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s t : State} (h : VG.Proof.Bignum.X86_64.RT p sp sl q s) {rs : List (Nat × Nat)}
    (hf : Frm q.B rs s.mem t.mem) (hr : ∀ r ∈ rs, q.a ≤ r.1 ∧ r.1 + r.2 ≤ q.Z)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp, .rsi, .r11, .r12] s t) : VG.Proof.Bignum.X86_64.RT p sp sl q t := by
  obtain ⟨ok, mx, eb, c, hl⟩ := h
  have hok := ok
  obtain ⟨hoa, haZ, _, hsp, hsl, _⟩ := ok
  exact ⟨hok, mx, eb, c.of_frm hf hr hoa (by omega) hsp hsl k, hl⟩

theorem RT.rdi {p sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s : State} (h : VG.Proof.Bignum.X86_64.RT p sp sl q s) : s.gpr .rdi = VG.Proof.Bignum.X86_64.off q.B q.o :=
  let ⟨_, _, _, c, _⟩ := h; c.rdi

theorem pins_rt {p sp sl : Nat} {Φ : VG.Proof.Bignum.X86_64.RegPub → State → Prop} (h : ∀ q s, Φ q s → VG.Proof.Bignum.X86_64.RT p sp sl q s) : Pins Φ [.rdi] :=
  VG.Proof.Bignum.X86_64.pins_eqs (fun q _ => VG.Proof.Bignum.X86_64.off q.B q.o) fun q s hs r hr => by
    rw [List.mem_singleton.mp hr]; exact (h q s hs).rdi

theorem ofs_bound {p : Nat} (hp : p < 2) : VG.Impl.Rsa.X86_64.CrtIfma.D * p ≤ 3712 := by
  have : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  rcases AmmSym.D_mul hp with h | h <;> omega

/-! ## The blocks -/

theorem arr52_eq (p j c : Nat) : CrtIfma.arr52 p j c =
    ([.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma))] : List Instr) ++
      (([.alu .add .r11 (.imm (BitVec.ofNat 32 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + c))), .movImm64 .r12 mask52] : List Instr) ++
        CrtIfma.to52) := rfl

/-- `arr52`'s loads: the array's and the area's addresses. -/
theorem arrLd_ok {p j sp sl : Nat} (hj : j < 8) {q : VG.Proof.Bignum.X86_64.RegPub} {s : State} (h : VG.Proof.Bignum.X86_64.RT p sp sl q s) :
    WP isa (.block [.mov .rsi (.mem (hdr (sArr j))), .mov .r11 (.mem (hdr sIfma))]) s fun t =>
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 j) ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off q.B q.a := by
  obtain ⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hH : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact c.scr.ld (by have := hdr_lt_slot 16 8 hi; omega)
  refine WP.mono (WP.keep [.rsi, .r11] (Q := fun t => t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 j) ∧
    t.gpr .r11 = VG.Proof.Bignum.X86_64.off q.B q.a) (by
      xrun [State.ea, hdr, c.rdi, hdrOff, hH _ (show sArr j < 32 by unfold sArr; omega), hH sIfma (by decide)]
      exact ⟨c.hdr.harr j hj, c.ia⟩) rfl) fun t h => h.1

theorem arr52_rt {p j c sp sl : Nat} (hc : c + 160 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D) (hj : j < 8) {q : VG.Proof.Bignum.X86_64.RegPub} {s : State} (h : VG.Proof.Bignum.X86_64.RT p sp sl q s) :
    WP isa (.block (CrtIfma.arr52 p j c)) s fun t => VG.Proof.Bignum.X86_64.RT p sp sl q t ∧ t.gpr .r12 = mask52 := by
  have hRT := h
  obtain ⟨⟨hoa, haZ, hp, -⟩, mx, eb, c', -⟩ := h
  have := VG.Proof.Bignum.X86_64.ofs_bound hp
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  exact WP.mono (arr52r_ok c'.scr c'.rdi c'.hdr c'.ia hoa haZ hp hc hj) fun t ⟨_, f, k, h12, _⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k, h12⟩

/-- `arr52` is constant time, given that the taint analysis checks the rest after its loads. -/
theorem arr52_ct {p j c sp sl : Nat} (hj : j < 8) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block ([.mov .rsi (.mem (hdr (sArr j))),
      .mov .r11 (.mem (hdr sIfma))] : List Instr)) hc₁).isSome = true) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rsi, .r11]) (.block (([.alu .add .r11 (.imm (BitVec.ofNat 32 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + c))),
      .movImm64 .r12 mask52] : List Instr) ++ CrtIfma.to52)) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RT p sp sl)) (.block (CrtIfma.arr52 p j c)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.arr52_eq]
  exact VG.Proof.Bignum.X86_64.ct_split _ _ [.rdi] [.rsi, .r11] (VG.Proof.Bignum.X86_64.pins_rt fun _ _ h => h) hT₁
    (fun _ _ h => VG.Proof.Bignum.X86_64.arrLd_ok hj h)
    (VG.Proof.Bignum.X86_64.pins_eqs (fun q r => if r = .rsi then VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 j) else VG.Proof.Bignum.X86_64.off q.B q.a) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT

theorem k0St_eq (p : Nat) : CrtIfma.k0St p = ([.mov .r11 (.mem (hdr sIfma))] : List Instr) ++
    (([.alu .add .r11 (.imm (BitVec.ofNat 32 (VG.Impl.Rsa.X86_64.CrtIfma.D * p))), .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] :
      List Instr) ++ (List.range 4).map (fun l => .store (CrtIfma.at_ .r11 (oK0 + 8 * l)) .rax)) := rfl

theorem k0St_rt {p sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s : State} (h : VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r12 = mask52) :
    WP isa (.block (CrtIfma.k0St p)) s fun t => VG.Proof.Bignum.X86_64.RT p sp sl q t ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p) := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h12⟩ := h
  have := VG.Proof.Bignum.X86_64.ofs_bound hp
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  exact WP.mono (k0r_ok c.scr c.rdi c.hdr c.ia hoa haZ hp h12) fun t ⟨_, f, r11, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [oK0]; omega) (k.mono (by simp)), r11⟩

theorem k0St_ct (p : Nat) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .r11]) (.block (([.alu .add .r11 (.imm (BitVec.ofNat 32 (VG.Impl.Rsa.X86_64.CrtIfma.D * p))),
      .mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
      (List.range 4).map (fun l => .store (CrtIfma.at_ .r11 (oK0 + 8 * l)) .rax))) hc).isSome = true) :
    RelCT isa (Two fun q s => VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r12 = mask52) (.block (CrtIfma.k0St p)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.k0St_eq]
  refine VG.Proof.Bignum.X86_64.ct_split (Ψ := fun q t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off q.B q.o ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off q.B q.a) _ _ [.rdi] [.rdi, .r11]
    (VG.Proof.Bignum.X86_64.pins_rt fun _ _ h => h.1) (by taint_decide) (fun q s h => ?_)
    (VG.Proof.Bignum.X86_64.pins_eqs (fun q r => if r = .rdi then VG.Proof.Bignum.X86_64.off q.B q.o else VG.Proof.Bignum.X86_64.off q.B q.a) fun q s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) hT
  obtain ⟨⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩, -⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT' : tabBytes 16 = 2304 := rfl
  have hH : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sIfma)) 8 := by
    rw [off_off]; exact c.scr.ld (by unfold sIfma sFn; omega)
  exact WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = VG.Proof.Bignum.X86_64.off q.B q.a) (by
    xrun [State.ea, hdr, c.rdi, hdrOff, hH]; exact c.ia) rfl) fun t ⟨h11, k⟩ =>
      ⟨(k.gpr (by decide)).trans c.rdi, h11⟩

theorem eZero_rt {p sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s : State} (h : VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) :
    WP isa (.block CrtIfma.eZero) s fun t =>
      VG.Proof.Bignum.X86_64.RT p sp sl q t ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p) ∧ t.gpr .rax = 0 := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h11⟩ := h
  have := VG.Proof.Bignum.X86_64.ofs_bound hp
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  exact WP.mono (eZr_ok c.scr haZ hp h11) fun t ⟨_, f, ra, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [oE]; omega) (k.mono (by simp)),
      (k.gpr (by decide)).trans h11, ra⟩

theorem eZero_ct (p : Nat) {sp sl : Nat} :
    RelCT isa (Two fun q s => VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) (.block CrtIfma.eZero)
      fun _ _ => True :=
  two_taint [.r11] (VG.Proof.Bignum.X86_64.pins_eqs (fun q _ => VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p))
    fun q s (h : VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2) (by taint_decide)

theorem finOne_rt {sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s : State}
    (h : VG.Proof.Bignum.X86_64.RT 1 sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1) ∧ s.gpr .rax = 0) :
    WP isa (.block CrtIfma.finOne) s fun t => VG.Proof.Bignum.X86_64.RT 1 sp sl q t ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1) := by
  have hRT := h.1
  obtain ⟨⟨⟨hoa, haZ, hp, -⟩, mx, eb, c, -⟩, h11, ha⟩ := h
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  exact WP.mono (finr_ok c.scr haZ h11 ha) fun t ⟨_, f, k⟩ =>
    ⟨hRT.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [oFin]; omega) (k.mono (by simp)),
      (k.gpr (by decide)).trans h11⟩

theorem finOne_ct {sp sl : Nat} :
    RelCT isa (Two fun q s => VG.Proof.Bignum.X86_64.RT 1 sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1) ∧ s.gpr .rax = 0)
      (.block CrtIfma.finOne) fun _ _ => True :=
  two_taint [.r11] (VG.Proof.Bignum.X86_64.pins_eqs (fun q _ => VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1))
    fun q s (h : VG.Proof.Bignum.X86_64.RT 1 sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * 1) ∧ s.gpr .rax = 0) r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2.1) (by taint_decide)

/-! ## The exponent's copy -/

/-- After `eCopy`'s first block: the pointer, the length and the destination. -/
def ECp (p : Nat) (q : VG.Proof.Bignum.X86_64.RegPub) (t : State) : Prop :=
  t.gpr .rsi = q.ep ∧ t.gpr .rcx = BitVec.ofNat 64 q.L ∧
    t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) (oE + 128 - q.L)

theorem eBlk_ok {p sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s : State}
    (h : VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) :
    WP isa (.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sp)), .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sl)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (oE + 128))), .alu .sub .r11 (.reg .rcx)]) s (VG.Proof.Bignum.X86_64.ECp p q) := by
  obtain ⟨⟨⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩, mx, eb, c, hl⟩, h11⟩ := h
  have hn := c.scr.nowrap
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hlk : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sLink)) 8 := by
    rw [off_off]; exact c.scr.ld (by unfold sLink sFn; omega)
  have hlv₁ : s.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sLink)) 64 = q.B := c.lk
  have hp' : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off q.B (8 * sp)) 8 := c.scr.ld (by omega)
  have hl' : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off q.B (8 * sl)) 8 := c.scr.ld (by omega)
  have hlv' : VG.Proof.Bignum.X86_64.word s.mem q.B (8 * sl) = BitVec.ofNat 64 q.L := by rw [← hl]; exact c.lv
  refine WP.mono (WP.keep [.rax, .rcx, .rsi, .r11] (Q := fun t => t.gpr .rsi = q.ep ∧
    t.gpr .rcx = BitVec.ofNat 64 q.L ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) (oE + 128 - q.L)) (by
    xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, c.rdi, hdrOff, hlk, hlv₁, hp', hl',
      AmmSym.se_ofNat (show oE + 128 < 2 ^ 31 by simp only [oE]; omega)]
    and_intros
    · exact c.pv
    · exact hlv'
    rw [show s.mem.readW (VG.Proof.Bignum.X86_64.off q.B (8 * sl)) 64 = BitVec.ofNat 64 q.L from hlv', h11,
      VG.Offset.add_ofNat_sub _ (by simp only [oE]; omega)]) rfl) fun t h => h.1

/-- `eCopy` is constant time, given that the taint analysis checks its loads
from `n`'s workspace. -/
theorem eCopy_ct {p sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sp)),
      .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two fun q s => VG.Proof.Bignum.X86_64.RT p sp sl q s ∧ s.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p))
      (seqs (CrtIfma.eCopy sp sl)) fun _ _ => True := by
  show RelCT isa _ (.seq (.block (([.mov .rax (.mem (hdr sLink))] : List Instr) ++
    (([.mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sp)), .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sl))] : List Instr) ++
      ([.alu .add .r11 (.imm (BitVec.ofNat 32 (oE + 128))), .alu .sub .r11 (.reg .rcx)] : List Instr)))) _) _
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.ECp p) ?_ fun q s h => VG.Proof.Bignum.X86_64.eBlk_ok h)
    (two_taint [.rsi, .rcx, .r11] (VG.Proof.Bignum.X86_64.pins_eqs (fun q r => if r = .rsi then q.ep else if r = .rcx then
      BitVec.ofNat 64 q.L else VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) (oE + 128 - q.L)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => (VG.Proof.Bignum.X86_64.RT p sp sl q t ∧
      t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) ∧ t.gpr .rax = q.B) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_rt fun _ _ h => h.1) (by taint_decide) ?_) (RelCT.block_append (RelCT.seq (two_piece
      (Ψ := fun q t => t.gpr .rcx = BitVec.ofNat 64 q.L ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) [.rax]
      (VG.Proof.Bignum.X86_64.pins_eqs (fun q _ => q.B) fun q s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2) hT ?_)
    (two_taint [.rcx, .r11] (VG.Proof.Bignum.X86_64.pins_eqs (fun q r => if r = .rcx then BitVec.ofNat 64 q.L else
      VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide)))))
  · rintro q s ⟨hRT, h11⟩
    have hRT' := hRT
    obtain ⟨⟨hoa, haZ, -⟩, mx, eb, c, -⟩ := hRT'
    have hn := c.scr.nowrap
    have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hT' : tabBytes 16 = 2304 := rfl
    have hlk : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sLink)) 8 := by
      rw [off_off]; exact c.scr.ld (by unfold sLink sFn; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = q.B ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, c.rdi, hdrOff, hlk]; exact c.lk) rfl) fun t ⟨⟨ha, hm⟩, k⟩ =>
        ⟨⟨hRT.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (k.mono (by simp)),
          (k.gpr (by decide)).trans h11⟩, ha⟩
  · rintro q s ⟨⟨hRT, h11⟩, ha⟩
    obtain ⟨⟨hoa, haZ, hp, hsp, hsl, -⟩, mx, eb, c, hl⟩ := hRT
    have hn := c.scr.nowrap
    have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hp' : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off q.B (8 * sp)) 8 := c.scr.ld (by omega)
    have hl' : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off q.B (8 * sl)) 8 := c.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 q.L) (by
      xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, ha, hdrOff, hp', hl']; rw [← hl]; exact c.lv) rfl) fun t ⟨hcx, k⟩ =>
        ⟨hcx, (k.gpr (by decide)).trans h11⟩

/-! ## `k1`, and the region -/

/-- `region_ok`'s hypotheses. -/
def RegPre (p sp sl : Nat) (q : VG.Proof.Bignum.X86_64.RegPub) (s : State) : Prop :=
  q.Ok p sp sl ∧ ∃ (w : Nat) (mx : BitVec 64) (X : Nat) (eb : List Byte), SubCtx s q.B q.Z q.o w 16 mx ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sIfma) = VG.Proof.Bignum.X86_64.off q.B q.a ∧ wv s.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16 = X ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < X ∧ VG.Proof.Bignum.X86_64.word s.mem q.B (8 * sp) = q.ep ∧
    VG.Proof.Bignum.X86_64.word s.mem q.B (8 * sl) = BitVec.ofNat 64 eb.length ∧ Src s q.B q.Z q.ep eb ∧ eb.length = q.L

/-- Before `doubles`. -/
def K2 (p sp sl : Nat) (q : VG.Proof.Bignum.X86_64.RegPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.DblPreW Public.aN aT (q.pw, 32) s ∧
    WP isa (doubles Public.aN Public.aAcc Public.aTmp aT CrtIfma.sCtr) s (VG.Proof.Bignum.X86_64.RT p sp sl q)

/-- Before `doubles`' count. -/
def K1 (p sp sl : Nat) (q : VG.Proof.Bignum.X86_64.RegPub) (s : State) : Prop :=
  s.gpr .rdi = VG.Proof.Bignum.X86_64.off q.B q.o ∧ WP isa (.block [.mov32 .rcx (.imm 32)]) s (VG.Proof.Bignum.X86_64.K2 p sp sl q)

/-- Before `k1`. -/
def K0 (p sp sl : Nat) (q : VG.Proof.Bignum.X86_64.RegPub) (s : State) : Prop :=
  GoodW q.pw s ∧ WP isa (seqs (copyArr aT Public.aY)) s (VG.Proof.Bignum.X86_64.K1 p sp sl q)

/-- `region_ok`'s hypotheses give `K0`, as `k1_ok` runs `k1`. -/
theorem k1_chain {p sp sl : Nat} {q : VG.Proof.Bignum.X86_64.RegPub} {s : State} (h : VG.Proof.Bignum.X86_64.RegPre p sp sl q s) : VG.Proof.Bignum.X86_64.K0 p sp sl q s := by
  obtain ⟨ok, w, mx, X, eb, hc, hia, hN, hY, hpv, hlv, he, hl⟩ := h
  have hok := ok
  obtain ⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩ := ok
  have hn := hc.scr.nowrap
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hg := hc.good
  have lT := slot_le (w := 16) (show aT < 8 by decide)
  have lN := slot_le (w := 16) (show Public.aN < 8 by decide)
  have sTN := slot_sep (w := 16) (show aT ≠ Public.aN by decide)
  have hk1 : ∀ r ∈ k1Ranges 16, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot 16 8 := by
    have := slot_le (w := 16) (show Public.aAcc < 8 by decide)
    have := slot_le (w := 16) (show Public.aTmp < 8 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [CrtIfma.sCtr, sFn] <;> omega
  refine ⟨⟨mx, hg, Nat.le_refl _⟩, WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) (by omega) (o := aT)
    (a := Public.aY) (by decide) (by decide) (by decide)) fun s₁ ⟨hv₁, ho₁, k₁⟩ => ?_⟩
  have hg₁ := hg.of_outsideArr ho₁ k₁
  have hN₁ : wv s₁.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16 = X := by rw [ho₁.wv (by omega) (by omega)]; exact hN
  refine ⟨hg₁.rdi, WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 32 ∧ t.mem = s₁.mem) (by
    xrun; and_intros) rfl) fun s₂ ⟨⟨cx₂, me₂⟩, k₂⟩ => ?_⟩
  have hg₂ : Good s₂ (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 8) 16 mx :=
    ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [me₂]; exact hg₁.hdr⟩
  refine ⟨⟨⟨mx, hg₂, Nat.le_refl _⟩, show 2 ≤ 16 by decide, show 16 < 2 ^ 31 by decide, show 1 ≤ 32 by decide,
    show 32 < 2 ^ 31 by decide, cx₂,
    by rw [me₂, hv₁, hN₁]; exact hY⟩, ?_⟩
  refine WP.mono (doubles_ok hg₂.scr hg₂.rdi hg₂.hdr (Nat.le_refl _) (by decide) (by decide) (mo := Public.aN)
    (acc := Public.aAcc) (tmp := Public.aTmp) (o := aT) (sl := CrtIfma.sCtr) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (c := 32) (by decide) (by decide) cx₂ (by rw [me₂, hv₁, hN₁]; exact hY)) fun t ⟨_, hf, hH, k⟩ => ?_
  have fW : Frm (VG.Proof.Bignum.X86_64.off q.B q.o) (k1Ranges 16) s.mem t.mem :=
    (Frm.of_outside (ho₁.mono (o' := VG.Proof.Bignum.X86_64.slot 16 aT) (n' := 8 * (16 + 2)) (Nat.le_refl _) (by omega))
      (by simp [k1Ranges])).trans (by rw [← me₂]; exact hf)
  have fB : Frm q.B (shiftRanges q.o (k1Ranges 16)) s.mem t.mem :=
    fW.rebase (by omega) fun r hr => by have := hk1 r hr; omega
  have kk := (k₁.trans k₂).trans k
  have hia' : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sIfma) = VG.Proof.Bignum.X86_64.off q.B q.a := by
    rw [fW.word_eq (fun r hr => by
      have := hdr_lt_slot 16 Public.aAcc (show sIfma < 32 by decide)
      have := hdr_lt_slot 16 Public.aTmp (show sIfma < 32 by decide)
      have := hdr_lt_slot 16 aT (show sIfma < 32 by decide)
      simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [CrtIfma.sCtr, sIfma, sFn] at * <;> omega)
      (by unfold sIfma sFn; omega)]
    exact hia
  exact ⟨hok, mx, eb, TCtx.of_regionA hc hoa haZ hp hsp hsl hpv hlv he
    (fB.mono fun r hr => List.mem_append_left _ hr) kk.2.2 kk.2.1 ((kk.gpr (by decide)).trans hc.rdi) hH hia', hl⟩

/-- A piece, then the rest of a list. -/
theorem ct_cons {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} {cs : List (Prog isa)} (hcs : cs ≠ [])
    (hc : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hr : RelCT isa (Two Ψ) (seqs cs) fun _ _ => True) : RelCT isa (Two Φ) (seqs (c :: cs)) fun _ _ => True := by
  match cs, hcs with
  | _ :: _, _ => exact VG.Proof.Bignum.X86_64.ct_step id (fun _ _ h => h) hw hc hr

theorem k1_ct {p sp sl : Nat} {rest : List (Prog isa)} (hr0 : rest ≠ [])
    (hr : RelCT isa (Two (VG.Proof.Bignum.X86_64.RT p sp sl)) (seqs rest) fun _ _ => True) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RegPre p sp sl)) (seqs (CrtIfma.k1 ++ rest)) fun _ _ => True := by
  refine two_map id (fun _ _ h => VG.Proof.Bignum.X86_64.k1_chain h) ?_
  simp only [CrtIfma.k1, List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Bignum.X86_64.ct_steps (by simp [copyArr]) (by simp) RegPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (VG.Proof.Bignum.X86_64.copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_eqs (fun q _ => VG.Proof.Bignum.X86_64.off q.B q.o)
    fun q s (h : VG.Proof.Bignum.X86_64.K1 p sp sl q s) r hr => by rw [List.mem_singleton.mp hr]; exact h.1) (by taint_decide))
    (fun _ _ h => h.2) ?_
  exact VG.Proof.Bignum.X86_64.ct_cons hr0 (two_map (fun q : VG.Proof.Bignum.X86_64.RegPub => (q.pw, 32)) (fun _ _ h => h.1) (VG.Proof.Bignum.X86_64.doublesW_ct (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) (fun _ _ h => h.2) hr

/-- `p`'s region is constant time. -/
theorem region0_ct {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sp)),
      .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RegPre 0 sp sl)) (seqs (CrtIfma.region 0 sp sl)) fun _ _ => True := by
  rw [show CrtIfma.region 0 sp sl = CrtIfma.k1 ++ (.block (CrtIfma.arr52 0 Public.aN oM) ::
    .block (CrtIfma.arr52 0 aT oK1) :: .block (CrtIfma.arr52 0 aXc oX) :: .block (CrtIfma.arr52 0 Public.aY oY) ::
    .block (CrtIfma.arr52 0 Public.aY oFin) :: .block (CrtIfma.k0St 0) :: .block CrtIfma.eZero ::
    CrtIfma.eCopy sp sl) from rfl]
  refine VG.Proof.Bignum.X86_64.k1_ct (List.cons_ne_nil _ _) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))
    (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (VG.Proof.Bignum.X86_64.k0St_ct 0 (by taint_decide)) (fun _ _ h => VG.Proof.Bignum.X86_64.k0St_rt h) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (by simp [CrtIfma.eCopy]) (VG.Proof.Bignum.X86_64.eZero_ct 0) (fun _ _ h => VG.Proof.Bignum.X86_64.eZero_rt h) ?_
  exact two_map id (fun _ _ h => ⟨h.1, h.2.1⟩) (VG.Proof.Bignum.X86_64.eCopy_ct hT)

/-- `q`'s region is constant time. -/
theorem region1_ct {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rax]) (.block [.mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sp)),
      .mov .rcx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sl))]) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RegPre 1 sp sl)) (seqs (CrtIfma.region 1 sp sl)) fun _ _ => True := by
  rw [show CrtIfma.region 1 sp sl = CrtIfma.k1 ++ (.block (CrtIfma.arr52 1 Public.aN oM) ::
    .block (CrtIfma.arr52 1 aT oK1) :: .block (CrtIfma.arr52 1 aXc oX) :: .block (CrtIfma.arr52 1 Public.aY oY) ::
    .block (CrtIfma.k0St 1) :: .block CrtIfma.eZero :: .block CrtIfma.finOne :: CrtIfma.eCopy sp sl) from rfl]
  refine VG.Proof.Bignum.X86_64.k1_ct (List.cons_ne_nil _ _) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))
    (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (two_map id (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.arr52_ct (by decide) (by taint_decide) (by taint_decide))) (fun _ _ h => VG.Proof.Bignum.X86_64.arr52_rt (by decide) (by decide) h.1) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (VG.Proof.Bignum.X86_64.k0St_ct 1 (by taint_decide)) (fun _ _ h => VG.Proof.Bignum.X86_64.k0St_rt h) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (List.cons_ne_nil _ _) (VG.Proof.Bignum.X86_64.eZero_ct 1) (fun _ _ h => VG.Proof.Bignum.X86_64.eZero_rt h) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (by simp [CrtIfma.eCopy]) VG.Proof.Bignum.X86_64.finOne_ct (fun _ _ h => VG.Proof.Bignum.X86_64.finOne_rt h) ?_
  exact VG.Proof.Bignum.X86_64.eCopy_ct hT

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTIfma`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: constant time, `ifma`

`ifma`'s blocks read pointers from the workspaces' headers, which are the
same in two runs with the same public data; the taint analysis checks each
block after its loads, whose results correctness gives (the head block,
`head_ct`; the moves between the workspaces, `swap_ct`; the results,
`result_ct`). The vector code's addresses all come from `rbx`, the area's
base (`vecB_ct`). With the regions (`region0_ct`, `region1_ct`), `ifma` is
constant time (`ifma_ct`) for `ifma_ok`'s hypotheses.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-! ## The head block -/

/-- The public data of the head: `n`'s workspace and the primes'. -/
structure HdPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  oq : Nat

/-- `ifmaHead_ok`'s hypotheses. -/
def HdPre (p : VG.Proof.Bignum.X86_64.HdPub) (s : State) : Prop :=
  ∃ (minv mq : BitVec 64), Good s p.B p.Z p.w minv ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧ p.op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ p.oq ∧
    p.oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ p.Z ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.B p.op ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ WsAt s.mem p.B p.oq 16 mq

/-- After `q`'s base is loaded. -/
def HdA (p : VG.Proof.Bignum.X86_64.HdPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.HdPre p s ∧ t.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdx] s t

/-- After the area's base is computed and `p`'s base loaded. -/
def HdB (p : VG.Proof.Bignum.X86_64.HdPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.HdPre p s ∧ t.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B p.op ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) ∧
    t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t

/-- After the store into `p`'s workspace, and `q`'s base loaded again. -/
def HdC (p : VG.Proof.Bignum.X86_64.HdPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.HdPre p s ∧ t.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) ∧
    t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sIfma)) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16)) ∧
    VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t

theorem head_eq : (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
    ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
      .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr)) =
    ([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ ((wsEndT ++ ([.mov .rdx (.mem (hdr sWsP))] : List Instr)) ++
      (([.store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ))] : List Instr) ++
        ([.store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Pins `rdi` (`n`'s base) and `rdx` from a predicate after the head's start. -/
theorem pins_hd {Φ : VG.Proof.Bignum.X86_64.HdPub → State → Prop} (f : VG.Proof.Bignum.X86_64.HdPub → Addr)
    (h : ∀ p t, Φ p t → ∃ s, VG.Proof.Bignum.X86_64.HdPre p s ∧ t.gpr .rdx = f p ∧ t.gpr .rdi = s.gpr .rdi) :
    Pins Φ [.rdi, .rdx] :=
  VG.Proof.Bignum.X86_64.pins_eqs (fun p r => if r = .rdi then p.B else f p) fun p t h' r hr => by
    obtain ⟨s, ⟨_, _, hg, _⟩, hdx, hdi⟩ := h p t h'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hdi.trans hg.rdi
    · exact hdx

/-- The head block is constant time. -/
theorem head_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.HdPre) (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
    ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
      .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.head_eq]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.HdA) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_eqs (fun p _ => p.B) fun p s h r hr => by
      obtain ⟨_, _, hg, _⟩ := h; rw [List.mem_singleton.mp hr]; exact hg.rdi) (by taint_decide) ?_)
    (RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.HdB) [.rdi, .rdx]
      (VG.Proof.Bignum.X86_64.pins_hd (fun p => VG.Proof.Bignum.X86_64.off p.B p.oq) fun p t ⟨s, h, dx, _, k⟩ => ⟨s, h, dx, k.gpr (by decide)⟩) (by taint_decide) ?_)
      (RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.HdC) [.rdi, .rdx]
        (VG.Proof.Bignum.X86_64.pins_hd (fun p => VG.Proof.Bignum.X86_64.off p.B p.op) fun p t ⟨s, h, dx, _, _, k⟩ => ⟨s, h, dx, k.gpr (by decide)⟩)
        (by taint_decide) ?_)
        (two_taint [.rdi, .rdx] (VG.Proof.Bignum.X86_64.pins_hd (fun p => VG.Proof.Bignum.X86_64.off p.B p.oq) fun p t ⟨s, h, dx, _, _, k⟩ =>
          ⟨s, h, dx, k.gpr (by decide)⟩) (by taint_decide)))))))
  · rintro p s h
    have h' := h
    obtain ⟨minv, mq, hg, hlo, hpq, haZ, hsp, hsq, hwsq⟩ := h'
    have hn := hg.scr.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hsq]) rfl)
      fun t ⟨⟨dx, me⟩, k⟩ => ⟨s, h, dx, me, k⟩
  · rintro p t ⟨s, h, dx, me, k⟩
    have h' := h
    obtain ⟨minv, mq, hg, hlo, hpq, haZ, hsp, hsq, hwsq⟩ := h'
    have hs := hg.scr
    have hn := hs.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hT : tabBytes 16 = 2304 := rfl
    rw [WP.block_append_iff]
    refine WP.mono (wsEndT_ok (X := VG.Proof.Bignum.X86_64.off p.B p.oq) (Z := VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) (wx := 16)
      ((hs.congr k.2.2).sub (by omega) (by omega)) dx (by rw [me]; exact hwsq.hdr.hw)
      (by rw [me]; exact hwsq.hdr.harr _ (by decide)) (by omega)) fun t₂ ⟨ax₂, me₂, k₂⟩ => ?_
    have k12 := k.trans k₂
    have hdi₂ : t₂.gpr .rdi = p.B := by rw [k12.gpr (by decide)]; exact hg.rdi
    refine WP.mono (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B p.op ∧ u.mem = t₂.mem) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, (hs.congr k12.2.2).ld (d := 8 * sWsP) (by unfold sWsP sFn; omega)]
      rw [me₂, me]; exact hsp) rfl) fun u ⟨⟨dx', me'⟩, k'⟩ =>
        ⟨s, h, dx', by rw [k'.gpr (by decide)]; exact ax₂, me'.trans (me₂.trans me), (k12.trans k').mono (by simp)⟩
  · rintro p t ⟨s, h, dx, ax, me, k⟩
    have h' := h
    obtain ⟨minv, mq, hg, hlo, hpq, haZ, hsp, hsq, hwsq⟩ := h'
    have hs := hg.scr
    have hn := hs.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hT : tabBytes 16 = 2304 := rfl
    have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
    have hdi : t.gpr .rdi = p.B := by rw [k.gpr (by decide)]; exact hg.rdi
    have hst : InRegions t.wr (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sIfma)) 8 := by
      rw [k.2.2, off_off]; exact hs.st (by unfold sIfma sFn; omega)
    have hq' : (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sIfma)) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16))).readW
        (VG.Proof.Bignum.X86_64.off p.B (8 * sWsQ)) 64 = VG.Proof.Bignum.X86_64.off p.B p.oq := by
      rw [off_off]
      have := (VG.Proof.Bignum.X86_64.writeW_outside s.mem p.B (d := p.op + 8 * sIfma) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16))
        (by unfold sIfma sFn; omega)).word (d := 8 * sWsQ) (.inl (by unfold sWsQ sFn; omega))
        (by unfold sWsQ sFn; omega)
      exact this.trans hsq
    have hl : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * sWsQ)) 8 := by
      rw [k.2.1, k.2.2]; exact hs.ld (by unfold sWsQ sFn; omega)
    refine WP.mono (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = VG.Proof.Bignum.X86_64.off p.B p.oq ∧
      u.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sIfma)) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16))) (by
        xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdi, dx, ax, me, hdrOff, hst, hl, hq']) rfl) fun u ⟨⟨dx', me'⟩, k'⟩ =>
      ⟨s, h, dx', by rw [k'.gpr (by decide)]; exact ax, me', (k.trans k').mono (by simp)⟩

/-! ## Between the workspaces -/

/-- In a prime's workspace (`rdi = off B o`), linked to `n`'s. -/
def SwPre (p : Addr × Nat × Nat) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.1 p.2.2 ∧ s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.1 p.2.1 ∧ VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.1 p.2.1) (8 * sLink) = p.1 ∧
    p.2.1 + 8 * 32 ≤ p.2.2

/-- Back to `n`'s workspace, and into the one in slot `sl`: constant time. -/
theorem swap_ct (sl : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Bignum.X86_64.SwPre) (.block [leave, .mov .rdi (.mem (hdr sl))]) fun _ _ => True :=
  VG.Proof.Bignum.X86_64.ct_split [leave] [.mov .rdi (.mem (hdr sl))] [.rdi] [.rdi]
    (VG.Proof.Bignum.X86_64.pins_eqs (fun p _ => VG.Proof.Bignum.X86_64.off p.1 p.2.1) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1)
    (by taint_decide) (Ψ := fun p t => t.gpr .rdi = p.1)
    (fun p s ⟨hs, hdi, hlk, ho⟩ => WP.mono (VG.Proof.Bignum.X86_64.leaveB_ok hs hdi hlk ho) fun t h => h.1)
    (VG.Proof.Bignum.X86_64.pins_eqs (fun p _ => p.1) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h) hT

/-! ## The vector code -/

/-- In `q`'s workspace, the area's base in its header. -/
def VPre (p : Addr × Nat × Nat × Nat) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.1 p.2.1 ∧ s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.1 p.2.2.1 ∧ VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.1 p.2.2.1) (8 * sIfma) = VG.Proof.Bignum.X86_64.off p.1 p.2.2.2 ∧
    p.2.2.1 + 8 * 32 ≤ p.2.1

/-- The area's base into `rbx`, and the vector code: constant time. -/
theorem vecB_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.VPre) (seqs [.block [.mov .rbx (.mem (hdr sIfma))], CrtIfma.vec])
    fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.1 p.2.2.2) [.rdi]
    (VG.Proof.Bignum.X86_64.pins_eqs (fun p _ => VG.Proof.Bignum.X86_64.off p.1 p.2.2.1) fun p s h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.1)
    (by taint_decide) fun p s ⟨hs, hdi, hia, ho⟩ => by
      have hn := hs.nowrap
      have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.1 p.2.2.1) (8 * sIfma)) 8 := by
        rw [off_off]; exact hs.ld (by unfold sIfma sFn; omega)
      exact WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = VG.Proof.Bignum.X86_64.off p.1 p.2.2.2) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl, hia]) rfl) fun t h => h.1)
    (two_taint [.rbx] (VG.Proof.Bignum.X86_64.pins_eqs (fun p _ => VG.Proof.Bignum.X86_64.off p.1 p.2.2.2) fun p s h r hr => by
      rw [List.mem_singleton.mp hr]; exact h) (by taint_decide))

/-! ## The results -/

/-- The public data of a result: `n`'s workspace, the prime's and the area. -/
structure ResPub where
  B : Addr
  Z : Nat
  o : Nat
  a : Nat

/-- `resBlock_ok`'s hypotheses. -/
def ResPre (p : Nat) (q : VG.Proof.Bignum.X86_64.ResPub) (s : State) : Prop :=
  ∃ mx : BitVec 64, VG.Proof.Bignum.X86_64.Scr s q.B q.Z ∧ s.gpr .rdi = VG.Proof.Bignum.X86_64.off q.B q.o ∧ Hdr s.mem (VG.Proof.Bignum.X86_64.off q.B q.o) 16 mx ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sIfma) = VG.Proof.Bignum.X86_64.off q.B q.a ∧ q.o + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ q.a ∧
    q.a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ q.Z ∧ p < 2 ∧ (∀ j < 20, AmmSym.limb s.mem (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) j < 2 ^ 52) ∧
    AmmSym.val52 s.mem (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) < 2 * wv s.mem (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16

/-- The bases of the subtraction. -/
def ResRegs (q : VG.Proof.Bignum.X86_64.ResPub) (t : State) : Prop :=
  t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aAcc) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) ∧
    t.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 16 ∧
    t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aTmp)

theorem result_eq (p : Nat) : CrtIfma.result p = [.block (([.mov .r11 (.mem (hdr sIfma)),
    .alu .add .r11 (.imm (BitVec.ofNat 32 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY))), .mov .r8 (.mem (hdr (sArr Public.aAcc)))] : List Instr) ++
    (CrtIfma.to64 ++ ([.mov .rbx (.mem (hdr (sArr Public.aY))), .mov .r10 (.mem (hdr (sArr Public.aN))),
      .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr Public.aTmp)))] : List Instr))), subMod, selectAcc] := by
  simp only [CrtIfma.result, List.append_assoc]

/-- `result p` is constant time, given that the taint analysis checks its first loads. -/
theorem result_ct (p : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block ([.mov .r11 (.mem (hdr sIfma)),
      .alu .add .r11 (.imm (BitVec.ofNat 32 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY))), .mov .r8 (.mem (hdr (sArr Public.aAcc)))] :
        List Instr)) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.ResPre p)) (seqs (CrtIfma.result p)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.result_eq]
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.ResRegs) (VG.Proof.Bignum.X86_64.ct_split _ _ [.rdi] [.rdi, .r11, .r8]
    (Ψ := fun q t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off q.B q.o ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aAcc))
    (VG.Proof.Bignum.X86_64.pins_eqs (fun q _ => VG.Proof.Bignum.X86_64.off q.B q.o) fun q s h r hr => by
      obtain ⟨_, _, hdi, _⟩ := h; rw [List.mem_singleton.mp hr]; exact hdi) hT ?_
    (VG.Proof.Bignum.X86_64.pins_eqs (fun q r => if r = .rdi then VG.Proof.Bignum.X86_64.off q.B q.o else if r = .r11 then VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) else
      VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aAcc)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide)) ?_)
    (two_taint [.r8, .rbx, .r10, .r12, .rsi] (VG.Proof.Bignum.X86_64.pins_eqs (fun q r => if r = .r8 then VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aAcc)
      else if r = .rbx then VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) else if r = .r10 then
        VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) else if r = .r12 then BitVec.ofNat 64 16 else
          VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aTmp)) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2) (by taint_decide))
  · rintro q s ⟨mx, hs, hdi, hH, hia, hoa, haZ, hp, -⟩
    have hn := hs.nowrap
    have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
    have hDp : VG.Impl.Rsa.X86_64.CrtIfma.D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
    have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
    have hT' : tabBytes 16 = 2304 := rfl
    have : oY = 192 := rfl
    have hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * i)) 8 := fun i hi => by
      rw [off_off]; exact hs.ld (by have := hdr_lt_slot 16 8 hi; omega)
    refine WP.mono (WP.keep [.r11, .r8] (Q := fun t => t.gpr .r11 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (VG.Proof.Bignum.X86_64.slot 16 Public.aAcc)) (by
      xrun [State.ea, hdr, hdi, hdrOff, hH' sIfma (by decide), hH' (sArr Public.aAcc) (by decide),
        AmmSym.se_ofNat (show VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY < 2 ^ 31 by omega)]
      and_intros
      · rw [show s.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off q.B q.o) (8 * sIfma)) 64 = VG.Proof.Bignum.X86_64.off q.B q.a from hia]
      · exact hH.harr _ (by decide)) rfl) fun t ⟨⟨h11, h8'⟩, k⟩ => ⟨(k.gpr (by decide)).trans hdi, h11, h8'⟩
  · rintro q s ⟨mx, hs, hdi, hH, hia, hoa, haZ, hp, hL, hV⟩
    have := resBlock_ok hs hdi hH hia hoa haZ hp hL hV
    simp only [List.append_assoc] at this
    exact WP.mono this fun t ⟨_, _, r8, bx, r10, r12, si, _⟩ => ⟨r8, bx, r10, r12, si⟩

/-! ## `ifma` -/

/-- The public data of `ifma`: `n`'s workspace, the primes', the area, and
the exponents' pointers and lengths. -/
structure IfPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  oq : Nat
  a : Nat
  ep : Addr
  eq : Addr
  lp : Nat
  lq : Nat

/-- `ifma_ok`'s hypotheses, but the values' (which the constant time does not need). -/
def IfPre (p : VG.Proof.Bignum.X86_64.IfPub) (s : State) : Prop :=
  ∃ (minv mp mq mk : BitVec 64) (P Q : Nat) (ebp ebq : List Byte), VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧
    VG.Proof.Bignum.X86_64.IPre s.mem p.B p.w p.op p.oq minv mp mq mk P Q p.ep p.eq ebp.length ebq.length ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧
    p.op + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ p.oq ∧ p.a = p.oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ∧ p.a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ p.Z ∧
    P % 2 = 1 ∧ Q % 2 = 1 ∧ wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < P ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < Q ∧ wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 < P ∧
    wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 < Q ∧ Src s p.B p.Z p.ep ebp ∧ Src s p.B p.Z p.eq ebq ∧
    1 ≤ ebp.length ∧ ebp.length ≤ 128 ∧ 1 ≤ ebq.length ∧ ebq.length ≤ 128 ∧ ebp.length = p.lp ∧ ebq.length = p.lq

/-- Before the last `leave`. -/
def F8 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop := t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.op

/-- Before `p`'s result. -/
def F7 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.ResPre 0 ⟨p.B, p.Z, p.op, p.a⟩ t ∧ WP isa (seqs (CrtIfma.result 0)) t (VG.Proof.Bignum.X86_64.F8 p)

/-- Before the move to `p`'s workspace. -/
def F6 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.SwPre (p.B, p.oq, p.Z) t ∧ WP isa (.block [leave, enterP]) t (VG.Proof.Bignum.X86_64.F7 p)

/-- Before `q`'s result. -/
def F5 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.ResPre 1 ⟨p.B, p.Z, p.oq, p.a⟩ t ∧ WP isa (seqs (CrtIfma.result 1)) t (VG.Proof.Bignum.X86_64.F6 p)

/-- Before the vector code. -/
def F4 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.VPre (p.B, p.Z, p.oq, p.a) t ∧ WP isa (seqs [.block [.mov .rbx (.mem (hdr sIfma))], CrtIfma.vec]) t (VG.Proof.Bignum.X86_64.F5 p)

/-- Before `q`'s region. -/
def F3 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.RegPre 1 sDq sQlen ⟨p.B, p.Z, p.oq, p.a, p.eq, p.lq⟩ t ∧ WP isa (seqs (CrtIfma.region 1 sDq sQlen)) t (VG.Proof.Bignum.X86_64.F4 p)

/-- Before the move to `q`'s workspace. -/
def F2 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.SwPre (p.B, p.op, p.Z) t ∧ WP isa (.block [leave, enterQ]) t (VG.Proof.Bignum.X86_64.F3 p)

/-- Before `p`'s region. -/
def F1 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.RegPre 0 sDp sPlen ⟨p.B, p.Z, p.op, p.a, p.ep, p.lp⟩ t ∧ WP isa (seqs (CrtIfma.region 0 sDp sPlen)) t (VG.Proof.Bignum.X86_64.F2 p)

/-- Before `ifma`. -/
def F0 (p : VG.Proof.Bignum.X86_64.IfPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.HdPre ⟨p.B, p.Z, p.w, p.op, p.oq⟩ t ∧ WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
    ([.mov .rdx (.mem (hdr sWsP)), .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
      .store (VG.Impl.Rsa.X86_64.Crt.ws .rdx sIfma) .rax, enterP] : List Instr))) t (VG.Proof.Bignum.X86_64.F1 p)

theorem regPre_of {p sp sl : Nat} {B : Addr} {Z o a w : Nat} {ep : Addr} {s : State} {mx : BitVec 64} {X : Nat}
    {eb : List Byte} (hoa : o + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z) (hp : p < 2)
    (hsp : sp < 32) (hsl : sl < 32) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 128) (hc : SubCtx s B Z o w 16 mx)
    (hia : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sIfma) = VG.Proof.Bignum.X86_64.off B a) (hN : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16 = X)
    (hY : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < X) (hpv : VG.Proof.Bignum.X86_64.word s.mem B (8 * sp) = ep)
    (hlv : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) (he : Src s B Z ep eb) :
    VG.Proof.Bignum.X86_64.RegPre p sp sl ⟨B, Z, o, a, ep, eb.length⟩ s :=
  ⟨⟨hoa, haZ, hp, hsp, hsl, hL1, hL2⟩, w, mx, X, eb, hc, hia, hN, hY, hpv, hlv, he, rfl⟩

theorem resPre_of {p : Nat} {B : Addr} {Z o a : Nat} {s : State} {mx : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off B o) (hH : Hdr s.mem (VG.Proof.Bignum.X86_64.off B o) 16 mx) (hia : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sIfma) = VG.Proof.Bignum.X86_64.off B a)
    (hoa : o + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 ≤ a) (haZ : a + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z) (hp : p < 2)
    (hL : ∀ j < 20, AmmSym.limb s.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) j < 2 ^ 52)
    (hV : AmmSym.val52 s.mem (VG.Proof.Bignum.X86_64.off B a) (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oY) < 2 * wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot 16 Public.aN) 16) :
    VG.Proof.Bignum.X86_64.ResPre p ⟨B, Z, o, a⟩ s :=
  ⟨mx, hs, hdi, hH, hia, hoa, haZ, hp, hL, hV⟩

theorem swPre_of {B : Addr} {o Z : Nat} {s : State} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off B o)
    (hlk : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B) (ho : o + 8 * 32 ≤ Z) : VG.Proof.Bignum.X86_64.SwPre (B, o, Z) s :=
  ⟨hs, hdi, hlk, ho⟩

theorem vPre_of {B : Addr} {Z o a : Nat} {s : State} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off B o)
    (hia : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sIfma) = VG.Proof.Bignum.X86_64.off B a) (ho : o + 8 * 32 ≤ Z) : VG.Proof.Bignum.X86_64.VPre (B, Z, o, a) s :=
  ⟨hs, hdi, hia, ho⟩

/-- `ifma_ok`'s hypotheses give `F0`, as `ifma_ok` runs the pieces. -/
theorem ifma_chain {p : VG.Proof.Bignum.X86_64.IfPub} {s : State} (h : VG.Proof.Bignum.X86_64.IfPre p s) : VG.Proof.Bignum.X86_64.F0 p s := by
  obtain ⟨B, Z, w, op, oq, a, ep, eq, lp, lq⟩ := p
  dsimp only [VG.Proof.Bignum.X86_64.IfPre] at h
  obtain ⟨minv, mp, mq, mk, P, Q, ebp, ebq, hs, hdi, h, hlo, hpq, ha, haZ, hPo, hQo, hYp, hYq, hXp, hXq, hep,
    heq, hLp1, hLp2, hLq1, hLq2, rfl, rfl⟩ := h
  have hn := hs.nowrap
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have lY := slot_le (w := 16) (show Public.aY < 8 by decide)
  have lC := slot_le (w := 16) (show aXc < 8 by decide)
  have hY0 := hdr_lt_slot 16 Public.aY (show 31 < 32 by decide)
  have hC0 := hdr_lt_slot 16 aXc (show 31 < 32 by decide)
  subst ha
  -- The head.
  refine ⟨⟨minv, mq, ⟨hs, hdi, h.nh⟩, hlo, hpq, haZ, h.wsP, h.wsQ, h.qws⟩, WP.mono
    (VG.Proof.Bignum.X86_64.headI_ok hs hdi h hlo hpq rfl haZ) fun u₁ ⟨m₁, f₁, d₁, k₁⟩ => ?_⟩
  have hf₁ : ∀ {d n}, d + n ≤ op + 8 * sIfma ∨ (op + 8 * sIfma + 8 ≤ d ∧ d + n ≤ oq + 8 * sIfma) ∨
      oq + 8 * sIfma + 8 ≤ d → ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
  have hYp₁ : wv u₁.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 = wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hCp₁ : wv u₁.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 = wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 aXc) 16 := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr (.inl ⟨by unfold sIfma sFn; omega, by omega⟩))) (by omega)
  have hZ₁ : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], r.1 + r.2 ≤ Z := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega
  have hc₁ := SubCtx.mk' (hs.congr k₁.2.2) m₁.nh m₁.pws d₁ hlo (by omega)
  have hep₁ := hep.congr (InScr.of_frm f₁ hZ₁) k₁.2.1 k₁.2.2
  -- `p`'s region.
  dsimp only [VG.Proof.Bignum.X86_64.F1]
  refine ⟨VG.Proof.Bignum.X86_64.regPre_of (by omega) haZ (by decide) (by decide) (by decide) hLp1 hLp2 hc₁ m₁.pia m₁.pn
    (by rw [hYp₁]; exact hYp) m₁.dp m₁.pl hep₁, WP.mono (region_ok (p := 0) hc₁ m₁.pia (by omega) haZ (by decide)
      m₁.pn (by rw [hYp₁]; exact hYp) (by decide) (by decide) m₁.dp m₁.pl hep₁ hLp1 hLp2)
    fun u₂ ⟨rp, f₂, w₂, d₂, k₂⟩ => ?_⟩
  have f₂' := f₂.widen (VG.Proof.Bignum.X86_64.regFr_ifmaR (oq := oq) (.inl rfl) (by decide))
  have m₂ := m₁.of_frm f₂' hlo hpq (by omega) (by omega)
  have F₂ : Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ VG.Proof.Bignum.X86_64.ifmaR op oq (oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16))
      s.mem u₂.mem :=
    (f₁.mono fun r hr => List.mem_append_left _ hr).trans (f₂'.mono fun r hr => List.mem_append_right _ hr)
  have hZF : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ VG.Proof.Bignum.X86_64.ifmaR op oq (oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16),
      r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hZ₁ r hr
    · have := VG.Proof.Bignum.X86_64.ifmaR_le hpq (by omega) r hr; omega
  have hs₂ := hs.congr (w₂.trans k₁.2.2)
  -- To `q`'s workspace.
  dsimp only [VG.Proof.Bignum.X86_64.F2]
  refine ⟨VG.Proof.Bignum.X86_64.swPre_of hs₂ d₂ m₂.pws.link (by omega), WP.mono (VG.Proof.Bignum.X86_64.swapWs_ok (o' := oq) hs₂ d₂ m₂.pws.link m₂.wsQ (by decide)
    (by omega)) fun u₃ ⟨d₃, me₃, k₃⟩ => ?_⟩
  rw [← me₃] at m₂ F₂
  have hq₃ : ∀ j, j < 8 → j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv u₃.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 j) 16 = wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 j) 16 := fun j hj h1 h2 h3 => by
    have := slot_le (w := 16) hj
    have := hdr_lt_slot 16 j (show 31 < 32 by decide)
    rw [wv_off, wv_off, me₃, f₂.wv_eq (fun r hr => ?_) (by omega),
      f₁.wv_eq (hf₁ (.inr (.inr (by unfold sIfma sFn; omega)))) (by omega)]
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := VG.Proof.Bignum.X86_64.k1sh_lt op r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)
  have k₁₃ := (k₁.trans k₂).trans k₃
  have hc₃ := SubCtx.mk' (hs.congr k₁₃.2.2) m₂.nh m₂.qws d₃ (by omega) (by omega)
  have heq₃ := heq.congr (InScr.of_frm F₂ hZF) k₁₃.2.1 k₁₃.2.2
  have hYq₃ : wv u₃.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < Q := by
    rw [hq₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hYq
  -- `q`'s region.
  dsimp only [VG.Proof.Bignum.X86_64.F3]
  refine ⟨VG.Proof.Bignum.X86_64.regPre_of (by omega) haZ (by decide) (by decide) (by decide) hLq1 hLq2 hc₃ m₂.qia m₂.qn hYq₃ m₂.dq m₂.ql
    heq₃, WP.mono (region_ok (p := 1) hc₃ m₂.qia (by omega) haZ (by decide) m₂.qn hYq₃ (by decide) (by decide) m₂.dq
      m₂.ql heq₃ hLq1 hLq2) fun t ⟨rq, f₄, w₄, d₄, k₄⟩ => ?_⟩
  have f₄' := f₄.widen (VG.Proof.Bignum.X86_64.regFr_ifmaR (op := op) (.inr rfl) (by decide))
  rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0)), hYp₁, hCp₁, ← me₃] at rp
  simp only [Nat.one_ne_zero, ↓reduceIte] at rq
  rw [hq₃ _ (by decide) (by decide) (by decide) (by decide),
    hq₃ _ (by decide) (by decide) (by decide) (by decide)] at rq
  have mu := m₂.of_frm f₄' hlo hpq (by omega) (by omega)
  have rp' := rp.of_frm f₄ (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := VG.Proof.Bignum.X86_64.k1sh_lt oq r hr; omega)
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)) (by omega)
  have hsu : VG.Proof.Bignum.X86_64.Scr t B Z := hs.congr (w₄.trans k₁₃.2.2)
  -- The vector code.
  dsimp only [VG.Proof.Bignum.X86_64.F4]
  refine ⟨VG.Proof.Bignum.X86_64.vPre_of hsu d₄ mu.qia (by omega), WP.mono (VG.Proof.Bignum.X86_64.vecI_ok (K := False) (C := 0) (wp := 16) hsu d₄ mu haZ (by omega)
    rp' rq rfl hPo hQo hYp hYq hXp hXq (fun h => h.elim) (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
    hLp2 hLq2) fun v ⟨⟨gp, _⟩, ⟨gq, _⟩, ov, dv, rdv, wrv, _, kv⟩ => ?_⟩
  have fv : Frm B (VG.Proof.Bignum.X86_64.ifmaR op oq (oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16)) t.mem v.mem :=
    (Frm.of_outside_off ov (by omega) (by omega)).widen fun r hr =>
      ⟨(oq + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16, 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8), List.mem_append_right _ (List.mem_singleton_self _),
        by rw [List.mem_singleton.mp hr]; simp only; omega⟩
  have mv := mu.of_frm fv hlo hpq (by omega) (by omega)
  have hsv : VG.Proof.Bignum.X86_64.Scr v B Z := hsu.congr wrv
  have hdv : v.gpr .rdi = VG.Proof.Bignum.X86_64.off B oq := dv.trans d₄
  -- `q`'s result.
  dsimp only [VG.Proof.Bignum.X86_64.F5]
  refine ⟨VG.Proof.Bignum.X86_64.resPre_of hsv hdv mv.qws.hdr mv.qia (by omega) haZ (by decide) gq.lt (by rw [mv.qn]; exact gq.v),
    WP.mono (result_ok (p := 1) hsv hdv mv.qws.hdr mv.qia (by omega) haZ (by decide) mv.qn gq.lt gq.v)
    fun t₁ ⟨_, f₁', d₁', k₁'⟩ => ?_⟩
  have m₁' := mv.of_frm (f₁'.mono (VG.Proof.Bignum.X86_64.resSh_ifmaR op oq _ (.inr rfl))) hlo hpq (by omega) (by omega)
  have hs₁ := hsv.congr k₁'.2.2
  have hd₁ : t₁.gpr .rdi = VG.Proof.Bignum.X86_64.off B oq := d₁'.trans hdv
  -- To `p`'s workspace.
  dsimp only [VG.Proof.Bignum.X86_64.F6]
  refine ⟨VG.Proof.Bignum.X86_64.swPre_of hs₁ hd₁ m₁'.qws.link (by omega), WP.mono (VG.Proof.Bignum.X86_64.swapWs_ok (o' := op) hs₁ hd₁ m₁'.qws.link m₁'.wsP
    (by decide) (by omega)) fun t₂ ⟨d₂', me₂', k₂'⟩ => ?_⟩
  rw [← me₂'] at m₁'
  have gp₂ := VG.Proof.Bignum.X86_64.goodY_below gp (show Frm B _ v.mem t₂.mem by rw [me₂']; exact f₁')
    (fun r hr => by have := VG.Proof.Bignum.X86_64.resSh_lt oq r hr; omega) (by decide) (by omega)
  have hs₂' := hs₁.congr k₂'.2.2
  -- `p`'s result.
  dsimp only [VG.Proof.Bignum.X86_64.F7]
  exact ⟨VG.Proof.Bignum.X86_64.resPre_of hs₂' d₂' m₁'.pws.hdr m₁'.pia (by omega) haZ (by decide) gp₂.1.lt
      (by rw [m₁'.pn]; exact gp₂.1.v),
    WP.mono (result_ok (p := 0) hs₂' d₂' m₁'.pws.hdr m₁'.pia (by omega) haZ (by decide) m₁'.pn gp₂.1.lt gp₂.1.v)
      fun t₃ ⟨_, _, d₃', _⟩ => d₃'.trans d₂'⟩

/-- `ifma` is constant time. -/
theorem ifma_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.IfPre) (seqs CrtIfma.ifma) fun _ _ => True := by
  refine two_map id (fun _ _ h => VG.Proof.Bignum.X86_64.ifma_chain h) ?_
  rw [VG.Proof.Bignum.X86_64.ifma_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Bignum.X86_64.ct_cons (by simp [CrtIfma.region]) (two_map (fun p : VG.Proof.Bignum.X86_64.IfPub => (⟨p.B, p.Z, p.w, p.op, p.oq⟩ : VG.Proof.Bignum.X86_64.HdPub))
    (fun _ _ h => h.1) VG.Proof.Bignum.X86_64.head_ct) (fun _ _ h => h.2) ?_
  refine VG.Proof.Bignum.X86_64.ct_steps (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (by simp)
    (fun p : VG.Proof.Bignum.X86_64.IfPub => (⟨p.B, p.Z, p.op, p.a, p.ep, p.lp⟩ : VG.Proof.Bignum.X86_64.RegPub)) (fun _ _ h => h.1) (fun _ _ h => h.2)
    (VG.Proof.Bignum.X86_64.region0_ct (by taint_decide)) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (by simp [CrtIfma.region]) (two_map (fun p : VG.Proof.Bignum.X86_64.IfPub => (p.B, p.op, p.Z)) (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.swap_ct sWsQ (by taint_decide))) (fun _ _ h => h.2) ?_
  refine VG.Proof.Bignum.X86_64.ct_steps (by simp [CrtIfma.region, CrtIfma.k1, copyArr]) (by simp)
    (fun p : VG.Proof.Bignum.X86_64.IfPub => (⟨p.B, p.Z, p.oq, p.a, p.eq, p.lq⟩ : VG.Proof.Bignum.X86_64.RegPub)) (fun _ _ h => h.1) (fun _ _ h => h.2)
    (VG.Proof.Bignum.X86_64.region1_ct (by taint_decide)) ?_
  refine VG.Proof.Bignum.X86_64.ct_steps (c := [.block [.mov .rbx (.mem (hdr sIfma))], CrtIfma.vec]) (by simp) (by simp [CrtIfma.result])
    (fun p : VG.Proof.Bignum.X86_64.IfPub => (p.B, p.Z, p.oq, p.a)) (fun _ _ h => h.1) (fun _ _ h => h.2) VG.Proof.Bignum.X86_64.vecB_ct ?_
  refine VG.Proof.Bignum.X86_64.ct_steps (by simp [CrtIfma.result]) (by simp) (fun p : VG.Proof.Bignum.X86_64.IfPub => (⟨p.B, p.Z, p.oq, p.a⟩ : VG.Proof.Bignum.X86_64.ResPub))
    (fun _ _ h => h.1) (fun _ _ h => h.2) (VG.Proof.Bignum.X86_64.result_ct 1 (by taint_decide)) ?_
  refine VG.Proof.Bignum.X86_64.ct_cons (by simp [CrtIfma.result]) (two_map (fun p : VG.Proof.Bignum.X86_64.IfPub => (p.B, p.oq, p.Z)) (fun _ _ h => h.1)
    (VG.Proof.Bignum.X86_64.swap_ct sWsP (by taint_decide))) (fun _ _ h => h.2) ?_
  exact VG.Proof.Bignum.X86_64.ct_steps (by simp [CrtIfma.result]) (by simp) (fun p : VG.Proof.Bignum.X86_64.IfPub => (⟨p.B, p.Z, p.op, p.a⟩ : VG.Proof.Bignum.X86_64.ResPub))
    (fun _ _ h => h.1) (fun _ _ h => h.2) (VG.Proof.Bignum.X86_64.result_ct 0 (by taint_decide))
    (two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_eqs (fun p _ => VG.Proof.Bignum.X86_64.off p.B p.op) fun p s (h : VG.Proof.Bignum.X86_64.F8 p s) r hr => by
      rw [List.mem_singleton.mp hr]; exact h) (by taint_decide))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PcCode`. -/
section

/-!
# `vg_rsa_public_precompute` on x86-64: correctness

The entry (`pcEntry_ok`), an invalid modulus (`pcFail_ok`) and the whole
function (`pcCode_correct`), against `pcContract`, which states the shared
contract's precondition on the registers.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

/-! ## The contract on the registers -/

/-- `vg_rsa_public_precompute(pre = rdi, pre_len = rsi, n = rdx, n_len = rcx,
scratch = r8, scratch_len = r9)`. -/
def pcContract : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [n] ∧ s.wr = [pre, scr] ∧ pre.Disjoint n ∧ pre.Disjoint scr ∧ n.Disjoint scr ∧
      ret.Disjoint pre ∧ ret.Disjoint n ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64 ∧ Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧
      (s.gpr .rsi).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (s.gpr .r9).toNat
  post s s' :=
    match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
    | some ws => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = ws
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-! ## The entry -/

/-- Slot `i` of the header at `r8`. -/
def hdr8 (i : Nat) : MemOp := { base := .r8, disp := 8 * (i : Int) }

theorem pcEntry_eq : Precompute.entry = [.store (VG.Proof.Bignum.X86_64.hdr8 0) .rbx, .store (VG.Proof.Bignum.X86_64.hdr8 1) .rbp, .store (VG.Proof.Bignum.X86_64.hdr8 2) .r12,
    .store (VG.Proof.Bignum.X86_64.hdr8 3) .r13, .store (VG.Proof.Bignum.X86_64.hdr8 4) .r14, .store (VG.Proof.Bignum.X86_64.hdr8 5) .r15, .store (VG.Proof.Bignum.X86_64.hdr8 sOut) .rdi,
    .store (VG.Proof.Bignum.X86_64.hdr8 sN) .rdx, .store (VG.Proof.Bignum.X86_64.hdr8 sK) .rcx, .mov .rdi (.reg .r8)] := rfl

/-- The header after the entry's stores. -/
def pcEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk : BitVec 64) : Mem :=
  ((((((((m.writeW (VG.Proof.Bignum.X86_64.off B (8 * 0)) v0).writeW (VG.Proof.Bignum.X86_64.off B (8 * 1)) v1).writeW (VG.Proof.Bignum.X86_64.off B (8 * 2)) v2).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * 3)) v3).writeW (VG.Proof.Bignum.X86_64.off B (8 * 4)) v4).writeW (VG.Proof.Bignum.X86_64.off B (8 * 5)) v5).writeW (VG.Proof.Bignum.X86_64.off B (8 * sOut)) vo).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sN)) vn).writeW (VG.Proof.Bignum.X86_64.off B (8 * sK)) vk

theorem pcEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk : BitVec 64) :
    let m' := VG.Proof.Bignum.X86_64.pcEntryMem m B v0 v1 v2 v3 v4 v5 vo vn vk
    VG.Proof.Bignum.X86_64.word m' B (8 * 0) = v0 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 1) = v1 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 2) = v2 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 3) = v3 ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * 4) = v4 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 5) = v5 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sOut) = vo ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sN) = vn ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sK) = vk ∧ VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' VG.Proof.Bignum.X86_64.pcEntryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- The entry: the saved registers and the arguments in the header at
`scratch` (`r8`), and its base in `rdi`. -/
theorem pcEntry_ok {s : State} {B : Addr} (hB : s.gpr .r8 = B)
    (hw : ∀ i < 22, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8) :
    WP isa (.block Precompute.entry) s fun t => t.gpr .rdi = B ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 0) = s.gpr .rbx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 1) = s.gpr .rbp ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 2) = s.gpr .r12 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 3) = s.gpr .r13 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 4) = s.gpr .r14 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 5) = s.gpr .r15 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sN) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sK) = s.gpr .rcx ∧ VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdi] s t := by
  rw [VG.Proof.Bignum.X86_64.pcEntry_eq]
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = VG.Proof.Bignum.X86_64.pcEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx)) ?_ rfl) fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  · xrun [State.ea, VG.Proof.Bignum.X86_64.hdr8, hB, hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide),
      hw 4 (by decide), hw 5 (by decide), hw sOut (by decide), hw sN (by decide), hw sK (by decide)]
    rfl
  rw [hm]
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hN, hK, ho⟩ := VG.Proof.Bignum.X86_64.pcEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp)
    (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx)
  exact ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK, ho, k⟩

/-! ## An invalid modulus -/

theorem readW_zero {m : Mem} {a : Addr} (h : ∀ i < 8, m (a + BitVec.ofNat 64 i) = 0) : m.readW a 64 = 0 :=
  (Mem.readW_congr (m' := fun _ => 0) fun i hi => h i (by omega)).trans (by simp [Mem.readW, Mem.read])

theorem sixteen_w (r : BitVec 64) {w : Nat} (h : r = BitVec.ofNat 64 w) :
    r + r + (r + r) + (r + r + (r + r)) + (r + r + (r + r) + (r + r + (r + r))) = BitVec.ofNat 64 (16 * w) := by
  subst h; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega

/-- `fail`: `16 w` zero bytes to `pre` (`2 w` words), 0 returned, and the
saved registers restored. -/
theorem pcFail_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = op) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hout : ∀ j < 16 * ((k + 7) / 8), InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < 16 * ((k + 7) / 8), Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)) :
    WP isa Precompute.fail s fun t =>
      PcPost s t B Z ((k + 7) / 8) op (List.replicate (2 * ((k + 7) / 8)) 0) false := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold Precompute.fail
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 (16 * ((k + 7) / 8)) ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK,
      shr3_w k (by omega), VG.Proof.Bignum.X86_64.sixteen_w _ rfl]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 16 * ((k + 7) / 8)) (by omega)
    (FailInv s₁ op (16 * ((k + 7) / 8))) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t₂ hI => ?_)
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧
        t'.gpr .rcx = BitVec.ofNat 64 (16 * ((k + 7) / 8) - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = 16 * ((k + 7) / 8)))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ 16 * ((k + 7) / 8) - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show 16 * ((k + 7) / 8) - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show 16 * ((k + 7) / 8) - j - 1 = 16 * ((k + 7) / 8) - (j + 1) by omega],
        decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, VG.WriteBytes.writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  -- The saved registers.
  have hw₂ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hI.frame _ (fun j hj => scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega) j (by omega)), hm₁]
  have k12 := k₁.trans hI.keep
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  rw [exit_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide),
      hw₂ 2 (by decide), hw₂ 3 (by decide), hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨?_, ?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [Spec.Rsa.wordsAt, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    refine VG.Proof.Bignum.X86_64.readW_zero fun b hb => ?_
    have hi := List.mem_range.mp hi
    rw [hm, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hI.bytes _ (by omega)
  · rw [k₃.gpr (by decide), hI.keep.gpr (by decide), hax]; rfl
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm, hI.frame x fun j hj he => by
      rw [he, VG.Proof.Bignum.X86_64.ofs, Mem.sub_ofNat_toNat op (by omega)] at hx; omega,
      hm₁]

/-! ## The whole function -/

/-- What `code` uses of its contract's precondition, for the working space
`B = scratch` (`r8`) of `Z` bytes, `m`'s length `k` and `pre`'s `2 w`
words. -/
structure PcCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hpl : (s.gpr .rsi).toNat = 2 * (((s.gpr .rcx).toNat + 7) / 8)
  hZ : 128 * (s.gpr .rcx).toNat ≤ (s.gpr .r9).toNat * 8
  hs : VG.Proof.Bignum.X86_64.Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8)
  hnb : Src s (s.gpr .r8) ((s.gpr .r9).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  hpw : ∀ i < 2 * (((s.gpr .rcx).toNat + 7) / 8), InRegions s.wr (VG.Proof.Bignum.X86_64.off (s.gpr .rdi) (8 * i)) 8
  hpb : ∀ j < 16 * (((s.gpr .rcx).toNat + 7) / 8), InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  hps : ∀ j < 16 * (((s.gpr .rcx).toNat + 7) / 8),
    (s.gpr .r9).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (s.gpr .r8) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (s.gpr .r9).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (s.gpr .r8) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    16 * (((s.gpr .rcx).toNat + 7) / 8) ≤ VG.Proof.Bignum.X86_64.ofs (s.gpr .rdi) (s.gpr .rsp + BitVec.ofNat 64 b)

theorem pcCtx_of {s : State} (h : pcContract.pre s) : VG.Proof.Bignum.X86_64.PcCtx s := by
  simp only [VG.Proof.Bignum.X86_64.pcContract] at h
  obtain ⟨hrd, hwr, dPn, dPs, dns, dRp, dRn, dRs, wP, wN, wS, hk, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hpl
  have hs : VG.Proof.Bignum.X86_64.Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hp8 : (s.gpr .rsi).toNat * 8 = 16 * (((s.gpr .rcx).toNat + 7) / 8) := by omega
  have hpre : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  refine ⟨hk1, hk2, hpl, by omega, hs, VG.Proof.Bignum.X86_64.src_of_region (by rw [hrd]; simp) (by omega) dns,
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => ⟨_, hpre, VG.Proof.Bignum.X86_64.contains_byte _ (by omega) (by omega)⟩,
    fun j hj => VG.Proof.Bignum.X86_64.out_scr dPs (VG.Proof.Bignum.X86_64.contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := VG.Proof.Bignum.X86_64.contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨VG.Proof.Bignum.X86_64.out_scr dRs hc, hp8 ▸ VG.Proof.Bignum.X86_64.out_scr dRp hc⟩

theorem pcCode_correct (M : Mont)
    (hmx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : pcContract.pre s) :
    ∃ t s', Exec isa (Precompute.code M.mm) s t s' ∧ abiPreserved s s' ∧ pcContract.post s s' := by
  have c := VG.Proof.Bignum.X86_64.pcCtx_of h
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa (Precompute.code M.mm) s fun s' => gprPreserved s s' ∧ pcContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Precompute.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.pcEntry_ok rfl fun i hi => c.hs.st (by omega))
    fun t₁ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK, ho₁, k₁⟩ => ?_
  have i₁ : InScr (s.gpr .r8) ((s.gpr .r9).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hnb₁ := c.hnb.congrK i₁ k₁
  refine WP.mono (invalid_ok ((k₁.gpr (by decide)).trans rfl) (by rw [k₁.gpr (by decide), VG.Proof.Bignum.X86_64.ofNat_toNat64]) hk1 hk2
    (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have kk := k₁.trans k₂
  have i₂ : InScr (s.gpr .r8) ((s.gpr .r9).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact i₁
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = s.gpr .r8 := (k₂.gpr (by decide)).trans hdi
  have hw : ∀ i < 2 * (((s.gpr .rcx).toNat + 7) / 8), InRegions t₂.wr (VG.Proof.Bignum.X86_64.off (s.gpr .rdi) (8 * i)) 8 :=
    fun i hi => by rw [kk.2.2]; exact c.hpw i hi
  have hz : VG.Proof.Bignum.X86_64.slot (((s.gpr .rcx).toNat + 7) / 8) 8 ≤ (s.gpr .r9).toNat * 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  -- What either branch leaves.
  have fin : ∀ t (ws : List (BitVec 64)) (cb : Bool),
      PcPost t₂ t (s.gpr .r8) ((s.gpr .r9).toNat * 8) (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .rdi) ws cb →
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
        if cb then some ws else none) →
      (cb = false → ws = List.replicate (2 * (((s.gpr .rcx).toNat + 7) / 8)) 0) →
      gprPreserved s t ∧ pcContract.post s t := by
    intro t ws cb hp hpc hws
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.saved 0 (by decide)).trans (by rw [hm₂]; exact h0)
      · exact (hp.saved 1 (by decide)).trans (by rw [hm₂]; exact h1)
      · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
      · exact (hp.saved 2 (by decide)).trans (by rw [hm₂]; exact h2)
      · exact (hp.saved 3 (by decide)).trans (by rw [hm₂]; exact h3)
      · exact (hp.saved 4 (by decide)).trans (by rw [hm₂]; exact h4)
      · exact (hp.saved 5 (by decide)).trans (by rw [hm₂]; exact h5)
    · obtain ⟨hZx, hPx⟩ := c.hret b hb
      rw [hp.frame _ hZx hPx, i₂ _ hZx]
    · simp only [VG.Proof.Bignum.X86_64.pcContract]
      rw [hpc, c.hpl]
      cases cb
      · simp only [Bool.false_eq_true, ite_false]
        exact ⟨by rw [hp.rax]; rfl, by rw [hp.words, hws rfl]⟩
      · simp only [ite_true]
        exact ⟨by rw [hp.rax]; rfl, hp.words⟩
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [VG.X86_64.eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    refine WP.mono (VG.Proof.Bignum.X86_64.pcFail_ok hs₂ hdi₂ (by omega) (by omega) (by omega) (by rw [hm₂]; exact hO)
      (by rw [hm₂, hK, VG.Proof.Bignum.X86_64.ofNat_toNat64]) (fun j hj => by rw [kk.2.2]; exact c.hpb j hj) c.hps)
      fun t hp => fin t _ false hp ?_ fun _ => rfl
    simp only [Spec.Rsa.publicPrecompute, VG.Proof.Bignum.X86_64.bytesAt_length, hv, Bool.false_eq_true, ite_false]
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    refine WP.mono (pcMain_ok M hs₂ hdi₂ hz hk1 hk2 (by rw [hm₂]; exact hO) (by rw [hm₂, hK, VG.Proof.Bignum.X86_64.ofNat_toNat64])
      (by rw [hm₂]; exact hN) (c.hnb.congrK i₂ kk) (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) hv hw c.hps)
      fun t ⟨ws, hws, hp⟩ => fin t ws true hp (by rw [hws]; rfl) fun h => absurd h (by decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PcCT`. -/
section

/-!
# `vg_rsa_public_precompute` on x86-64: constant time but for `n`

Every piece's addresses and branches depend only on the pointers, the
lengths and `n`: the load of `m` and `-m⁻¹` (`pcLoad_ct`), `R² mod m`
(`r2_ct`), the copies to `pre` (`pcOut_ct`), and the whole function
(`pcCode_constantTime`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## `main` -/

/-- The public data of `main`: the working space, `k`, `pre`, and `m` (its
bytes `nb` at `np`). -/
structure PcPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  nb : List Byte

abbrev PcPub.w (p : VG.Proof.Bignum.X86_64.PcPub) : Nat := (p.k + 7) / 8
abbrev PcPub.N (p : VG.Proof.Bignum.X86_64.PcPub) : Nat := Spec.Rsa.os2ip p.nb

/-- `pcMain_ok`'s hypotheses. -/
def PcM (p : VG.Proof.Bignum.X86_64.PcPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sOut) = p.op ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sN) = p.np ∧ Src s p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ (∀ i < 2 * p.w, InRegions s.wr (VG.Proof.Bignum.X86_64.off p.op (8 * i)) 8) ∧
    (∀ i < 16 * p.w, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (p.op + BitVec.ofNat 64 i))

/-- `PcM` after code that changes only memory in the working space outside
the header's arguments, and not `rdi`. -/
theorem PcM.congr {p : VG.Proof.Bignum.X86_64.PcPub} {s t : State} (h : VG.Proof.Bignum.X86_64.PcM p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.PcM p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk2, hO, hK, hN, hn, hnl, hv, hpw, hps⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk2, (hfx sOut (by decide)).trans hO,
    (hfx sK (by decide)).trans hK, (hfx sN (by decide)).trans hN, hn.congrK hi k, hnl, hv,
    fun i hi => by rw [k.2.2]; exact hpw i hi, hps⟩

theorem pins_PcM : Pins VG.Proof.Bignum.X86_64.PcM [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the first block. -/
def Pc1 (p : VG.Proof.Bignum.X86_64.PcPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.PcM p s ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j)) ∧
    s.gpr .rsi = p.np ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN)

/-- After `m`'s load. -/
def Pc2 (p : VG.Proof.Bignum.X86_64.PcPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.PcM p s ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sArr j) = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j)) ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aN) p.w = p.N ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN)

/-- After `-m⁻¹`: `R² mod m`'s hypotheses, and `PcM`. -/
def Pc3 (p : VG.Proof.Bignum.X86_64.PcPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, VG.Proof.Bignum.X86_64.PcM p s ∧ VG.Proof.Bignum.X86_64.R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s

theorem pins_Pc1 : Pins VG.Proof.Bignum.X86_64.Pc1 [.rdi, .rsi, .rcx, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.1.2.1, h₂.1.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem pins_Pc2 : Pins VG.Proof.Bignum.X86_64.Pc2 [.rdi, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.2.1, h₂.1.2.1]
  · rw [h₁.2.2.2.2, h₂.2.2.2.2]

/-- The load of `m` and `-m⁻¹` leak the same in runs that agree on `m`. -/
theorem pcLoad_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.PcM) (seqs pcLoad) (Two VG.Proof.Bignum.X86_64.Pc3) := by
  unfold pcLoad
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.Pc1) _ VG.Proof.Bignum.X86_64.pins_PcM (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk2, -, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge p.w
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t ⟨_, hcx, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), hW, hb, hsi, hcx, hbx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.Pc2) _ VG.Proof.Bignum.X86_64.pins_Pc1 (by taint_decide) ?_) ?_
  · intro p s ⟨h, hW, hb, hsi, hcx, hbx⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk1, hk2, -, -, -, hn, hnl, -⟩ := h'
    have := slot_le (w := p.w) (show aN < 8 by decide)
    refine WP.mono (loadArr_ok hs (by decide) hZ hn hnl (by omega) (by omega) hsi hcx hbx) fun t ⟨hv, ha, k⟩ =>
      ⟨h.congr (Frm.of_arrays1 ha (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k (by decide),
        by rw [ha.hslot (by decide)]; exact hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact hb j hj,
        hv, (k.gpr (by decide)).trans hbx⟩
    · rw [List.mem_singleton.mp hr]; exact this.trans hZ
    · rw [List.mem_singleton.mp hr]; exact VG.Proof.Bignum.X86_64.arr_fixed _
  -- `-m⁻¹`.
  refine two_piece (Ψ := VG.Proof.Bignum.X86_64.Pc3) _ VG.Proof.Bignum.X86_64.pins_Pc2 (by taint_decide) ?_
  intro p s ⟨h, hW, hb, hv, hbx⟩
  have h' := h
  obtain ⟨hs, hdi, hZ, hk1, hk2, -, -, -, -, hnl, hval, -⟩ := h'
  obtain ⟨hodd, -, hlo⟩ := valid_facts hval hk1
  have hn := hs.nowrap
  have h0 := slot_le (w := p.w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot p.w 0 (show 31 < 32 by decide)
  have hsN := slot_le (w := p.w) (show aN < 8 by decide)
  have hw1 : 2 ≤ p.w := by unfold PcPub.w; omega
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eAN : sArr aN = 8 := rfl
  have hZ8 : 8 * 32 ≤ p.Z := by omega
  have hodd₀ : (VG.Proof.Bignum.X86_64.word s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), Nat.mod_mod_of_dvd _ (by decide), hv, hodd]
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  rw [seqs_one, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10, .r12, .rbx] (Q := fun t => t.gpr .r10 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, at0, hdi, hdrOff, hl sW (by decide), hbx, hW,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld (d := VG.Proof.Bignum.X86_64.slot p.w aN) (by omega)])
    rfl) fun t₃ ⟨⟨h10₃, h12₃, hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [hbx₃] at hinv
  have hs₄ := (hs.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = p.B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by unfold sMinv; omega)]) rfl)
    fun t ⟨hm, k₅⟩ => ?_
  have hm' : t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * sMinv)) (t₄.gpr .r15) := by rw [hm, hm₄, hm₃]
  have hwo : VG.Proof.Bignum.X86_64.Outside p.B (8 * sMinv) 8 s.mem t.mem := by rw [hm']; exact VG.Proof.Bignum.X86_64.writeW_outside _ p.B _ (by omega)
  have kk := (k₃.trans k₄).trans k₅
  refine ⟨t₄.gpr .r15, h.congr (Frm.of_outside hwo (List.mem_singleton_self _)) (by simp [sMinv]; omega)
    (by simp [sMinv]) kk (by decide), ⟨⟨hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄, ⟨?_, ?_, fun j hj => ?_⟩⟩, hZ⟩,
    hw1, by dsimp only; unfold PcPub.w; omega, ?_, ?_, (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h12₃),
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10₃), hodd, hlo⟩
  · rw [hwo.word (by unfold sW sMinv; omega) (by omega)]; exact hW
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hwo.word (d := 8 * sArr j) (by unfold sArr sMinv; omega) (by unfold sArr; omega)]; exact hb j hj
  · dsimp only
    rw [hwo.wv (by have := hdr_lt_slot p.w aN (show sMinv < 32 by decide); omega) (by omega)]; exact hv
  · dsimp only
    rw [hwo.word (by have := hdr_lt_slot p.w aN (show sMinv < 32 by decide); omega) (by omega)]; exact hinv

/-! ## `R² mod m` -/

/-- `main`'s public data with `-m⁻¹`. -/
abbrev PcPub.L (q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, q.1.w, q.2⟩

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem pc3_minv {p : VG.Proof.Bignum.X86_64.PcPub} {s₁ s₂ : State} {mi₁ mi₂ : BitVec 64}
    (h₁ : VG.Proof.Bignum.X86_64.R2Pre ⟨⟨p.B, p.Z, p.w, mi₁⟩, p.N⟩ s₁) (h₂ : VG.Proof.Bignum.X86_64.R2Pre ⟨⟨p.B, p.Z, p.w, mi₂⟩, p.N⟩ s₂) : mi₁ = mi₂ := by
  have e : ∀ {s : State} {mi : BitVec 64}, VG.Proof.Bignum.X86_64.R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s →
      ((p.N % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 := fun h => by
    have hw := h.2.1
    have hv := h.2.2.2.1
    have hi := h.2.2.2.2.1
    dsimp only at hw hv hi
    rwa [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), hv] at hi
  exact VG.Proof.Bignum.X86_64.minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.2.2.2.2.2.2.2.1) (e h₁) (e h₂)

/-- What the copies to `pre` need. -/
def PcO (q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64) (s : State) : Prop :=
  GoodL (PcPub.L q) s ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧ VG.Proof.Bignum.X86_64.word s.mem q.1.B (8 * sOut) = q.1.op ∧
    (∀ i < 2 * q.1.w, InRegions s.wr (VG.Proof.Bignum.X86_64.off q.1.op (8 * i)) 8) ∧
    (∀ i < 16 * q.1.w, q.1.Z ≤ VG.Proof.Bignum.X86_64.ofs q.1.B (q.1.op + BitVec.ofNat 64 i))

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem pcR2_ct (M : Mont) : RelCT isa (Two VG.Proof.Bignum.X86_64.Pc3) (seqs (r2Steps M)) (Two VG.Proof.Bignum.X86_64.PcO) := by
  have h := two_post (Φ := fun (q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64) s => VG.Proof.Bignum.X86_64.PcM q.1 s ∧ VG.Proof.Bignum.X86_64.R2Pre ⟨PcPub.L q, q.1.N⟩ s)
    (Ψ := VG.Proof.Bignum.X86_64.PcO) (two_map (fun q => (⟨PcPub.L q, q.1.N⟩ : VG.Proof.Bignum.X86_64.R2Pub)) (fun _ _ h => h.2) (VG.Proof.Bignum.X86_64.r2_ct M)) ?_
  · exact h.mono (fun _ _ hp => VG.Proof.Bignum.X86_64.two_bind (fun p s₁ s₂ ⟨mi₁, m₁, r₁⟩ ⟨mi₂, m₂, r₂⟩ => by
      obtain rfl := VG.Proof.Bignum.X86_64.pc3_minv r₁ r₂
      exact ⟨(p, mi₁), ⟨m₁, r₁⟩, m₂, r₂⟩) hp) fun _ _ h => h
  rintro ⟨p, mi⟩ s ⟨hm, hr⟩
  obtain ⟨hg, hw, hw', hn, hinv, h12, h10, hodd, hlo⟩ := hr
  dsimp only at hg hw hw' hn hinv h12 h10 hodd hlo
  refine WP.mono (r2_ok M hg.1 hg.2 hw hw' hn hinv h12 h10 hodd hlo) fun t ⟨hg', _, _, f, k⟩ =>
    ⟨⟨hg', hg.2⟩, hw, hw', ?_, fun i hi => by rw [k.2.2]; exact hm.2.2.2.2.2.2.2.2.2.2.2.1 i hi,
      hm.2.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [(Fixed.of_frm f (r2Ranges_fixed _)) sOut (by decide)]
  exact hm.2.2.2.2.2.1

/-! ## The copies to `pre` -/

/-- `Good` after code that changes only memory outside the working space. -/
theorem Good.of_inScr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hi : ∀ x, VG.Proof.Bignum.X86_64.ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = B) : VG.Proof.Bignum.X86_64.Good t B Z w minv := by
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have hw : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi' =>
    Mem.readW_congr fun b hb => hi _ (by rw [VG.Proof.Bignum.X86_64.ofs_off B (d := 8 * i) (i := b) (by omega)]; omega)
  exact ⟨hg.scr.congr hwr, hdi, ⟨by rw [hw sW (by decide)]; exact hg.hdr.hw,
    by rw [hw sMinv (by decide)]; exact hg.hdr.hminv,
    fun j hj => by rw [hw (sArr j) (by unfold sArr; omega)]; exact hg.hdr.harr j hj⟩⟩

/-- Before the first copy. -/
def PcO1 (q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.PcO q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w aN) ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off q.1.op 0

/-- After the first copy. -/
def PcO2 (q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.PcO q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off q.1.op 0

/-- Before the second copy. -/
def PcO3 (q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.PcO q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w aR2) ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off q.1.op (8 * q.1.w)

theorem pins_PcO : Pins VG.Proof.Bignum.X86_64.PcO [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.rdi, h₂.1.1.rdi]

/-- A copy of `w` words from the working space to `pre` at `pre + 8 d`,
`d ≤ w`: the working space is as it was. -/
theorem pcCopy_ok {q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64} {s : State} (h : VG.Proof.Bignum.X86_64.PcO q s) {e d : Nat} (hd : d ≤ q.1.w)
    (he : e + 8 * q.1.w ≤ q.1.Z) (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B e) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off q.1.op (8 * d))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 q.1.w) :
    WP isa copyWords s fun t => VG.Proof.Bignum.X86_64.PcO q t ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r14] s t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  have hs : VG.Proof.Bignum.X86_64.Scr s q.1.B q.1.Z := hg.1.scr
  have hn := hs.nowrap
  have hZ : VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z := hg.2
  have hsep : ∀ x, VG.Proof.Bignum.X86_64.ofs q.1.B x < q.1.Z → 16 * q.1.w ≤ VG.Proof.Bignum.X86_64.ofs q.1.op x := fun x hx => le_ofs_of_sep hps hx
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega) (by omega) (by omega)
    (fun j hj => hs.ld (by omega))
    (fun j hj => by rw [show 8 * d + 8 * j = 8 * (d + j) by omega]; exact hpw (d + j) (by omega))
    (fun j hj b hb => Or.inr (le_trans (by omega)
      (hsep _ (by rw [VG.Proof.Bignum.X86_64.ofs_off q.1.B (d := e + 8 * j) (i := b) (by omega)]; omega)))))
    fun t ⟨_, _, ho, k⟩ => ?_
  have hi : ∀ x, VG.Proof.Bignum.X86_64.ofs q.1.B x < q.1.Z → t.mem x = s.mem x := fun x hx =>
    ho x (Or.inr (by have := hsep x hx; omega))
  refine ⟨⟨⟨Good.of_inScr (hg.1 : VG.Proof.Bignum.X86_64.Good s q.1.B q.1.Z q.1.w q.2) hZ hi k.2.2
    ((k.gpr (by decide)).trans hg.1.rdi), hZ⟩, hw, hw', ?_,
    fun i hi' => by rw [k.2.2]; exact hpw i hi', hps⟩, k⟩
  rw [← hO]
  exact Mem.readW_congr fun b hb => hi _ (by
    have := hdr_lt_slot q.1.w 0 (show 31 < 32 by decide)
    have := slot_le (w := q.1.w) (show 0 < 8 by decide)
    rw [VG.Proof.Bignum.X86_64.ofs_off q.1.B (d := 8 * sOut) (i := b) (by unfold sOut sFn; omega)]; unfold sOut sFn; omega)

theorem PcO.mem {q : VG.Proof.Bignum.X86_64.PcPub × BitVec 64} {s t : State} (h : VG.Proof.Bignum.X86_64.PcO q s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.PcO q t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  exact ⟨⟨Good.of_inScr (hg.1 : VG.Proof.Bignum.X86_64.Good s q.1.B q.1.Z q.1.w q.2) hg.2 (fun x _ => by rw [hm]) k.2.2
    ((k.gpr hr).trans hg.1.rdi), hg.2⟩, hw, hw', by rw [hm]; exact hO,
    fun i hi => by rw [k.2.2]; exact hpw i hi, hps⟩

/-- The copies to `pre` leak the same in runs with the same working space and
`pre`. -/
theorem pcOut_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.PcO) (seqs pcOut) fun _ _ => True := by
  unfold pcOut
  -- The first copy's registers.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.PcO1) _ VG.Proof.Bignum.X86_64.pins_PcO (by taint_decide) ?_) ?_
  · intro q s h
    have hs : VG.Proof.Bignum.X86_64.Scr s q.1.B q.1.Z := h.1.1.scr
    have hn := hs.nowrap
    have hZ : VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge q.1.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off q.1.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 q.1.w ∧
        t.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w aN) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off q.1.op 0 ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.1.1.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
        h.1.1.hdr.hw, h.1.1.hdr.harr aN (by decide), h.2.2.2.1]) rfl)
      fun t ⟨⟨h12, hsi, hbx, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h12, hsi, hbx⟩
  -- The first copy.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.PcO2) [.rsi, .rbx, .r12] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, hsi, hbx⟩
    have := slot_le (w := q.1.w) (show aN < 8 by decide)
    have hZ : VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z := h.1.2
    exact WP.mono (VG.Proof.Bignum.X86_64.pcCopy_ok h (d := 0) (by omega) (by omega) hsi (by rw [hbx]) h12)
      fun t ⟨h', k⟩ => ⟨h', (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hbx⟩
  -- The second copy's registers.
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.PcO3) [.rdi, .r12, .rbx] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, hbx⟩
    have hs : VG.Proof.Bignum.X86_64.Scr s q.1.B q.1.Z := h.1.1.scr
    have hn := hs.nowrap
    have hZ : VG.Proof.Bignum.X86_64.slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge q.1.w
    have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 q.1.w → r + r + (r + r) + (r + r + (r + r)) =
        BitVec.ofNat 64 (8 * q.1.w) := by
      rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
    have hbx' : s.gpr .rbx = q.1.op := by rw [hbx]; simp [VG.Proof.Bignum.X86_64.off]
    refine WP.mono (WP.keep [.rax, .rbx, .rsi] (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off q.1.op (8 * q.1.w) ∧
        t.gpr .rsi = VG.Proof.Bignum.X86_64.off q.1.B (VG.Proof.Bignum.X86_64.slot q.1.w aR2) ∧ t.mem = s.mem) (by
      unfold eightW
      simp only [List.cons_append, List.nil_append]
      xrun [State.ea, hdr, h.1.1.rdi, hdrOff, hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
        h.1.1.hdr.harr aR2 (by decide), h12, hbx', hax8 _ rfl]) rfl)
      fun t ⟨⟨hbx₁, hsi, hm⟩, k⟩ => ⟨h.mem hm k (by decide), (k.gpr (by decide)).trans h12, hsi, hbx₁⟩
  -- The second copy and the exit.
  exact two_taint [.rsi, .rbx, .r12, .rdi] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]) (by taint_decide)

/-- `main` leaks the same in runs that agree on the public data and `n`. -/
theorem pcMain_ct (M : Mont) : RelCT isa (Two VG.Proof.Bignum.X86_64.PcM) (Precompute.main M.mm) fun _ _ => True := by
  rw [pcMain_eq M]
  refine RelCT.seqs_append (by simp [pcLoad]) (by simp [r2Steps]) (RelCT.seq VG.Proof.Bignum.X86_64.pcLoad_ct ?_)
  exact RelCT.seqs_append (by simp [r2Steps]) (by simp [pcOut]) (RelCT.seq (VG.Proof.Bignum.X86_64.pcR2_ct M) VG.Proof.Bignum.X86_64.pcOut_ct)

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def PcC (p : VG.Proof.Bignum.X86_64.PcPub) (s : State) : Prop :=
  pcContract.pre s ∧ s.gpr .r8 = p.B ∧ (s.gpr .r9).toNat * 8 = p.Z ∧ (s.gpr .rcx).toNat = p.k ∧
    s.gpr .rdi = p.op ∧ s.gpr .rdx = p.np ∧ Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.nb

/-- After the entry and the modulus' check. -/
def PcC3 (p : VG.Proof.Bignum.X86_64.PcPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr t p.B p.Z ∧ t.gpr .rdi = p.B ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sOut) = p.op ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sN) = p.np ∧ Src t p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    (∀ i < 2 * p.w, InRegions t.wr (VG.Proof.Bignum.X86_64.off p.op (8 * i)) 8) ∧
    (∀ j < 16 * p.w, InRegions t.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ i < 16 * p.w, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (p.op + BitVec.ofNat 64 i)) ∧
    t.zf = some (Spec.Rsa.modulusValid p.N p.k)

/-- `vg_rsa_public_precompute` leaks the same in runs that agree on the public
data and `n`. -/
theorem pcCode_ct (M : Mont) : RelCT isa (Two VG.Proof.Bignum.X86_64.PcC) (Precompute.code M.mm) fun _ _ => True := by
  unfold Precompute.code
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.PcC3) [.r8, .rdx, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨-, a₁, -, c₁, -, d₁, -⟩ := h₁
    obtain ⟨-, a₂, -, c₂, -, d₂, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [d₁, d₂]
    · rw [← VG.Proof.Bignum.X86_64.ofNat_toNat64 (s₁.gpr .rcx), ← VG.Proof.Bignum.X86_64.ofNat_toNat64 (s₂.gpr .rcx), c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro ⟨B, Z, k, op, np, nb⟩ s ⟨hs, hB, hZ, hk, hop, hnp, hnb⟩
    have c := VG.Proof.Bignum.X86_64.pcCtx_of hs
    have hZ' := c.hZ
    have hk1 := c.hk1
    have hk2 := c.hk2
    have hn := c.hs.nowrap
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Bignum.X86_64.pcEntry_ok rfl fun i hi => c.hs.st (by omega))
      fun t₁ ⟨hdi, _, _, _, _, _, _, hO, hN, hK, ho₁, k₁⟩ => ?_
    have i₁ : InScr (s.gpr .r8) ((s.gpr .r9).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
    have hnb₁ := c.hnb.congrK i₁ k₁
    refine WP.mono (invalid_ok ((k₁.gpr (by decide)).trans rfl) (by rw [k₁.gpr (by decide), VG.Proof.Bignum.X86_64.ofNat_toNat64])
      hk1 hk2 (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi))
      (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
    have kk := k₁.trans k₂
    subst hB hZ hk hop hnp hnb
    exact ⟨c.hs.congr kk.2.2, (k₂.gpr (by decide)).trans hdi,
      show VG.Proof.Bignum.X86_64.slot (((s.gpr .rcx).toNat + 7) / 8) 8 ≤ (s.gpr .r9).toNat * 8 by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega, hk1, hk2,
      by rw [hm₂]; exact hO, by rw [hm₂, hK, VG.Proof.Bignum.X86_64.ofNat_toNat64], by rw [hm₂]; exact hN,
      c.hnb.congrK (by rw [hm₂]; exact i₁) kk, VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      fun i hi => by rw [kk.2.2]; exact c.hpw i hi, fun j hj => by rw [kk.2.2]; exact c.hpb j hj, c.hps, hz₂⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, z₁⟩ := h₁
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, z₂⟩ := h₂
    simp only [VG.X86_64.eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold Precompute.fail
    have pin : ∀ p t, (VG.Proof.Bignum.X86_64.PcC3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.B := fun p t h => h.1.2.1
    refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rsi = p.op ∧
        t.gpr .rcx = BitVec.ofNat 64 (16 * p.w) ∧ t.gpr .rdi = p.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨⟨hs, hdi, hZ, hk1, hk2, hO, hK, -⟩, -⟩
    have hn := hs.nowrap
    obtain ⟨g0, g8⟩ := VG.Proof.Bignum.X86_64.slot0_ge p.w
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 (16 * p.w)) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK,
        shr3_w p.k (by omega), VG.Proof.Bignum.X86_64.sixteen_w _ rfl]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hdi⟩
  · -- `main`.
    refine two_map id (fun p t ⟨⟨hs, hdi, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, hpw, _, hps, hz⟩, he⟩ =>
      ⟨hs, hdi, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, ?_, hpw, hps⟩) (VG.Proof.Bignum.X86_64.pcMain_ct M)
    simp only [VG.X86_64.eval, hz] at he; simpa using he

/-- The public data of a state. -/
def pcPubOf (s : State) : VG.Proof.Bignum.X86_64.PcPub :=
  ⟨s.gpr .r8, (s.gpr .r9).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx,
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩

/-- `vg_rsa_public_precompute` is constant time but for `n`. -/
theorem pcCode_constantTime (M : Mont) :
    ConstantTime isa pcContract.pre pcContract.pub (Precompute.code M.mm) := by
  refine RelCT.constantTime ((VG.Proof.Bignum.X86_64.pcCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨VG.Proof.Bignum.X86_64.pcPubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .r8 (by decide), by rw [r .r9 (by decide)]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), hn.symm⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubVerified`. -/
section

/-!
# `vg_rsa_public` on x86-64: verified against the shared contract

`pubContract` states the shared contract on the registers and the stack
(`public_implies`); with correctness (`code_correct`) and constant time
(`code_constantTime`), `code` is verified (`public_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting `pubContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6008`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x80
    else if a = 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The leak of `n` and `e`, as bytes, determines each when `n`'s length is
the same. -/
theorem leak_eq {a b c d : List Byte} (hl : a.length = c.length)
    (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat)) : a = c ∧ b = d := by
  have hi : (a ++ b) = (c ++ d) := List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h
  exact List.append_inj hi hl

theorem public_implies : pubContract.Implies (Spec.Rsa.publicContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Bignum.X86_64.pubContract, VG.Proof.Bignum.X86_64.stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Bignum.X86_64.pubContract, VG.Proof.Bignum.X86_64.stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Bignum.X86_64.pubContract, VG.Proof.Bignum.X86_64.stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Bignum.X86_64.pubContract, VG.Proof.Bignum.X86_64.stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Bignum.X86_64.pubContract, VG.Proof.Bignum.X86_64.stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hn, he⟩ := VG.Proof.Bignum.X86_64.leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Bignum.X86_64.pubContract, VG.Proof.Bignum.X86_64.stackArgs_four, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Bignum.X86_64.satState

theorem public_verified : Verified target VG.Impl.Bignum.X86_64.Public.code (Spec.Rsa.publicContract abi) :=
  Verified.of_correct VG.Proof.Bignum.X86_64.code_correct VG.Proof.Bignum.X86_64.code_constantTime VG.Proof.Bignum.X86_64.public_implies

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PcVerified`. -/
section

/-!
# `vg_rsa_public_precompute` on x86-64: verified against the shared contract

`pcContract` states the shared contract on the registers
(`precompute_implies`); with correctness (`pcCode_correct`) and constant
time (`pcCode_constantTime`), `Precompute.code` is verified
(`precompute_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pcContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def pcSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x4000 | .r9 => 1024
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 8192⟩]

theorem precompute_implies : pcContract.Implies (Spec.Rsa.publicPrecomputeContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, VG.Proof.Bignum.X86_64.pcContract, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, VG.Proof.Bignum.X86_64.pcContract, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, VG.Proof.Bignum.X86_64.pcContract, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, VG.Proof.Bignum.X86_64.pcContract, List.append_eq] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
    refine ⟨?_, List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, VG.Proof.Bignum.X86_64.pcContract, List.append_eq] [pcSatState] using VG.Proof.Bignum.X86_64.pcSatState

/-- `vg_rsa_public_precompute` with Montgomery multiplication `M`, given that
its code never loads MXCSR (which the registration file evaluates). -/
theorem precompute_verified (M : Mont) (hmx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Precompute.code M.mm) (Spec.Rsa.publicPrecomputeContract abi) :=
  Verified.of_correct (VG.Proof.Bignum.X86_64.pcCode_correct M hmx) (VG.Proof.Bignum.X86_64.pcCode_constantTime M) VG.Proof.Bignum.X86_64.precompute_implies

end VG.Proof.Bignum.X86_64

end
