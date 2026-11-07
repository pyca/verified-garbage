module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.KS
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: p's arithmetic (`pArith_vp`), which the candidate's attempt uses apart from the power in
-- `Power`

/-! # DSA parameter search on RISC-V: p and `(p − 1) / q`

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/KSSetup.lean`, `KSLoad.lean`,
`KSStore.lean`, `KSDiv.lean` and `PArith.lean`). `ksEnter_vp`: the key working
space's registers (`ksRegs`); `ksSetup_vp`: every array zero but `[aOne] = 1`,
and the top word of every other array zero (`TopAll`), which the division's
divisor needs; `loadS_vp`: a claim on `scratch` into an array; `storeS_vp`:
an array's low octets into a claim; `divL_vp`: the division. `pArith`
(`pArith_vp`): from X and q in claims, by the division of X by q:
`p − 1 = X − X mod 2q` (`pm1_eq`) in array `aPm1`, `p` in `aP` and big-endian
at `sPBE`, `(p − 1) / q` in `aE` and big-endian at `sE`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Proof.Rsa.RISCV64.Keys (Ws arr num slot S opRegs)
open VG.Impl.Rsa.RISCV64.Keys (seqs sub3 sel copy bitOf orOne clrLow zeroArrays setOne load storeBytes)
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The arrays after the setup: all zero but `[aOne] = 1`. -/
abbrev A0 : Nat → Nat := KU (fun _ => 0) aOne 1

/-- Every array. -/
abbrev allArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem allArrs_lt : ∀ j ∈ allArrs, j < nArrs := by decide

/-- The top word of every array but `aOne` is zero. -/
abbrev TopAll (G : GP) (m : Mem) : Prop := ∀ j < nArrs, j ≠ aOne → word m G.KB (arr G.w j + 8 * G.w) = 0

/-- An address in a region apart from `⟨B, Z⟩` is at least `Z` past `B`. -/
theorem past_of_disjoint' {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ (a - B).toNat := by
  have := hd a ha
  simp only [Region.Contains] at this
  omega

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem lens_w {G : GP} (l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    16 ≤ G.w ∧ G.w ≤ 48 ∧ 8 * G.w = G.pLen ∧ S G.w = G.pLen + 16 := by
  simp only [GP.w, S]; rcases l with e | e | e <;> rw [e] <;> decide

/-- The key working space's registers. -/
theorem ksEnter_vp : VP (St G c X) (.block (ksRegs G.pLen)) (KSt G c X) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
    (Taint.ofRegs [.s6]) (.block (ksRegs G.pLen)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  have l := h.lens
  have ⟨w1, w2, w3, w4⟩ := lens_w l
  have kb := (lay_ok l).2.2.2.2
  have p16 : G.pLen + 16 < 2048 := by omega
  have p8 : G.pLen / 8 < 2048 := by omega
  simp only [ksRegs]
  refine scrB_ok (by decide) h.gi.s6 kb.1 (by rcases l with e | e | e <;> rw [e] <;> decide) fun s₁ k₁ m₁ sp₁ a₁ => ?_
  refine wp_li p16 fun s₂ u₂ => wp_li p8 fun t u => WP.block_nil ?_
  have K : Keep [.s11, .s10, .s9] s t := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u.other _ hr.2.2, u₂.other _ hr.2.1, k₁.gpr (by simpa using hr.1)],
    by rw [u.rd, u₂.rd, k₁.2.1], by rw [u.wr, u₂.wr, k₁.2.2]⟩
  refine ⟨⟨h.of_keep K (by rw [u.mem, u₂.mem, m₁]) (by rw [u.sp, u₂.sp, sp₁]), x⟩, ?_, ?_, ?_⟩
  · rw [u.gpr]
  · rw [u.other _ (by decide), u₂.gpr, w4]
  · rw [u.other _ (by decide), u₂.other _ (by decide), a₁]

/-- Every array zeroed, then `[aOne] = 1`. -/
theorem ksSetup_vp :
    VP (KSt G c X) ksSetup (fun σ t => KSt G { c with A := A0, live := allArrs } X σ t ∧ TopAll G t.mem) := by
  refine ks_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11]) ksSetup,
    by kernel_rfl⟩ (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have l := h.lens
  have ⟨w1, w2, w3, w4⟩ := lens_w l
  have nw := hw.nowrap
  unfold ksSetup
  rw [WP.seq_iff]
  refine WP.sp_eq (WP.mono (VG.Proof.Rsa.RISCV64.Keys.zeroArrays_ok hw (c := nArrs) (by decide) (by decide)
    (by decide)) fun t₁ ⟨ht₁, f₁, z, k₁⟩ sp₁ => ?_)
  refine WP.sp_eq (WP.mono (VG.Proof.Rsa.RISCV64.Keys.setOne_ok ht₁ (j := aOne) (by decide) (by decide))
    fun t ⟨ht, f₂, v₂, k₂⟩ sp₂ => ?_)
  have zv : ∀ j < nArrs, num t₁.mem G.KB G.w j = 0 := fun j hj => by
    have := VG.Proof.Rsa.RISCV64.Keys.wordsVal_zero_part (a := 0) (c := G.w) (z j hj) (by omega)
    simpa using this
  have zt : ∀ j < nArrs, word t₁.mem G.KB (arr G.w j + 8 * G.w) = 0 := fun j hj => by
    have := VG.Proof.Rsa.RISCV64.Keys.wordsVal_zero_part (a := G.w) (c := 1) (z j hj) (by omega)
    simp only [VG.Proof.Mont.wordsVal, Nat.mul_zero, Nat.add_zero] at this
    exact BitVec.eq_of_toNat_eq (by simpa using this)
  have F : KKeep G.KB G.w allArrs [] s.mem t.mem :=
    (f₁.mono (by intro j hj; simp only [List.mem_range] at hj; simp only [allArrs, List.mem_cons, List.not_mem_nil, or_false]; simp only [nArrs] at hj; omega)).trans (f₂.mono (by decide))
  have R : Keep (opRegs ++ opRegs) s t := k₁.trans k₂
  have fr := frame_of_outside (hw.frame_out F allArrs_lt (by simp))
  refine ⟨⟨⟨h.of_ks R (sp₂.trans sp₁) fr (fun j hj => ?_) allArrs_lt (fun d hd => ?_) h.kslOk,
    x⟩, kr.of_keep R⟩, fun j hj hne => ?_⟩
  · show num _ _ _ _ = KU (fun _ => 0) aOne 1 j
    have hj' := allArrs_lt j hj
    by_cases e : j = aOne
    · subst e; rw [KU_self, v₂, zv _ (by decide)]
    · rw [KU_ne _ _ e, f₂.num (by simpa using Ne.symm e) (by simp) (ht₁.fit64 hj'), zv _ hj']
  · have hk := h.kslOk d hd
    rw [f₂.slot hk.1 (by simp), f₁.slot hk.1 (by simp)]; exact h.ksl d hd
  · rw [f₂.word (j := j) (i := G.w) (by omega) (by simpa using Ne.symm hne) (by simp) (ht₁.fit64 hj)]
    exact zt j hj

/-- The taint analysis of a load, its source and length public. -/
abbrev CertL (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.RISCV64.taint
  (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1]) (load j .a0 .a1) hc).isSome = true

/-- Array `j`, zero, := the `n` bytes `bs` at `a0` (`a1 = n`), readable and
apart from the key working space; the other arrays' top words kept. -/
theorem loadAt_vp {j n : Nat} {P : Addr} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hn0 : 0 < n) (hnw : n ≤ 8 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < n, InRegions (s.rd ++ s.wr) (off P i) 1) ∧
      Region.Disjoint ⟨P, n⟩ G.rK ∧ P.toNat + n ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem P n = bs) :
    VP (fun σ s => (KSt G c X σ s ∧ TopAll G s.mem) ∧ s.gpr .a0 = P ∧ s.gpr .a1 = BitVec.ofNat 64 n)
      (load j .a0 .a1)
      (fun σ t => KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        TopAll G t.mem) := by
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.1.gi.s6, by rw [hs.1.1.1.1.gi.sp, ← hs.1.1.1.1.gi.hG]; rfl⟩)
    [.s9, .s10, .s11, .a0, .a1] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨⟨_, a⟩, _⟩, a0, a1⟩ ⟨⟨⟨_, b⟩, _⟩, b0, b1⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a.s9, b.s9]
      · rw [a.s10, b.s10]
      · rw [a.s11, b.s11]
      · rw [a0, b0]
      · rw [a1, b1]) fun σ s ⟨⟨⟨⟨h, x⟩, kr⟩, top⟩, p0, p1⟩ => ?_
  obtain ⟨hR, sep, fit, b⟩ := hsrc σ s ⟨h, x⟩
  have hw := h.ws kr
  have z : num s.mem G.KB G.w j = 0 := by rw [h.arrs j hjl, hj0]
  have hc : ∀ i < n, (⟨P, n⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine h.ksOp kr (js := [j]) (ds := []) (by simpa using hj) (by simp)
    (P := fun t => num t.mem G.KB G.w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P n) ∧
      Outside G.KB (arr G.w j) (8 * G.w) s.mem t.mem)
    ((VG.Proof.Rsa.RISCV64.Keys.load_ok hw hj (by decide) (by decide) p0 p1 hn0 hnw hR
      (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' sep (hc i hi)) (Nat.not_le.mpr hx)) z).mono
      fun t ⟨w, k, v, r, o⟩ => ⟨w, k, ⟨v, o⟩, r⟩)
    fun t k ⟨v, o⟩ R sp f => ?_
  have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by rw [v, b, VG.Proof.Dsa.decodeBE_os2ip]
  refine ⟨⟨⟨h.of_op R sp f hj k vw, x⟩, kr.of_keep R⟩, fun i hi hne => ?_⟩
  have fi := hw.fit64 hi
  by_cases e : i = j
  · subst e
    rw [o.word (.inr (Nat.le_refl _)) (by simp only [S] at fi; omega)]
    exact top i hi hne
  · rw [k.word (j := i) (i := G.w) (by omega) (by simpa using Ne.symm e) (by simp) fi]
    exact top i hi hne

/-- Array `j`, zero, := the bytes `bs` that a claim puts at byte `o` of `scratch`. -/
theorem loadS_vp {j o n : Nat} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hbs : (o, bs) ∈ c.cl) (hn : bs.length = n)
    (hn0 : 0 < n) (hnw : n ≤ 8 * G.w) (ho : o < 2048) (hn11 : n < 2048) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem) (loadS j o n)
      (fun σ t => KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        TopAll G t.mem) := by
  refine VP.seq (G := fun σ s => (KSt G c X σ s ∧ TopAll G s.mem) ∧ s.gpr .a0 = G.sa o ∧
      s.gpr .a1 = BitVec.ofNat 64 n)
    (VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.s6, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [scr .a0 o, .li .a1 n]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_)
    (loadAt_vp cert hj hjl hj0 hn0 hnw fun σ s ⟨h, x⟩ => ?_)
  · refine wp_addi ho fun s₁ u₁ => wp_li hn11 fun t u => WP.block_nil ?_
    have K : Keep [.a0, .a1] s t := ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u.other _ hr.2, u₁.other _ hr.1], by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩
    refine ⟨⟨⟨⟨h.of_keep K (by rw [u.mem, u₁.mem]) (by rw [u.sp, u₁.sp]), x⟩, kr.of_keep K⟩,
      by rw [u.mem, u₁.mem]; exact top⟩, ?_, ?_⟩
    · rw [u.other _ (by decide), u₁.gpr, h.gi.s6]
    · rw [u.gpr]
  · have gi := h.gi
    have big := gi.wBig
    have kb := gi.kBig
    have fit := gi.scrFit
    have ok := h.clOk _ hbs
    simp only [ClOk, hn] at ok
    have b := h.sb _ hbs
    simp only [hn] at b
    refine ⟨fun i hi => by rw [show off (G.sa o) i = G.sa (o + i) from GP.sa_add G o i]; exact gi.inRdWr (by omega),
      (gi.kdisj ok.2.1 ok.2.2).symm, ?_, b⟩
    rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The taint analysis of a store, its destination, length and mask public. -/
abbrev CertS (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.RISCV64.taint
  (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1, .t4]) (storeBytes j .a0 .a1) hc).isSome = true

theorem ofInt_m1 : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide

/-- The claim at byte `o` of `scratch` := `[j]`'s low `n` bytes, big-endian. -/
theorem storeS_vp {j o n : Nat} (cert : CertS j) (hj : j ∈ c.live) (hn0 : 0 < n) (hnw : n ≤ 8 * G.w)
    (ho11 : o < 2048) (hn11 : n < 2048) (hoc : ∀ σ s, St G c X σ s → ClOk G (o, List.replicate n 0))
    {cl' : Claims} (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart o n x) :
    VP (KSt G c X) (storeS j o n)
      (KSt G { c with cl := (o, Spec.Rsa.i2osp (c.A j % 256 ^ n) n) :: cl' } X) := by
  refine VP.seq (G := fun σ s => KSt G c X σ s ∧ s.gpr .a0 = G.sa o ∧ s.gpr .a1 = BitVec.ofNat 64 n ∧
      s.gpr .t4 = BitVec.allOnes 64)
    (VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.gi.s6, by rw [hs.1.1.gi.sp, ← hs.1.1.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
        (.block [scr .a0 o, .li .a1 n, .li .t4 (-1)]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_) ?_
  · refine wp_addi ho11 fun s₁ u₁ => wp_li hn11 fun s₂ u₂ => ?_
    refine WP.cons (exec_li (by decide)) (WP.block_nil ?_)
    have u₃ := Upd.write s₂ .t4 (BitVec.ofInt 64 (-1))
    have K : Keep [.a0, .a1, .t4] s (s₂.write .t4 (BitVec.ofInt 64 (-1))) := ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1],
      by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
    refine ⟨⟨⟨h.of_keep K (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.sp, u₂.sp, u₁.sp]), x⟩, kr.of_keep K⟩,
      ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.gi.s6]
    · rw [u₃.other _ (by decide), u₂.gpr]
    · rw [u₃.gpr, ofInt_m1]
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.s6, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩)
    [.s9, .s10, .s11, .a0, .a1, .t4] cert (fun σ₁ σ₂ s₁ s₂ ⟨⟨_, a⟩, a0, a1, a4⟩ ⟨⟨_, b⟩, b0, b1, b4⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [a.s9, b.s9]
      · rw [a.s10, b.s10]
      · rw [a.s11, b.s11]
      · rw [a0, b0]
      · rw [a1, b1]
      · rw [a4, b4]) fun σ s ⟨⟨⟨h, x⟩, kr⟩, p0, p1, p4⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hw := h.ws kr
  have hjN := h.liveOk j hj
  have ok := hoc σ s ⟨h, x⟩
  simp only [ClOk, List.length_replicate] at ok
  have va := h.arrs j hj
  have hsep : Region.Disjoint ⟨G.sa o, n⟩ G.rK := (gi.kdisj ok.2.1 ok.2.2).symm
  have hc : ∀ i < n, (⟨G.sa o, n⟩ : Region).Contains (off (G.sa o) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have sNat : (G.sa o).toNat = G.scr.toNat + o := by
    rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine WP.sp_eq (WP.mono (VG.Proof.Rsa.RISCV64.Keys.storeBytes_ok hw hjN (by decide) p0 p1 (by decide)
    (by decide) (by decide) (b := true) (by simpa using p4) hn0 hnw
    (fun i hi => by rw [show off (G.sa o) i = G.sa (o + i) from GP.sa_add G o i]; exact gi.inScr (by omega))
    (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' hsep (hc i hi)) (Nat.not_le.mpr hx))
    (by omega)) fun t ⟨_, bt, ot, kt⟩ sp => ⟨⟨?_, x⟩, kr.of_keep kt⟩)
  have bs : Spec.Rsa.bytesAt t.mem (G.sa o) n = Spec.Rsa.i2osp (c.A j % 256 ^ n) n := by
    rw [VG.Proof.Rsa.RISCV64.Keys.bytes_of_store hnw fun i hi => by rw [bt i hi]; rfl, va]
  refine h.of_scrs kt sp (os := [(o, n)]) (fun p hp => ?_)
    ((frame_of_outside ot).mono (by simp)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bs, by simp only [ClOk, VG.Proof.Rsa.i2osp_length]; omega⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

/-- The division `[q] := [q] / [d]`, `[r] := [q] mod [d]`, by a divisor of
`L` octets (in `a1`) whose top word is zero (`TopAll`). -/
theorem divL_vp {q r d L : Nat}
    (cert : ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6, .s9, .s10, .s11])
      (.seq (.block [.li .a1 L]) (VG.Impl.Rsa.RISCV64.Div.divL q r d .a1)) hc).isSome = true)
    (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hrd : r ≠ d) (hd1 : d ≠ aOne) (hL1 : 1 ≤ L) (hLw : L ≤ 8 * G.w) (hL11 : L < 2048)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (hpos : 0 < c.A d) (hDl : c.A d < 2 ^ (8 * L)) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem)
      (.seq (.block [.li .a1 L]) (VG.Impl.Rsa.RISCV64.Div.divL q r d .a1)) (KSt G (divCfg c q r d) X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_
  refine WP.seq (wp_li hL11 fun s₁ u₁ => WP.block_nil ?_)
  have K1 : Keep [.a1] s s₁ := ⟨fun r hr => u₁.other r (by simpa using hr), u₁.rd, u₁.wr⟩
  have h₁ := h.of_keep K1 u₁.mem u₁.sp
  have kr₁ := kr.of_keep K1
  have hw := h₁.ws kr₁
  have va := h₁.arrs q hqL
  have vd := h₁.arrs d hdL
  refine h₁.ksOp kr₁ (js := [q, r]) (ds := []) (ws := .s8 :: VG.Proof.Rsa.RISCV64.Keys.divRegs)
    (by simp [hq, hr]) (by simp)
    (P := fun u => num u.mem G.KB G.w q = c.A q / c.A d ∧ num u.mem G.KB G.w r = c.A q % c.A d)
    (WP.mono (VG.Proof.Rsa.RISCV64.Keys.divL_ok hw hq hr hd (by decide) hqr hqd hrd u₁.gpr hL1 hLw
      (by rw [u₁.mem]; exact top d hd hd1) (by rw [vd]; exact hDl))
      fun u ⟨w, k, R, _, v⟩ => by
        rw [va, vd] at v
        exact ⟨w, k, ⟨(v hpos).1, (v hpos).2.2.1⟩, R⟩)
    fun u k ⟨vq, vr⟩ R sp f => ⟨⟨?_, x⟩, kr₁.of_keep R⟩
  have l := h.lens
  refine h₁.of_ks R sp f (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk
  · show num u.mem G.KB G.w j = KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d) j
    by_cases ejr : j = r
    · subst ejr; rw [KU_self]; exact vr
    rw [KU_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [KU_self]; exact vq
    rw [KU_ne _ _ ejq]
    have jl : j ∈ c.live := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejq
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejr
      · exact hj
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl) <;> omega)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h₁.arrs j jl
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact hq
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr
    · exact h.liveOk j hj
  · rw [k.slot (h.kslOk e he).1 (by simp)]; exact h₁.ksl e he

end

/-! ## p and `(p − 1) / q` -/

/-- `X − X mod q`, less `q` for an odd quotient, is `X − X mod 2q`. -/
theorem pm1_eq (x q : Nat) :
    x - x % q - (if x / q % 2 = 0 then 0 else q) = 2 * q * (x / (2 * q)) := by
  have h1 := Nat.mod_add_div x q
  have h2 : x / (2 * q) = x / q / 2 := by rw [Nat.mul_comm, Nat.div_div_eq_div_mul]
  have h3 := Nat.mod_add_div (x / q) 2
  rw [h2]
  generalize x / q / 2 = a at h3 ⊢
  generalize x / q = b at h1 h3 ⊢
  have e : x - x % q = q * b := by omega_arith
  rw [e]
  have e2 : 2 * q * a = 2 * (q * a) := by rw [Nat.mul_assoc]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · simp only [h, ↓reduceIte]
    have : b = 2 * a := by omega_arith
    rw [this, Nat.mul_left_comm, e2]; omega_arith
  · simp only [show ¬ b % 2 = 0 by omega_arith, ↓reduceIte]
    have : b = 2 * a + 1 := by omega_arith
    rw [this, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, e2]; omega_arith

/-- The candidate p from X and q. -/
abbrev pVal (x q : Nat) : Nat := x + 1 - x % (2 * q)

/-- The arrays after `pArith`. -/
abbrev pA (x q : Nat) : Nat → Nat :=
  KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (pVal x q - 1)) aE ((pVal x q - 1) / q)) aP (pVal x q)

/-- The stage after `pArith`. -/
abbrev pOut (c : Cfg) (G : GP) (x q : Nat) (rest : Claims) : Cfg :=
  { c with
    cl := (sE, Spec.Rsa.i2osp ((pVal x q - 1) / q) (eBytes G.pLen G.qLen)) ::
      (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest
    A := pA x q
    live := [aE, aP, aPm1, aOne, aZero]
    kls := [] }

/-- Simplifies the arrays' values of a stage. -/
macro "arr_simp" : tactic => `(tactic| simp only [KU, divCfg, A0, aQt, aRm, aDv, aX, aT, aS, aPm1, aP, aE,
  aH, aOne, aZero, aTmp, slOdd, Nat.reduceEqDiff, ↓reduceIte])

/-- The arrays after the loads, the division and `p − 1`. -/
abbrev aL (x q : Nat) : Nat → Nat := KU (KU (KU A0 aQt x) aX x) aDv q
abbrev aD (x q : Nat) : Nat → Nat := KU (KU (aL x q) aQt (x / q)) aRm (x % q)
abbrev aM (x q : Nat) : Nat → Nat :=
  KU (KU (KU (fun _ => 0) aOne 1) aQt (x / q)) aPm1 (x - x % q - (if x / q % 2 = 0 then 0 else q))

theorem pVal_eq (x q : Nat) : pVal x q = 2 * q * (x / (2 * q)) + 1 := VG.Proof.Dsa.Generation.pReduction_quotient x q

theorem pVal_lt {x q K : Nat} (hK : 1 ≤ K) (hx : x < 2 ^ K) : pVal x q < 2 ^ K := by
  have le : 2 * q * (x / (2 * q)) ≤ x := Nat.mul_div_le x (2 * q)
  have odd : pVal x q % 2 = 1 := VG.Proof.Dsa.Generation.pReduction_odd x q
  have ev : 2 ^ K % 2 = 0 := by
    rw [show K = K - 1 + 1 by omega_arith, Nat.pow_succ]; simp
  rw [pVal_eq] at odd ⊢
  rcases Nat.lt_or_ge (2 * q * (x / (2 * q)) + 1) (2 ^ K) with h | h
  · exact h
  · have : 2 * q * (x / (2 * q)) + 1 = 2 ^ K := by omega_arith
    rw [this] at odd; omega_arith

/-- `(p − 1) / q` fits its `eBytes` octets. -/
theorem e_lt {x q P Q : Nat} (hx : x < 2 ^ (8 * P)) (hq : 2 ^ (8 * Q - 1) ≤ q) (hQ : 1 ≤ Q) (hQP : Q ≤ P) :
    (pVal x q - 1) / q < 2 ^ (8 * eBytes P Q) := by
  have hp := pVal_lt (q := q) (by omega_arith) hx
  have q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul q0).mpr ?_) (Nat.pow_le_pow_right (by decide)
    (show 8 * P - 8 * Q + 1 ≤ 8 * eBytes P Q by simp only [eBytes]; omega_arith))
  calc pVal x q - 1 < 2 ^ (8 * P) := by omega_arith
    _ = 2 ^ (8 * P - 8 * Q + 1) * 2 ^ (8 * Q - 1) := by rw [← Nat.pow_add]; congr 1; omega_arith
    _ ≤ 2 ^ (8 * P - 8 * Q + 1) * q := Nat.mul_le_mul_left _ hq

theorem qLen_of {G : GP} (l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32) := by
  simp only [GP.qLen, Spec.Dsa.generationQLen]; rcases l with e | e | e <;> rw [e] <;> decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The stages after the loads, the division and `p − 1`. -/
abbrev cL (c : Cfg) (x q : Nat) : Cfg := { c with A := aL x q, live := [aDv, aX, aQt, aOne, aZero] }
abbrev cD (c : Cfg) (x q : Nat) : Cfg :=
  { c with A := aD x q, live := [aQt, aRm, aDv, aX, aOne, aZero] }
abbrev cM (c : Cfg) (x q : Nat) : Cfg := { c with A := aM x q, live := [aPm1, aQt, aOne, aZero], kls := [] }

theorem pLoads_vp {xb qb : List Byte} (l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen) :
    VP (St G c X) (seqs [.block (ksRegs G.pLen), ksSetup, loadS aQt sX G.pLen,
        loadS aX sX G.pLen, loadS aDv sQ G.qLen])
      (fun σ s => KSt G (cL c (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb)) X σ s ∧ TopAll G s.mem) := by
  have ⟨w1, w2, w3, w4⟩ := lens_w l
  have lq := qLen_of l
  refine VP.seq ksEnter_vp (VP.seq ksSetup_vp ?_)
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1])
    (load aQt .a0 .a1), by kernel_rfl⟩ (by decide) (by simp [aQt]) rfl (by exact hx) hxl (by omega) (by omega)
    (by decide) (by omega)) ?_
  refine VP.seq (loadS_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1])
    (load aX .a0 .a1), by kernel_rfl⟩ (by decide) (by simp [aX]) rfl (by exact hx) hxl (by omega) (by omega)
    (by decide) (by omega)) ?_
  refine (loadS_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1])
    (load aDv .a0 .a1), by kernel_rfl⟩ (by decide) (by simp [aDv]) rfl (by exact hqc) hql (by omega)
    (by omega) (by decide) (by omega)).mono (fun _ _ h => h) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ⟨⟨⟨h.mono
      (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨?_, rfl⟩) (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩, top⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [aDv, aX, aQt, aOne, aZero]

theorem pDivide_vp {x q : Nat} (l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hpos : 0 < q)
    (hq : q < 2 ^ (8 * G.qLen)) :
    VP (fun σ s => KSt G (cL c x q) X σ s ∧ TopAll G s.mem)
      (.seq (.block [.li .a1 G.qLen]) (VG.Impl.Rsa.RISCV64.Div.divL aQt aRm aDv .a1))
      (KSt G (cD c x q) X) := by
  have ⟨w1, w2, w3, w4⟩ := lens_w l
  have lq := qLen_of l
  refine (divL_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (.seq (.block [.li .a1 G.qLen]) (VG.Impl.Rsa.RISCV64.Div.divL aQt aRm aDv .a1)), by kernel_rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    (by omega) (by simp) (by simp) (by arr_simp; exact hpos) (by arr_simp; exact hq)).mono (fun _ _ h => h)
    fun σ s ⟨⟨h, x⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ?_)
      (fun d hd => ⟨hd, rfl⟩), x⟩, kr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [aQt, aRm, aDv, aX, aOne, aZero], by arr_simp⟩

theorem pPm1_vp {x q : Nat} :
    VP (KSt G (cD c x q) X)
      (seqs [sub3 aT aX aRm, .block (bitOf slOdd aQt), sel aS aZero aDv slOdd, sub3 aPm1 aT aS])
      (KSt G (cM c x q) X) := by
  refine VP.seq (sub3_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (sub3 aT aX aRm), by kernel_rfl⟩ (by decide) (by simp [aX]) (by simp [aRm]) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (.block (bitOf slOdd aQt)), by kernel_rfl⟩ (by simp [aQt]) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (sel aS aZero aDv slOdd), by kernel_rfl⟩ (by decide) (by simp [aZero]) (by simp [aDv]) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (sub3 aPm1 aT aS), by kernel_rfl⟩ (by decide) (by simp [aT]) (by simp [aS]) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        have h1 := Nat.mod_add_div x q
        have h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        have h3 := Nat.mul_le_mul_left q h2
        omega_arith)).mono (fun _ _ h => h) fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by simp [aPm1, aQt, aOne, aZero], by arr_simp⟩

theorem pTail_vp {x q : Nat} (hq : 2 ^ (8 * G.qLen - 1) ≤ q) (l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (hx : x < 2 ^ (8 * G.pLen)) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y ∧ Apart sE (eBytes G.pLen G.qLen) y) :
    VP (KSt G (cM c x q) X)
      (seqs [copy aP aPm1, .block (orOne aP), copy aE aQt, .block (clrLow aE),
        storeS aP sPBE G.pLen, storeS aE sE (eBytes G.pLen G.qLen)])
      (KSt G (pOut c G x q rest) X) := by
  have ⟨w1, w2, w3, w4⟩ := lens_w l
  have lq := qLen_of l
  have q0 : 0 < q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hq
  have pm := pm1_eq x q
  have pv := pVal_eq x q
  have plt := pVal_lt (q := q) (by omega_arith) hx
  have elt := e_lt (P := G.pLen) (Q := G.qLen) hx hq (by omega_arith) (by omega_arith)
  have hP : (x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2 * 2 + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide), Nat.mul_comm]
  have hE : x / q / 2 * 2 = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x q0, Nat.div_div_eq_div_mul, Nat.mul_comm q 2,
      Nat.mul_comm]
  have hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega_arith
  have nE : sE = 1344 := rfl
  have nP : sPBE = 960 := rfl
  have nH : hEnd = 280 := rfl
  have hkB : sE + G.pLen ≤ kB G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have eB : eBytes G.pLen G.qLen ≤ G.pLen := by simp only [eBytes]; omega_arith
  have p256 : (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) := by rw [Nat.pow_mul]
  have e256 : (256 : Nat) ^ eBytes G.pLen G.qLen = 2 ^ (8 * eBytes G.pLen G.qLen) := by rw [Nat.pow_mul]
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (copy aP aPm1), by kernel_rfl⟩ (by decide) (by simp [aPm1]) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (.block (orOne aP)), by kernel_rfl⟩ (by simp [aP])) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (copy aE aQt), by kernel_rfl⟩ (by decide) (by simp [aQt]) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11])
    (.block (clrLow aE)), by kernel_rfl⟩ (by simp [aE])) ?_
  refine VP.seq (storeS_vp (o := sPBE) (n := G.pLen) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
    (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1, .t4]) (storeBytes aP .a0 .a1), by kernel_rfl⟩
    (by simp [aP]) (by omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega_arith)
    (cl' := rest) fun y hy => ⟨(hrest y hy).1, (hrest y hy).2.1⟩) ?_
  refine (storeS_vp (o := sE) (n := eBytes G.pLen G.qLen) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
    (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1, .t4]) (storeBytes aE .a0 .a1), by kernel_rfl⟩
    (by simp [aE]) (by simp only [eBytes]; omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (fun σ s ⟨h, _⟩ => by have := h.gi.wBig; have := h.gi.kBig; simp only [ClOk, List.length_replicate]; omega_arith)
    (cl' := (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest) fun y hy => ?_).mono (fun _ _ h => h)
    fun σ s ⟨⟨h, xx⟩, kr⟩ => ⟨⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ?_)
      (fun d hd => absurd hd (by simp)), xx⟩, kr⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine ⟨List.mem_cons.mpr (.inl ?_), ?_⟩
      · arr_simp
        rw [hP, p256, Nat.mod_eq_of_lt plt]
      · simp only [Apart, VG.Proof.Rsa.i2osp_length]; omega_arith
    · exact ⟨List.mem_cons_of_mem _ hy, (hrest y hy).2.2⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine List.mem_cons.mpr (.inl ?_)
      arr_simp
      rw [hE, e256, Nat.mod_eq_of_lt elt]
    · exact List.mem_cons_of_mem _ hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> refine ⟨by simp [aE, aP, aPm1, aOne, aQt, aZero], ?_⟩ <;> arr_simp
    · exact hE
    · exact hP
    · exact hM

/-- p and `(p − 1) / q` from X and q. -/
theorem pArith_vp {xb qb : List Byte} (l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen)
    (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE qb) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y ∧ Apart sE (eBytes G.pLen G.qLen) y) :
    VP (St G c X) (pArith G.pLen G.qLen)
      (KSt G (pOut c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb) rest) X) := by
  have hxlt : Spec.Dsa.decodeBE xb < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt xb
    rwa [hxl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have hqlt : Spec.Dsa.decodeBE qb < 2 ^ (8 * G.qLen) := by
    have := VG.Proof.Dsa.decodeBE_lt qb
    rwa [hql, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have hpos : 0 < Spec.Dsa.decodeBE qb := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  exact VP.seq (pLoads_vp l hx hxl hqc hql) (VP.seq (pDivide_vp l hpos hqlt)
    (VP.seq pPm1_vp (pTail_vp hqlo l hxlt hrest)))

end

end VG.Proof.Dsa.RISCV64.PSearch
