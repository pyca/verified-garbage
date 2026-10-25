module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.First
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgRows
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Writes
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Key generation's noise from the first pairs' PRF outputs

`kgOut_ok`: `SamplePolyCBD₂` of buffer `N` into `ŝ[N]` or `ê[N - k]`,
transformed (`Kem16P.kgOut`). `noiseK_ok`: the six buffers the first two
pairs filled, then paired `PRF₂` for the rest of the noise, leave `ŝ` and `ê`
(`NK`) with `Â` as the pairs left it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (cw)
open VG.Impl.MlKem.AArch64.Noise (noiseOff)

variable {P : KemLay}

theorem kgTarget_eq (P : KemLay) (N : Nat) :
    Impl.MlKem.AArch64.Kem16P.kgTarget P N = Noise.outOff P true N := rfl

/-- `ŝ[N]` for `N < k`, `ê[N - k]` after. -/
abbrev kgPoly (P : KemLay) (s₀ : State) (N : Nat) : Poly :=
  if N < P.k then KPke.kgS P.params (dB s₀) N else KPke.kgE P.params (dB s₀) (N - P.k)

theorem kgPoly_eq (s₀ : State) (N : Nat) :
    kgPoly P s₀ N = ntt (samplePolyCBD 2 (prf 2 (KPke.kgSigma P.params (dB s₀)) (BitVec.ofNat 8 N))) := by
  unfold kgPoly
  split
  · rfl
  · rename_i h
    simp only [KPke.kgE, VG.Proof.MlKem.cbd, KemLay.params]
    rw [Nat.add_sub_cancel' (by omega_arith)]

/-- The polynomials of the noise lie between `NS + 1024` and the end of `scratch`, apart from
`TP`'s buffers. -/
theorem out_far (hw : P.Wf) (hr : Noise.Room P) {N : Nat} (hN : N < 2 * P.k) :
    NS + 1024 ≤ Noise.outOff P true N ∧ Noise.outOff P true N + 1024 ≤ P.scl ∧
      (Noise.outOff P true N + 1024 ≤ TP P ∨ SV P + 48 ≤ Noise.outOff P true N) ∧
      SH P ≤ Noise.outOff P true N := by
  have lo := Noise.outOff_low hw hr true N
  change KG.NS + 1024 ≤ _ at lo
  refine ⟨lo, Noise.outOff_fits hw hr true hN, ?_⟩
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have sv : SV P = TP P + 2048 := rfl
  unfold Noise.outOff
  split
  · rename_i h
    simp only [ite_true]
    have so : KG.sOff P N = SH P + 1024 * N := rfl
    rw [so]
    have := Nat.mul_le_mul_left 1024 (show N + 1 ≤ P.k by omega_arith)
    omega_arith
  · have := Noise.noise_past_kg hr (N - P.k)
    omega_arith

/-- **`kgOut`**: `SamplePolyCBD₂` of buffer `N` into its polynomial, transformed. -/
theorem kgOut_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (h : KB P s₀ s)
    (htr : Optimized.TransformTables s) {N : Nat} (hN6 : N < 6) (hN : N < 2 * P.k) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgOut P N) s fun t => KB P s₀ t ∧
      Frame [R (kA s₀) 3 (Noise.outOff P true N) 1024, R (kA s₀) 3 NS 1024] s.mem t.mem ∧
      t.gpr .x24 = s.gpr .x24 ∧ t.syms = s.syms ∧
      PolyIsW 16 t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true N))
        (ntt (samplePolyCBD 2 (bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128))) := by
  have hw := hp.wf
  obtain ⟨tN, tS, tB, -⟩ := out_far hw hr hN
  generalize ht : Noise.outOff P true N = T at tN tS tB
  have h3 := kL_le hw 3
  have hsv := hp.sv
  have sv : SV P = TP P + 2048 := rfl
  have kl3 : kL P 3 = P.scl := rfl
  have cst : SV P + 48 ≤ P.scl ∧ KG.NS + 1024 ≤ TP P := ⟨by omega_using [hsv, kl3], by lom⟩
  have t64 : T < 65536 := by omega_using [tS, h3, kl3]
  have hbo : TP P + 168 * N < 65536 := by omega_using [hsv, sv, h3, hN6]
  have fT : T + 1024 ≤ kL P 3 := by omega_using [tS, kl3]
  have fN : KG.NS + 1024 ≤ kL P 3 := by omega_using [cst, hsv, sv]
  have fB : TP P + 168 * N + 128 ≤ kL P 3 := by omega_using [hsv, sv, hN6]
  have dBT : (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint (R (kA s₀) 3 T 1024) :=
    sdisjK hp fB fT (by rcases tB with h | h <;> omega_arith)
  have dTN : (R (kA s₀) 3 T 1024).Disjoint (R (kA s₀) 3 KG.NS 1024) := sdisjK hp fT fN (.inr tN)
  have cT : Covers [R (kA s₀) 3 T 1024] s.wr := cov_w hp h (b := 3) (by decide) fT
  have cN : Covers [R (kA s₀) 3 KG.NS 1024] s.wr := cov_w hp h (b := 3) (by decide) fN
  have cB : Covers [R (kA s₀) 3 (TP P + 168 * N) 128] (s.rd ++ s.wr) := cov_r hp h (b := 3) (by decide) fB
  have sT := kb_disj hp (b := 3) (o := T) (l := 1024) (by decide) fT
    (.inr (by rcases tB with h | h <;> omega_arith)) (by decide)
  have sN := kb_disj hp (b := 3) (o := KG.NS) (l := 1024) (by decide) fN (.inr (.inr (by omega_arith))) (by decide)
  unfold Impl.MlKem.AArch64.Kem16P.kgOut
  rw [kgTarget_eq, ht]
  simp only [seqs, Impl.MlKem.AArch64.Kem16P.bufOff]
  have sample : WP isa (.seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 (TP P + 168 * N) ++
      Impl.MlKem.AArch64.ptrTo .x1 .x28 T)) Impl.MlKem.AArch64.Noise.cbdCall) s fun v =>
      Kept [R (kA s₀) 3 T 1024] s v ∧
      PolyIsW (cw true) v.mem (kA s₀ 3 + BitVec.ofNat 64 T)
        (samplePolyCBD 2 (bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128)) := by
    refine WP.seq (wp_ptrTo (by decide) hbo fun a ha ea => wp_ptrTo' (by decide) t64 fun u hu eu => ?_)
    have ou : Only [.x0, .x1] s u := (ha.trans hu).mono (by simp)
    have ku : Kept [R (kA s₀) 3 T 1024] s u := Kept.of_keep ou.keep ou.mem (by decide)
    exact cbdW_call (by rw [hu.get .x0 (by decide), ea, h.x28])
      (by rw [eu, ha.get .x28 (by decide), h.x28]) dBT
      (by rw [ou.rd, ou.wr]; exact Covers.cons (Covers.head cB) (Covers.right cT))
      (by rw [ou.wr]; exact cT)
      (fun v kv pv => ⟨ku.trans kv, by simpa only [ou.mem] using pv⟩)
  apply WP.assoc
  refine WP.seq (WP.mono_syms sample fun v ⟨kv, pv⟩ sv' => ?_)
  have kbv := h.call kv (fun r hr => by rw [List.mem_singleton.mp hr]; exact sT)
  have tv := htr.frame sv' kv.rd kv.wr kv.sp kv.frame cT
  have cv : Covers [polyRegion (kA s₀ 3 + BitVec.ofNat 64 T), polyRegion (kA s₀ 3 + BitVec.ofNat 64 KG.NS)] v.wr := by
    rw [kv.wr]; exact Covers.cons (Covers.head cT) (Covers.cons (Covers.head cN) Covers.nil)
  refine WP.mono_syms (Ntt16.W.nttAtWithW_ok t64 (by decide) (by rw [kbv.x28]) (by rw [kbv.x28])
    (dTN.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right
      (Region.sub_prefix (by decide : 512 ≤ 1024))) pv
    (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head cv))
      (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail cv))) Covers.nil))
    (tv.fast.ready cv)) fun t ⟨kt, pt⟩ st => ?_
  have kt' : Kept [R (kA s₀) 3 T 1024, R (kA s₀) 3 KG.NS 1024] v t := kt.sub fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
  refine ⟨kbv.call kt' fun r hr => ?_, (kv.frame.mono (by simp)).trans kt'.frame,
    (kt'.cs .x24 (by decide) (by decide)).trans (kv.cs .x24 (by decide) (by decide)), st.trans sv', pt⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sT
  · exact sN

/-- After `G`, the first two pairs and the first `j` polynomials of the noise. -/
structure NK (P : KemLay) (s₀ s : State) (j : Nat) (t : State) : Prop where
  c : CInvW P s₀ s.mem (s.gpr .x24) 4 t
  syms : t.syms = s.syms
  tt : Optimized.TransformTables t
  buf : ∀ N < 6, bytesAt t.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128 =
    bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128
  done : ∀ N < j, PolyIsW 16 t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true N)) (kgPoly P s₀ N)

/-- A region of `scratch` past `NS` and apart from `TP`'s buffers misses `σ`, `ρ`, `Â`, the
saved registers, the seed and the buffers. -/
theorem noise_regionK {s₀ : State} (hp : Pre P s₀) {o l : Nat} (hf : o + l ≤ kL P 3) (hNS : KG.NS ≤ o)
    (hm : o + l ≤ AH ∨ SH P ≤ o) (hb : o + l ≤ TP P ∨ SV P + 48 ≤ o) :
    ((R (kA s₀) 3 SB 32).Disjoint (R (kA s₀) 3 o l) ∧ (R (kA s₀) 3 SG 32).Disjoint (R (kA s₀) 3 o l) ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint (R (kA s₀) 3 o l)) ∧
    ((svR P s₀).Disjoint (R (kA s₀) 3 o l) ∧ (R (kA s₀) 0 0 64).Disjoint (R (kA s₀) 3 o l)) ∧
    ∀ N < 6, (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint (R (kA s₀) 3 o l) := by
  have hw := hp.wf
  have hsv := hp.sv
  have sv : SV P = TP P + 2048 := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have cst : SB + 32 ≤ SG ∧ SG + 32 ≤ KG.NS := by decide
  refine ⟨⟨sdisjK hp (by kl) hf (.inl (by omega_using [cst, hNS])),
    sdisjK hp (by kl) hf (.inl (by omega_using [cst, hNS])), sdisjK hp (by kl) hf (by omega_using [hm, sh])⟩,
    kb_disj hp (by decide) hf (.inr (by omega_using [hb, sv])) (by decide), fun N hN => ?_⟩
  exact sdisjK hp (by omega_using [hsv, sv, hN]) hf (by omega_using [hb, sv, hN, hm, tp, sh])

theorem NK.zero {s₀ s : State} (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s) : NK P s₀ s 0 s :=
  ⟨⟨H.b.kb, H.b.rho, H.b.sig, rfl, by have := Nat.mul_le_mul hk3 hk3; omega_arith,
    fun e he => ⟨H.b.red e he, rfl⟩⟩, rfl, H.tables.transforms, fun _ _ => rfl,
    fun N hN => absurd hN (Nat.not_lt_zero N)⟩

/-- `kgOut` keeps `NK`. -/
theorem kgOut_step {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) {j : Nat} (hj6 : j < 6)
    (hj : j < 2 * P.k) (hprf : PrfK P s₀ s.mem j) (H : NK P s₀ s j t) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgOut P j) t (NK P s₀ s (j + 1)) := by
  have hw := hp.wf
  refine WP.mono (kgOut_ok hp hr H.c.kb H.tt hj6 hj) fun u ⟨ku, fu, xu, su, pu⟩ => ?_
  obtain ⟨tN, tS, tB, tH⟩ := out_far hw hr hj
  have kl3 : kL P 3 = P.scl := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have fT : Noise.outOff P true j + 1024 ≤ kL P 3 := by omega_using [tS, kl3]
  have fN : KG.NS + 1024 ≤ kL P 3 := by kl
  have rT := noise_regionK hp fT (by omega_using [tN]) (.inr tH) tB
  have c0 : KG.NS + 1024 ≤ AH := by decide
  have rN := noise_regionK hp fN (Nat.le_refl _) (.inl (by decide)) (.inl (by omega_using [tp, sh, c0]))
  have far : ∀ r ∈ [R (kA s₀) 3 (Noise.outOff P true j) 1024, R (kA s₀) 3 KG.NS 1024],
      (((R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
        (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) ∧
      ((svR P s₀).Disjoint r ∧ (R (kA s₀) 0 0 64).Disjoint r) ∧
      ∀ N < 6, (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint r) := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact rT
    · exact rN
  have rdt : t.rd = s₀.rd := H.c.kb.rd
  have wrt : t.wr = s₀.wr := H.c.kb.wr
  refine ⟨H.c.frame ku xu fu fun r hr' => (far r hr').1, su.trans H.syms,
    H.tt.frame su (ku.rd.trans rdt.symm) (ku.wr.trans wrt.symm) (ku.sp.trans H.c.kb.sp.symm) fu
      (Covers.cons (Covers.head (cov_w hp H.c.kb (b := 3) (by decide) fT))
        (Covers.cons (Covers.head (cov_w hp H.c.kb (b := 3) (by decide) fN)) Covers.nil)),
    fun N hN => ?_, fun N hN => ?_⟩
  · rw [bytesAt_frame fu (fun r hr' => (far r hr').2.2 N hN) (by decide)]
    exact H.buf N hN
  · rcases (by omega_arith : N < j ∨ N = j) with hN | rfl
    · obtain ⟨tN', tS', -, -⟩ := out_far hw hr (N := N) (by omega_arith)
      have fT' : Noise.outOff P true N + 1024 ≤ kL P 3 := by omega_using [tS', kl3]
      have ord := Noise.outOff_order hw hr true hN
      refine polyIsW_frame_poly (w16 := true) fu (fun r hr' => ?_) (H.done N hN)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact sdisjK hp fT' fT (.inl ord)
      · exact sdisjK hp fT' fN (.inr tN')
    · rw [H.buf N hj6, hprf, ← kgPoly_eq] at pu
      exact pu

/-- The writes of a noise pair miss a region apart from its working space and outputs. -/
theorem writes_apartK {B : Addr} {n : Nat} {r : Region}
    (hs : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.scratchOff true), 2048⟩)
    (hn : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.nttOff true), 1024⟩)
    (ho : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.outOff P true n), 1024⟩)
    (ho' : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.outOff P true (n + 1)), 1024⟩) :
    ∀ q ∈ Noise.writes P true B n, r.Disjoint q := by
  intro q hq
  simp only [Noise.writes, Noise.pairWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (Offset.sub_base _ (d := 1800) (n := 48) (k := 2048) (by decide))
  · exact hs.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048))
  · exact hs.sub_right (Offset.sub_base _ (d := 400) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 528) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 1536) (n := 136) (k := 2048) (by decide))
  · exact ho
  · exact ho'
  · exact hn

/-- A noise pair (`Noise.noisePairWith`) for outputs `n` and `n + 1` keeps `NK`. -/
theorem pairK_step {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) {n : Nat} (hn : n + 1 < 2 * P.k)
    (H : NK P s₀ s n t) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW P true n) t (NK P s₀ s (n + 2)) := by
  have hw := hp.wf
  have kb := H.c.kb
  have kl3 : kL P 3 = P.scl := rfl
  have hc : Covers [⟨kA s₀ 3, P.scl⟩] t.wr := by
    simpa only [R, ptr_zero] using cov_w hp kb (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
  have lim := Noise.layout_limits hw true
  simp only [Noise.scratchOff, Noise.nttOff, Noise.seedOff, ite_true] at lim
  obtain ⟨oN, oS, oB, oH⟩ := out_far hw hr (N := n) (by omega_arith)
  obtain ⟨oN', oS', oB', oH'⟩ := out_far hw hr (N := n + 1) hn
  have fO : Noise.outOff P true n + 1024 ≤ kL P 3 := by omega_using [oS, kl3]
  have fO' : Noise.outOff P true (n + 1) + 1024 ≤ kL P 3 := by omega_using [oS', kl3]
  have fS : KG.SS + 2048 ≤ kL P 3 := by kl
  have fN : KG.NS + 1024 ≤ kL P 3 := by kl
  have cvs {o l : Nat} (h : o + l ≤ P.scl) := Noise.coversScratch hc h
  have rdy (m : Nat) (hm : m < 2 * P.k) :=
    H.tt.fast.ready (Noise.coversTwo (cvs (Noise.outOff_fits hw hr true hm)) (cvs (o := KG.NS) (l := 1024) (by omega_using [fN, kl3])))
  -- Every region apart from the pair's working space, `NS` and both outputs misses its writes.
  have away {r : Region} (h1 : r.Disjoint (R (kA s₀) 3 KG.SS 2048)) (h2 : r.Disjoint (R (kA s₀) 3 KG.NS 1024))
      (h3 : r.Disjoint (R (kA s₀) 3 (Noise.outOff P true n) 1024))
      (h4 : r.Disjoint (R (kA s₀) 3 (Noise.outOff P true (n + 1)) 1024)) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, r.Disjoint q :=
    writes_apartK (P := P) h1 h2 h3 h4
  have tfar (sym : String) (H' : List Nat) (tt : Optimized.TransformTable t sym H') :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (Region.mk (t.syms sym) 512).Disjoint q :=
    away (tt.apart (cov_w hp kb (b := 3) (by decide) fS)) (tt.apart (cov_w hp kb (b := 3) (by decide) fN))
      (tt.apart (cov_w hp kb (b := 3) (by decide) fO)) (tt.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have ffar : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (NttR.fastRegion t).Disjoint q :=
    away (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fS)) (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fN))
      (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fO)) (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have ifar : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (NttR.fastInvRegion t).Disjoint q :=
    away (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fS)) (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fN))
      (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fO)) (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have sc (o l : Nat) (hf : o + l ≤ kL P 3) (hs : o + l ≤ KG.SS) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 3 o l).Disjoint q :=
    away (sdisjK hp hf fS (.inl hs)) (sdisjK hp hf fN (.inl (by omega_using [hs, lim])))
      (sdisjK hp hf fO (.inl (by omega_using [hs, lim, oN]))) (sdisjK hp hf fO' (.inl (by omega_using [hs, lim, oN'])))
  have hi (o l : Nat) (hf : o + l ≤ kL P 3) (h1 : KG.NS + 1024 ≤ o)
      (h2 : o + l ≤ Noise.outOff P true n ∨ Noise.outOff P true n + 1024 ≤ o)
      (h3 : o + l ≤ Noise.outOff P true (n + 1) ∨ Noise.outOff P true (n + 1) + 1024 ≤ o) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 3 o l).Disjoint q :=
    away (sdisjK hp hf fS (.inr (by omega_using [h1, lim]))) (sdisjK hp hf fN (.inr h1))
      (sdisjK hp hf fO h2) (sdisjK hp hf fO' h3)
  refine WP.mono_syms (Noise.readonly_noisePair_layout (B := kA s₀ 3) hw hr true hn kb.x28 hc
    (rdy n (by omega_arith)) (rdy (n + 1) hn) ffar) fun u ⟨ku, pu, qu⟩ sy => ?_
  have sv : SV P = TP P + 2048 := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have hsv := hp.sv
  have cst : KG.SB + 32 ≤ KG.SG ∧ KG.SG + 32 ≤ KG.SS ∧ KG.NS + 1024 ≤ AH := by decide
  have seed0 : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 0 0 64).Disjoint q :=
    away (seed_disj hp (b := 3) (by decide) fS (by decide)) (seed_disj hp (b := 3) (by decide) fN (by decide))
      (seed_disj hp (b := 3) (by decide) fO (by decide)) (seed_disj hp (b := 3) (by decide) fO' (by decide))
  have kbu : KB P s₀ u := kb.call ku fun r hr' =>
    ⟨hi (SV P) 48 hsv (by omega_using [sv, tp, sh, cst]) (by omega_using [oB, oH, sv, tp])
        (by omega_using [oB', oH', sv, tp]) r hr', seed0 r hr'⟩
  have hsig : bytesAt t.mem (kA s₀ 3 + BitVec.ofNat 64 KG.SG) 32 = KPke.kgSigma P.params (dB s₀) := H.c.sig
  have samp {m : Nat} (hm : m < 2 * P.k) (h' : PolyIsW (cw true) u.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true m))
      (Noise.sampled t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.seedOff true)) m (Noise.transformed P true m))) :
      PolyIsW 16 u.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true m)) (kgPoly P s₀ m) := by
    rw [kgPoly_eq]
    simpa only [Noise.sampled, Noise.seedOff, Noise.transformed, Bool.true_or, ite_true, hsig, cw] using h'
  refine ⟨H.c.frame kbu (ku.cs .x24 (by decide) (by decide)) ku.frame fun r hr' =>
      ⟨sc KG.SB 32 (by kl) (by omega_using [cst]) r hr', sc KG.SG 32 (by kl) (by omega_using [cst]) r hr',
        hi AH (1024 * (P.k * P.k)) (by kl) (by omega_using [cst]) (by omega_using [oH, sh]) (by omega_using [oH', sh]) r hr'⟩,
    ?_, ?_, fun N hN => ?_, fun N hN => ?_⟩
  · rw [sy]; exact H.syms
  · exact H.tt.frameFar sy ku.rd ku.wr ku.sp ku.frame fun r hr' =>
      ⟨tfar _ _ H.tt.forward r hr', ifar r hr', ffar r hr'⟩
  · rw [bytesAt_frame ku.frame (hi (TP P + 168 * N) 128 (by omega_using [hsv, sv, hN]) (by omega_using [tp, sh, cst])
      (by omega_using [oB, oH, sv, tp, hN]) (by omega_using [oB', oH', sv, tp, hN])) (by decide)]
    exact H.buf N hN
  · rcases (by omega_arith : N < n ∨ N = n ∨ N = n + 1) with hN' | rfl | rfl
    · exact polyIsW_frame_poly (w16 := true) ku.frame (Noise.writes_old_far hw hr true (kA s₀ 3) hn hN') (H.done N hN')
    · exact samp (by omega_arith) pu
    · exact samp hn qu

/-- **The noise** from the first pairs' buffers, then paired `PRF₂` for the rest. -/
theorem noiseK_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s) :
    WPs (((List.range 6).map (Impl.MlKem.AArch64.Kem16P.kgOut P)) ++
      ((List.range (P.k - 3)).map fun i =>
        Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW P true (6 + 2 * i))) s
      (NK P s₀ s (2 * P.k)) := by
  refine WPs.append (WPs.mono (WPs.range (I := NK P s₀ s) (fun j hj t ht =>
    kgOut_step hp hr hj (by omega_arith) (H.prf j hj) ht) (NK.zero hk3 H)) fun t ht => ?_)
  have r := WPs.range (f := fun i => Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW P true (6 + 2 * i))
    (I := fun i => NK P s₀ s (6 + 2 * i)) (n := P.k - 3) (fun i hi u hu => by
      have st := pairK_step hp hr (n := 6 + 2 * i) (by omega_arith) hu
      rwa [show 6 + 2 * i + 2 = 6 + 2 * (i + 1) by omega_arith] at st) ht
  rwa [show 6 + 2 * (P.k - 3) = 2 * P.k by omega_arith] at r

/-- The noise as `KgRows` encodes `ŝ` from it. -/
theorem NK.encode {s₀ s t : State} (H : NK P s₀ s (2 * P.k) t) :
    EncodeInvW P s₀ s.mem t.mem (s.gpr .x24) 4 0 t := by
  refine ⟨H.c, fun j hj => ?_, fun j hj => ?_, fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _⟩
  · have d := H.done j (by omega_arith)
    simp only [kgPoly, ite_true, hj, Noise.outOff] at d
    exact d
  · have d := H.done (P.k + j) (by omega_arith)
    simp only [kgPoly, Noise.outOff, show ¬ P.k + j < P.k by omega_arith, ite_false, Nat.add_sub_cancel_left] at d
    exact d

end VG.Proof.MlKem.AArch64.KeyGen
