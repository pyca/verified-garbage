module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Base
public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
public import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkInline16
import VerifiedGarbage.Proof.MlKem.X86_64.Kg16Tail
import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import Mathlib.Tactic.Conv

/-!
# ML-KEM-768 on x86-64: key generation hashing `ek` while it samples `Â`, the rows

The fragment that samples three entries of `Â` while the sponge of `H`
absorbs `m` blocks (`sampleHAtM16_ok`, as `sampleHAt16_ok`), and the rows of
`kemKeyGenH16`: the fragment of row `i` (`frag_ok`), which absorbs the
blocks of `pad(ek)` that the rows before it wrote (`hb_eq`, `habs_take`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- What the fragment absorbing `m` blocks leaves. -/
structure SHPostM16 (m oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all3_16 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f
  hs : stateAt s'.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS) =
    SH.habs (stateAt s.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS))
      (fun i => bytesAt s.mem (pa s (sc oz) + BitVec.ofNat 64 (Sample4.oHB + 136 * i)) 136) m

theorem SHPostM16.b {m oa oz : Nat} {s s' : State} (h : SHPostM16 m oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem shPreM16 (m : Nat) {oa oz : Nat} {s s1 : State} (h : SHH16 oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    (sampleHMKW true m).pre (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have := shPre16 h hv k
  rw [sampleHKW_eq] at this
  exact this

/-- The fragment absorbing `m` blocks inlined, on the seeds at `scratch`, to the polynomials from `sc oa`. -/
theorem sampleHAtM16_ok {m : Nat} {b : Prog isa} (hb : BatchHMOk16 m b) {oa oz : Nat} {s : State}
    (h : SHH16 oa oz s) : WP isa (Encaps.sampleHAt b (sc oa) (sc oz)) s (SHPostM16 m oa oz s) := by
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hc : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s1.rd ++ s1.wr) := by
    rw [k.2.1, k.2.2]; exact h.c
  have hw : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.wr := by rw [k.2.2]; exact h.w
  refine WP.seq (WP.mono (WP.inline hb.ok (shPreM16 m h hv k) hc hw (Q := fun s2 => s2.rd = s1.rd ∧ s2.wr = s1.wr ∧
      abiPreserved s1 s2 ∧ Frame [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.mem s2.mem ∧
      (sampleHMKW true m).post (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩])
        (s2.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]))
    (fun s2 hrd hwr habi hf _ hpost => ⟨hrd, hwr, habi, hf, hpost⟩) hb.noCalls) fun s2 ⟨hrd, hwr, habi, hf, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleHMKW, State.withRegions_gpr, State.withRegions_mem, hv.1, hv.2.1, hv.2.2, hm] at hpost
  obtain ⟨hax, hres, hhs⟩ := hpost
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := habi.1
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm]
    exact hf.mono fun r hr => List.mem_append_left _ hr
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hax]
  · rw [hm3]; exact hres j hj f hf
  · rw [hm3]; exact hhs

/-- What the fragment computing two outputs of `PRF₂` leaves. -/
structure SHPostP16 (oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all3_16 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f
  pout : ∀ N < 2, bytesAt s'.mem (pa s (sc oz) + BitVec.ofNat 64 (Sample4.oPO + 128 * N)) 128 =
    prf 2 (bytesAt s.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oPS) 32) (BitVec.ofNat 8 N)

theorem SHPostP16.b {oa oz : Nat} {s s' : State} (h : SHPostP16 oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The fragment computing `PRF₂(σ, 0)` and `PRF₂(σ, 1)` inlined, on the seeds
at `scratch`, to the polynomials from `sc oa`. -/
theorem sampleHAtP16_ok {b : Prog isa} (hb : BatchPOk16 b) {oa oz : Nat} {s : State}
    (h : SHH16 oa oz s) : WP isa (Encaps.sampleHAt b (sc oa) (sc oz)) s (SHPostP16 oa oz s) := by
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hc : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s1.rd ++ s1.wr) := by
    rw [k.2.1, k.2.2]; exact h.c
  have hw : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.wr := by rw [k.2.2]; exact h.w
  refine WP.seq (WP.mono (WP.inline hb.ok (shPre16 h hv k) hc hw (Q := fun s2 => s2.rd = s1.rd ∧ s2.wr = s1.wr ∧
      abiPreserved s1 s2 ∧ Frame [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.mem s2.mem ∧
      samplePKW.post (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩])
        (s2.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]))
    (fun s2 hrd hwr habi hf _ hpost => ⟨hrd, hwr, habi, hf, hpost⟩) hb.noCalls) fun s2 ⟨hrd, hwr, habi, hf, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [samplePKW, SH.Post3, State.withRegions_gpr, State.withRegions_mem, hv.1, hv.2.1, hv.2.2, hm] at hpost
  obtain ⟨⟨hax, hres⟩, hpo⟩ := hpost
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := habi.1
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm]
    exact hf.mono fun r hr => List.mem_append_left _ hr
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hax]
  · rw [hm3]; exact hres j hj f hf
  · rw [hm3]; exact hpo

namespace KeyGenH

open KeyGen KeyGen16 VG.Impl.MlKem.X86_64.Top16 VG.Impl.MlKem.X86_64.KeyGenH16

theorem hm_spec : ∀ i < 3, (hm i).2 = hAbs i ∧ (hm i).2 + (hm i).1 = hAbs (i + 1) ∧
    136 * hAbs (i + 1) ≤ 384 * i ∧ (hm i).1 ≤ 3 := by decide

/-- Absorbing whole blocks of `E` from the state before block `t`. -/
theorem habs_take (E : List Byte) (t : Nat) :
    ∀ n, 136 * (t + n) ≤ E.length →
      SH.habs (HSponge.hstate E t) (fun j => (E.drop (136 * (t + j))).take 136) n = HSponge.hstate E (t + n)
  | 0, _ => rfl
  | n + 1, h => by
    show Spec.Sha3.keccakF (Proof.Sha3.xorAt (SH.habs _ _ n) 0 _) = _
    rw [habs_take E t n (by omega), ← Nat.add_assoc]
    exact HSponge.hstate_full (by omega)

/-- The first `i` rows of `ek`. -/
theorem ekK_take (L : Kem) (σ : State) (hk : L.k = 3) {i : Nat} (hi : i ≤ 3) :
    (ekK L σ).take (384 * i) = KPke.catK (tRow L σ) i := by
  have hl : ∀ j, (tRow L σ j).length = 384 := fun _ => encode12_length _
  have e3 : KPke.catK (tRow L σ) L.p.k = KPke.catK (tRow L σ) i ++
      ((List.range (3 - i)).map (i + ·)).flatMap (tRow L σ) := by
    rw [show L.p.k = i + (3 - i) by rw [show L.p.k = 3 from hk]; omega, KPke.catK_eq, KPke.catK_eq,
      List.range_add, List.flatMap_append]
  have hli : (KPke.catK (tRow L σ) i).length = 384 * i := KPke.catK_length hl i
  show (KPke.ekPKE L.p (aHat (rhoK L σ)) (kgD σ)).take (384 * i) = _
  rw [KPke.ekPKE, show (fun j => encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) j)) = tRow L σ from rfl, e3,
    List.append_assoc, List.take_left' hli]

theorem pa_add (s : State) (r : Reg) (o d : Nat) : pa s (r, o) + BitVec.ofNat 64 d = pa s (r, o + d) := by
  simp only [pa]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ekK_length {L : Kem} (σ : State) : (ekK L σ).length = L.ekLen := KPke.ekPKE_length _ _

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The blocks of `ek` that the fragment of row `i` absorbs, to `HB`. -/
theorem cp_ok {i : Nat} (hi : i < 3) {s : State} (h : KH K σ i (3 * i) s) :
    WP isa (if (hm i).1 = 0 then .block [] else copy (sc (Encaps16.oHB K)) (.r12, 136 * (hm i).2) (136 * (hm i).1)) s
      fun s' => KH K σ i (3 * i) s' ∧ (allOk K.L.k (rhoK K.L σ) (3 * i) →
        bytesAt s'.mem (pa s' (hbP K)) (136 * (hm i).1) = ((ekK K.L σ).drop (136 * (hm i).2)).take (136 * (hm i).1)) := by
  obtain ⟨e2, e21, hb, hm3⟩ := hm_spec i hi
  by_cases h0 : (hm i).1 = 0
  · rw [ite_eq_left h0]
    exact WP.block_nil ⟨h, fun _ => by rw [h0]; simp [bytesAt]⟩
  · rw [ite_eq_right h0]
    have hc := W.cp i hi
    simp only [cpChk, Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at hc
    obtain ⟨hcc, hk⟩ := hc
    obtain ⟨hkc, hr⟩ := keepAll_spec hk
    have L₀ := h.kc.lay W.toKgWfB hp
    refine WP.mono (copy_okL L₀ (show Reg.r12 ≠ .rdi by decide) hcc) fun s' ⟨hP, hb'⟩ =>
      ⟨h.keep W hp hP.b (hP.cs .r15 (by decide)) hkc (fun r hr' => hr r (List.mem_append_left _ hr'))
        (fun _ => hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _))), fun ho => ?_⟩
    rw [hP.pa rbx_cs, hb']
    have hcat : bytesAt s.mem (pa s (.r12, 0)) (384 * i) = KPke.catK (tRow K.L σ) i :=
      bytesAt_catK s.mem s .r12 0 384 _ i fun j hj => by rw [Nat.zero_add]; exact (h.ok ho).1 j hj
    rw [← ekK_take K.L σ W.k3 (by omega)] at hcat
    have := bytesAt_slice s.mem (pa s (.r12, 0)) (k := 136 * (hm i).2) (c := 136 * (hm i).1) (len := 384 * i)
      (by omega)
    rw [hcat, List.drop_take, List.take_take, Nat.min_eq_left (by omega), pa_add, Nat.zero_add] at this
    exact this.symm

/-- While the seeds of the fragment of row `i` are written. -/
structure SI (K : Kem16) (σ : State) (i J : Nat) (s : State) : Prop where
  kh : KH K σ i (3 * i) s
  sd : SeedsIs (rhoK K.L σ) K.L.k (3 * i) J s
  hb : allOk K.L.k (rhoK K.L σ) (3 * i) →
    bytesAt s.mem (pa s (hbP K)) (136 * (hm i).1) = ((ekK K.L σ).drop (136 * (hm i).2)).take (136 * (hm i).1)

theorem seedI_ok {i : Nat} (hi : i < 3) {J : Nat} (hJ : J < 4) {s : State} (h : SI K σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (SI K σ i (J + 1)) := by
  have hsd := W.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨hs, hk⟩ := hsd J hJ
  obtain ⟨hkc, hr⟩ := keepAll_spec hk
  have L₀ := h.kh.kc.lay W.toKgWfB hp
  refine WP.mono (seed_step L₀ (kgB_bases K.L) (by omega) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.kh.keep W hp hP.b (hP.cs .r15 (by decide)) hkc (fun r hr' => hr r (List.mem_append_left _ hr'))
      (fun _ => hr (hsP K, 200) (List.mem_append_right _ (List.mem_cons_self ..))), hS, fun ho => ?_⟩
  rw [L₀.keepBytes hP.b (hr (hbP K, 136 * (hm i).1) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))]
  exact h.hb ho

end

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The sampling of the fragment of row `i`: entries `3i` to `3i + 2` of `Â`,
and the blocks of `ek` absorbed. -/
theorem sm_ok (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {i : Nat} (hi : i < 3)
    {s : State} (h : SI K σ i 4 s) :
    WP isa (Encaps.sampleHAt (b (hm i).1) (sc (K.oA + 512 * (3 * i))) (sc K.oW)) s (KH K σ i (3 * i + 3)) := by
  obtain ⟨e2, e21, hbd, hm3⟩ := hm_spec i hi
  have hsm := W.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  obtain ⟨hkc, hr⟩ := keepAll_spec hsm.2
  have L₅ := h.kh.kc.lay W.toKgWfB hp
  have hE : (ekK K.L σ).length = 1184 := by rw [ekK_length, W.ek]
  refine WP.mono (sampleHAtM16_ok (v.batchHM16 b hb _ hm3) (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have ha : ∀ e' < 3 * i, keepB (kgR ++ kgW K.L) (smW K i) (aP K e') 512 = true := fun e' he' =>
    hr (aP K e', 512) (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))
  refine KH.of (h.kh.ks.keep W hp (Nat.le_refl _) h₆.b hkc fun r hr' =>
    hr r (List.mem_append_left _ (List.mem_append_left _ hr'))) ?_ fun ho => ?_
  · refine EkF16.MatB16.three (K := K) h.kh.mat L₅ h₆.b ha ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq h.sd (k := k) (by omega))]
    · have := h₆.res t ht f (by rw [seed4_eq h.sd (by omega)]; exact hf)
      rwa [poly4W, pBytes_true, pa_off] at this
  · have ho' := (EkF.allOk_add3.1 ho).1
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [L₅.keepBytes h₆.b (hr (ekP j, 384) (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))]
      exact (h.kh.ok ho').1 j hj
    · have eHS : ∀ t : State, pa t (hsP K) = pa t (sc K.oW) + BitVec.ofNat 64 Sample4.oHS := fun t => by
        rw [pa_off]; rfl
      have e0 := (h.kh.ok ho').2
      rw [show 3 * i / 3 = i by omega, eHS] at e0
      rw [h₆.b.pa rbx_bases, eHS, h₆.hs, e0, EkF.habs_congr _ (hm i).1
        (g := fun j => ((ekK K.L σ).drop (136 * ((hm i).2 + j))).take 136) fun j hj => ?_, ← e2,
        habs_take _ _ _ (by omega), e21, show (3 * i + 3) / 3 = i + 1 by omega]
      have hb := h.hb ho'
      have := bytesAt_slice s.mem (pa s (hbP K)) (k := 136 * j) (c := 136) (len := 136 * (hm i).1) (by omega)
      rw [hb, List.drop_take, List.take_take, Nat.min_eq_left (by omega), List.drop_drop, pa_off,
        show Encaps16.oHB K + 136 * j = K.oW + (Sample4.oHB + 136 * j) by simp only [Encaps16.oHB]; omega,
        ← pa_off, show 136 * (hm i).2 + 136 * j = 136 * ((hm i).2 + j) by omega] at this
      exact this.symm

end

/-- An entry of `Â` among the first `e`, once they all succeeded. -/
theorem aHat_part {k : Nat} {ρ : List Byte} {e : Nat} (h : allOk k ρ e) {e' : Nat} (he : e' < e) :
    sampleNTT minIterations (matSeed ρ (e' / k) (e' % k)) = some (aHat ρ (e' / k) (e' % k)) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (h e' he)
  rw [aHat, hf]; rfl

theorem r15_ok {k : Nat} {ρ : List Byte} {e : Nat} {r : BitVec 64} (h : r = if allOk k ρ e then 1 else 0)
    (hne : r.setWidth 32 ≠ 0) : allOk k ρ e := by
  by_contra ho
  rw [ifn ho] at h
  exact hne (by rw [h]; rfl)

theorem r15_no {k : Nat} {ρ : List Byte} {e : Nat} {r : BitVec 64} (h : r = if allOk k ρ e then 1 else 0)
    (he : r.setWidth 32 = 0) : ¬ allOk k ρ e := by
  intro ho
  rw [ifp ho] at h
  rw [h] at he
  exact absurd he (by decide)

/-- With an entry failed, the rows are not needed. -/
theorem KH.skip {K : Kem16} {σ s : State} {i e : Nat} (h : KH K σ i e s) (ho : ¬ allOk K.L.k (rhoK K.L σ) e) :
    KH K σ (i + 1) e s :=
  ⟨h.kc, h.rho, h.sb, h.sh, fun j hj hij => h.eh j hj (by omega), h.dk, h.mat, fun h' => absurd h' ho⟩

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- Row `i` of `t̂`, encoded to `ek`. -/
theorem row_ok (hK : KgRowsOk K.L) {i : Nat} (hi : i < 3) {s : State} (h : KH K σ i (3 * i + 3) s)
    (ho : allOk K.L.k (rhoK K.L σ) (3 * i + 3)) : WP isa (rowAt K i) s (KH K σ (i + 1) (3 * i + 3)) := by
  have k3 := W.k3
  have hc := W.rw i hi
  simp only [rwChk, Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have hkr : krChk (kgB K.L) (kgW K.L) K.L.k (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) = true := by
    rw [k3]; exact hc.1
  have L₀ := h.kc.lay W.toKgWfB hp
  have he : ∀ j < 3, sampleNTT minIterations (matSeed (rhoK K.L σ) i j) = some (aHat (rhoK K.L σ) i j) := by
    intro j hj
    have := aHat_part ho (e' := 3 * i + j) (by omega)
    rwa [k3, show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
  have hA : ∀ j < 3, PolyIsW 16 s.mem (pa s (sc (K.oA + 512 * (3 * i) + 512 * j))) (aHat (rhoK K.L σ) i j) := by
    intro j hj
    have := h.mat.mat (3 * i + j) (by omega) _ (by
      rw [k3, show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega]; exact he j hj)
    rwa [show K.oA + 512 * (3 * i + j) = K.oA + 512 * (3 * i) + 512 * j by omega] at this
  have redA : VecReducedW 16 s.mem (pa s (aP K (3 * i))) K.L.k := fun j hj => by
    rw [aP, sc_w16]; exact (hA j (by omega)).1
  have redS : VecReduced s.mem (pa s (sc oSH)) K.L.k := fun j hj => by
    rw [pa_off]; exact (h.sh j (by omega)).1
  have ep : rowAt K i = K.L.kgRowAt (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) := by
    rw [rowAt, k3]
  rw [ep]
  refine WP.mono (kgRowAt_okL hK L₀ rbx_na rbx_na rbx_na rbx_na hkr redA redS (h.eh i hi (Nat.le_refl _)).1)
    fun s' ⟨hP, hb⟩ => ?_
  refine h.keepG W hp (Nat.le_succ _) hP.b (hP.cs .r15 (by decide)) hkc (fun r hr' => hr r (List.mem_append_left _ hr'))
    (fun _ j hj hj' => ?_) (fun _ => hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _)))
  obtain rfl : j = i := by omega
  rw [hP.pa r12_cs, hb]
  have eA : vecAtW 16 s.mem (pa s (aP K (3 * j))) K.L.k = (List.range 3).map (aHat (rhoK K.L σ) j) := by
    rw [k3]; simp only [vecAtW]
    refine List.map_congr_left fun t ht => ?_
    rw [aP, sc_w16]; exact (hA t (List.mem_range.mp ht)).2
  have eS : vecAt s.mem (pa s (sc oSH)) K.L.k = (List.range 3).map (KPke.kgS K.L.p (kgD σ)) := by
    rw [k3]; simp only [vecAt]
    refine List.map_congr_left fun t ht => ?_
    rw [pa_off]; exact (h.sh t (List.mem_range.mp ht)).2
  rw [eA, eS, (h.eh j hi (Nat.le_refl _)).2, KPke.dot_eq_dotK, tRow, KPke.kgT, show K.L.p.k = 3 from k3]

/-- Row `i`, if every `SampleNTT` so far succeeded. -/
theorem rowIf_ok (hK : KgRowsOk K.L) {i : Nat} (hi : i < 3) {s : State} (h : KH K σ i (3 * i + 3) s) :
    WP isa (ifOk (rowAt K i)) s (KH K σ (i + 1) (3 * i + 3)) := by
  have hf := W.flg i hi
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hkc, hr⟩ := keepAll_spec hf.1
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · exact row_ok W hp hK hi (h.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2)
      (r15_ok h.mat.r15 hne)
  · exact (h.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2).skip (r15_no h.mat.r15 he)

end

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The fragment of row `i`: entries `3i` to `3i + 2` of `Â`, and the blocks
of `ek` that the rows before it wrote absorbed. -/
theorem frag_ok (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {i : Nat} (hi : i < 3)
    {s : State} (h : KH K σ i (3 * i) s) : WP isa (frag K b i) s (KH K σ i (3 * i + 3)) := by
  have k3 := W.k3
  have sd : ∀ J < 4, ∀ t, SI K σ i J t → WP isa (seedAt J ((3 * i + J) / 3) ((3 * i + J) % 3)) t (SI K σ i (J + 1)) :=
    fun J hJ t ht => by have := seedI_ok W hp hi hJ ht; rwa [k3] at this
  unfold frag
  refine WP.seq (WP.mono (cp_ok W hp hi h) fun s₁ ⟨h₁, hb₁⟩ => ?_)
  have i₁ : SI K σ i 0 s₁ := ⟨h₁, ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩, hb₁⟩
  have s0 := sd 0 (by decide) s₁ i₁
  rw [show (3 * i + 0) / 3 = i by omega, show (3 * i + 0) % 3 = 0 by omega] at s0
  refine WP.seq (WP.mono s0 fun s₂ i₂ => ?_)
  have s1 := sd 1 (by decide) s₂ i₂
  rw [show (3 * i + 1) / 3 = i by omega, show (3 * i + 1) % 3 = 1 by omega] at s1
  refine WP.seq (WP.mono s1 fun s₃ i₃ => ?_)
  have s2 := sd 2 (by decide) s₃ i₃
  rw [show (3 * i + 2) / 3 = i by omega, show (3 * i + 2) % 3 = 2 by omega] at s2
  refine WP.seq (WP.mono s2 fun s₄ i₄ => ?_)
  have s3 := sd 3 (by decide) s₄ i₄
  rw [show (3 * i + 3) / 3 = i + 1 by omega, show (3 * i + 3) % 3 = 0 by omega] at s3
  refine WP.seq (WP.mono s3 fun s₅ i₅ => ?_)
  rw [Top16.aP, k3]
  exact sm_ok W hp v hb hi i₅

end

theorem stateAt_of_bytes {m m' : Mem} {p q : Addr} (h : bytesAt m p 200 = bytesAt m' q 200) :
    stateAt m p = stateAt m' q :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [Proof.Sha3.byteOf_stateAt _ _ hi, Proof.Sha3.byteOf_stateAt _ _ hi]
    have := congrArg (fun l => l[i]?) h
    simpa [bytesAt, List.getElem?_map, List.getElem?_range hi] using this

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- `ρ` to `ek`, `ek` to `dk`, `H(ek)` from the sponge's state, and `z`. -/
theorem tail_ok {s : State} (h : KH K σ 3 9 s) (ho : allOk K.L.k (rhoK K.L σ) 9) :
    WP isa (tail K) s (KFin K.L σ) := by
  have k3 := W.k3
  have hek := W.ek
  have L₀ := h.kc.lay W.toKgWfB hp
  have Wb := W.toKgWfB
  have hE : (ekK K.L σ).length = 1184 := by rw [ekK_length, hek]
  have rows : bytesAt s.mem (pa s (.r12, 0)) (384 * K.L.k) =
      KPke.catK (fun i => encode12 (KPke.kgT K.L.p (aHat (rhoK K.L σ)) (kgD σ) i)) K.L.k := by
    rw [k3]; exact bytesAt_catK s.mem s .r12 0 384 _ 3 fun j hj => by
      rw [Nat.zero_add]; exact (h.ok ho).1 j hj
  have hs0 : stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) 5 := (h.ok ho).2
  have h15 : s.gpr .r15 = 1 := by rw [h.mat.r15, ifp ho]
  have tS := W.tS
  simp only [Bool.and_eq_true] at tS
  have tC := W.tC
  simp only [Bool.and_eq_true] at tC
  obtain ⟨tCK, tCr⟩ := keepAll_spec tC.2
  obtain ⟨hrate, hk, hps, hsq, hna, hocs⟩ := hashChk_spec W.tH
  unfold tail
  -- `ρ` to `ek`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 384 * K.L.k)) (src := sc oG) (n := 32) (by decide) Wb.f₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.kc.step Wb hp hP₁.b Wb.f₁K
  have L₁ := k₁.lay Wb hp
  have hek₁ : bytesAt s₁.mem (pa s₁ (.r12, 0)) K.L.ekLen = ekK K.L σ := by
    rw [Kem.ekLen, Params.ekLen, bytesAt_split, show 0 + 384 * K.L.p.k = 384 * K.L.k from Nat.zero_add _,
      hP₁.pa (p := (.r12, 384 * K.L.k)) r12_cs, hb₁, h.rho, ekK, KPke.ekPKE, L₀.keepBytes hP₁.b Wb.f₁E]
    exact congrArg (· ++ _) rows
  have hs₁ : stateAt s₁.mem (pa s₁ (hsP K)) = HSponge.hstate (ekK K.L σ) 5 := by
    rw [EkF.stateAt_keep L₀ hP₁.b tS.1]; exact hs0
  -- `ek` to `dk`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := (.r13, 384 * K.L.k)) (src := (.r12, 0)) (n := K.L.ekLen) (by decide) Wb.f₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step Wb hp hP₂.b Wb.f₂K
  have L₂ := k₂.lay Wb hp
  rw [hek₁] at hb₂
  have hek₂ : bytesAt s₂.mem (pa s₂ (.r12, 0)) K.L.ekLen = ekK K.L σ := by
    rw [L₁.keepBytes hP₂.b Wb.f₂E]; exact hek₁
  have hs₂ : stateAt s₂.mem (pa s₂ (hsP K)) = HSponge.hstate (ekK K.L σ) 5 := by
    rw [EkF.stateAt_keep L₁ hP₂.b tS.2]; exact hs₁
  -- the sponge's state to the sponge functions' state
  refine WP.seq (WP.mono (copy_okL L₂ (dst := sc 0) (src := hsP K) (n := 200) (show Reg.rbx ≠ .rdi by decide) tC.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_)
  have k₃ := k₂.step Wb hp hP₃.b tCK
  have L₃ := k₃.lay Wb hp
  have hR₃ : Spec.Sha3.Repr s₃.mem (pa s₃ (sc 0)) 136 ((ekK K.L σ).take 680) := by
    show stateAt _ _ = _
    rw [hP₃.pa rbx_cs, stateAt_of_bytes hb₃, hs₂, HSponge.hstate, ite_eq_left (by rw [hE]; decide)]
    rfl
  have ek₃ : bytesAt s₃.mem (pa s₃ (.r12, 0)) 1184 = ekK K.L σ := by
    rw [L₂.keepBytes hP₃.b (tCr ((.r12, 0), 1184) (by simp)), ← hek]; exact hek₂
  -- the rest of `ek`, the padding and the squeeze
  rw [show K.L.ekLen - 136 * hDone = 504 by rw [hek]; rfl, show 136 * hDone = 680 from rfl]
  refine WP.seq (WP.mono (absAll_ok (kgB_bases K.L) hrate [((.r12, 680), 504)] L₃ 0 _ hps (by decide)
    (by rw [List.length_take, hE]; rfl) hR₃) fun s₄ ⟨hP₄, hR₄⟩ => ?_)
  have epc : (ekK K.L σ).take 680 ++ pieces s₃ [((.r12, 680), 504)] = ekK K.L σ := by
    have := bytesAt_slice s₃.mem (pa s₃ (.r12, 0)) (k := 680) (c := 504) (len := 1184) (by omega)
    rw [ek₃, pa_add, Nat.zero_add] at this
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← this,
      List.take_of_length_le (show (List.drop 680 (ekK K.L σ)).length ≤ 504 by rw [List.length_drop, hE]),
      List.take_append_drop]
  rw [epc] at hR₄
  have L₄ := L₃.post hP₄.b (kgB_bases K.L)
  refine WP.seq (WP.mono (kpad_ok (show 6 < 256 by decide) (KPadH.of L₄ hk hrate (pos := 504 % 136) (by decide)))
    fun s₅ ⟨hP₅, hS₅⟩ => ?_)
  have hP₅' : PPost s₄ s₅ [(sc 0, 200), (sc 200, 640)] := hP₅
  have L₅ := L₄.post hP₅.b (kgB_bases K.L)
  have e4 : pa s₄ (sc 0) = pa s₃ (sc 0) := hP₄.pa (by decide)
  have hS := hS₅ (ekK K.L σ) (by rw [e4]; exact hR₄) (by rw [hE])
  refine WP.seq (WP.mono (ksqz_ok hna (KSqzH.of L₅ hsq hrate)) fun s₆ ⟨hP₆, ho₆⟩ => ?_)
  have hP₆' : PPost s₅ s₆ [(sc 0, 200), ((.r13, 384 * K.L.k + K.L.ekLen), 32), (sc 200, 640)] := hP₆
  have hP₃₆ : PPost s₃ s₆ (finW₃ K.L) :=
    PPost.trans (PPost.trans hP₄ hP₅' (by decide)
      (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h <;> simp [h])
      (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h <;> simp [h]))
      hP₆' (cs3 (by decide) hocs (by decide)) (fun w hw => hw) sub_acb
  have k₆ := k₃.step Wb hp hP₃₆.b Wb.f₃K
  have L₆ := k₆.lay Wb hp
  have e5 : pa s₅ (sc 0) = pa s₄ (sc 0) := hP₅.pa (by decide)
  have hH : bytesAt s₆.mem (pa s₃ (.r13, 384 * K.L.k + K.L.ekLen)) 32 = H (ekK K.L σ) := by
    rw [← hP₄.pa hocs, ← hP₅.pa hocs, ho₆, e5, hS, sha3Suffix6, H_eq]
  -- `z`
  refine WP.mono (copy_okL L₆ (dst := (.r13, 384 * K.L.k + K.L.ekLen + 32)) (src := (.rbp, 32)) (n := 32) (by decide)
    Wb.f₄) fun s₇ ⟨hP₇, hb₇⟩ => ?_
  have k₇ := k₆.step Wb hp hP₇.b Wb.f₄K
  rw [k₆.z] at hb₇
  refine ⟨k₇, ?_, ?_, ?_⟩
  · rw [hP₇.cs .r15 (by decide), hP₃₆.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h15]
  · rw [L₆.keepBytes hP₇.b Wb.f₄E, L₃.keepBytes hP₃₆.b Wb.f₃E, hek]; exact ek₃
  · have dS := Wb.dkS
    have dE := Wb.dkE
    have hP' := PPost.app hP₃₆ hP₇ (by simp [calleeSaved])
    rw [show K.L.dkLen = 384 * K.L.k + K.L.ekLen + 32 + 32 by
        simp only [Kem.k, Kem.dkLen, Kem.ekLen, Params.dkLen, Params.ekLen]; omega,
      bytesAt_split, bytesAt_split, bytesAt_split, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    rw [hP₇.pa (p := (.r13, 384 * K.L.k + K.L.ekLen + 32)) r13_cs, hb₇,
      L₆.keepBytes hP₇.b Wb.dkH, hP₃₆.pa (p := (.r13, 384 * K.L.k + K.L.ekLen)) r13_cs, hH,
      L₃.keepBytes hP'.b dE, L₂.keepBytes hP₃.b (by rw [k3, hek]; exact tCr ((.r13, 1152), 1184) (by simp)),
      hP₂.pa (p := (.r13, 384 * K.L.k)) r13_cs, hb₂, dkK]
    rw [L₃.keepBytes hP'.b (keepB_sub dS fun w hw => by
        rcases List.mem_append.1 hw with h | h
        exacts [List.mem_append_left _ (List.mem_append_right _ h), List.mem_append_right _ h]),
      L₂.keepBytes hP₃.b (by rw [k3]; exact tCr ((.r13, 0), 1152) (by simp)),
      L₁.keepBytes hP₂.b (keepB_sub dS fun w hw =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))),
      L₀.keepBytes hP₁.b (keepB_sub dS fun w hw =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw)))]
    have hdk : bytesAt s.mem (pa s (.r13, 0)) (384 * K.L.k) = KPke.dkPKE K.L.p (kgD σ) := by rw [k3]; exact h.dk
    rw [hdk]

end

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The last row and the tail, if every `SampleNTT` succeeded. -/
theorem last_ok (hK : KgRowsOk K.L) {s : State} (h₅ : KH K σ 2 9 s) :
    WP isa (ifOk (.seq (rowAt K 2) (tail K))) s (KEnd K.L σ) := by
  have k3 := W.k3
  have hf := W.flg 2 (by decide)
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hkc, hr⟩ := keepAll_spec hf.1
  have e9 : K.L.k * K.L.k = 9 := by rw [k3]
  refine ifOk_ok (fun s₆ hP hne => ?_) fun s₆ hP he => ?_
  · have ho := r15_ok h₅.mat.r15 hne
    have h₆ := h₅.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2
    refine WP.seq (WP.mono (row_ok W hp hK (i := 2) (by decide) h₆ ho) fun s₇ h₇ => ?_)
    refine WP.mono (tail_ok W hp h₇ ho) fun s' hf' => ⟨hf'.kc, by rw [hf'.r15, e9, ifp ho], fun _ => hf'⟩
  · have h₆ := h₅.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2
    have ho := r15_no h₅.mat.r15 he
    exact ⟨h₆.kc, by rw [e9]; exact h₆.mat.r15, fun h => absurd (by rwa [e9] at h) ho⟩

end

/-! ## Row 0, with `PRF₂(σ, 0)` and `PRF₂(σ, 1)` -/

/-- From the noise on, before the transforms: `ρ`, `σ` and the polynomials
of `s ‖ e` from 2 on. -/
structure KM (K : Kem16) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  se : ∀ N < 6, 2 ≤ N → PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)

theorem KN.km {K : Kem16} {σ s : State} (h : KN K 6 σ s) : KM K σ s := ⟨h.kc, h.rho, h.sig, h.sb, h.se⟩

/-- After row 0 of `Â`: its entries, and the outputs of `PRF₂(σ, 0)` and
`PRF₂(σ, 1)`; the polynomials of `s ‖ e` below `n0` too; and the sponge's
state zeroed, if `hz`. -/
structure KG (K : Kem16) (σ : State) (n0 : Nat) (hz : Bool) (s : State) : Prop extends KM K σ s where
  se0 : ∀ N < n0, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)
  mat : MatB16 K.L.k K.oA (rhoK K.L σ) 3 s
  pout : ∀ N < 2, bytesAt s.mem (pa s (poP K N)) 128 = prf 2 (KPke.kgSigma K.L.p (kgD σ)) (BitVec.ofNat 8 N)
  hs : hz = true → stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) 0

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

theorem KM.keep {s s' : State} (h : KM K σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hkc : kcChk K.L ws = true) (hk : ∀ r ∈ baseR ++ rR K 6, keepB (kgB K.L) ws r.1 r.2 = true) : KM K σ s' := by
  have L₀ := h.kc.lay W.toKgWfB hp
  refine ⟨h.kc.step W.toKgWfB hp hP hkc, ?_, ?_, ?_, fun N hN h2 => ?_⟩
  · rw [L₀.keepBytes hP (hk (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP (hk (sigP, 32) (by simp))]; exact h.sig
  · rw [L₀.keepBytes hP (hk (sc oSB, 32) (by simp))]; exact h.sb
  · exact L₀.keepPoly16 hP (hk (rP K N, 512) (List.mem_append_right _ (List.mem_map.2 ⟨N, List.mem_range.2 hN, rfl⟩)))
      (h.se N hN h2)

/-- While the seeds of row 0 are written, after `σ`'s copy. -/
structure S0 (K : Kem16) (σ : State) (J : Nat) (s : State) : Prop where
  km : KM K σ s
  r15 : s.gpr .r15 = 1
  sd : SeedsIs (rhoK K.L σ) K.L.k 0 J s
  ps : bytesAt s.mem (pa s (psP K)) 32 = KPke.kgSigma K.L.p (kgD σ)

theorem seed0_ok {J : Nat} (hJ : J < 4) {s : State} (h : S0 K σ J s) :
    WP isa (seedAt J ((0 + J) / K.L.k) ((0 + J) % K.L.k)) s (S0 K σ (J + 1)) := by
  have hsd := W.sd0
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨hs, hk⟩ := hsd J hJ
  obtain ⟨hkc, hr⟩ := keepAll_spec hk
  have L₀ := h.km.kc.lay W.toKgWfB hp
  refine WP.mono (seed_step L₀ (kgB_bases K.L) (by omega) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.km.keep W hp hP.b hkc (fun r hr' => hr r (List.mem_append_left _ hr')), by rw [hP.cs .r15 (by decide)]; exact h.r15,
      hS, ?_⟩
  rw [L₀.keepBytes hP.b (hr (psP K, 32) (List.mem_append_right _ (List.mem_singleton_self _)))]
  exact h.ps

/-- Row 0 of `Â`, and `PRF₂(σ, 0)` and `PRF₂(σ, 1)`. -/
theorem frag0_ok (v : Sample4Impl) {p : Prog isa} (hb : v.callee.batchP16 = some p) {s : State} (h : KN K 6 σ s) :
    WP isa (frag0 K p) s (KG K σ 0 false) := by
  have k3 := W.k3
  have hc0 := W.c0
  simp only [Bool.and_eq_true] at hc0
  obtain ⟨hkc0, hr0⟩ := keepAll_spec hc0.2
  have L₀ := h.kc.lay W.toKgWfB hp
  have sd : ∀ J < 4, ∀ t, S0 K σ J t → WP isa (seedAt J ((0 + J) / 3) ((0 + J) % 3)) t (S0 K σ (J + 1)) :=
    fun J hJ t ht => by have := seed0_ok W hp hJ ht; rwa [k3] at this
  unfold frag0
  refine WP.seq (WP.mono (copy_okL L₀ (dst := psP K) (src := sigP) (n := 32) (by decide) hc0.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have i₁ : S0 K σ 0 s₁ := ⟨h.km.keep W hp hP₁.b hkc0 hr0, by rw [hP₁.cs .r15 (by decide)]; exact h.r15,
    ⟨by rw [L₀.keepBytes hP₁.b (hr0 (sc oSB, 32) (by simp))]; exact h.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_cs, hb₁, h.sig]⟩
  have s0 := sd 0 (by decide) s₁ i₁
  refine WP.seq (WP.mono s0 fun s₂ i₂ => ?_)
  have s1 := sd 1 (by decide) s₂ i₂
  refine WP.seq (WP.mono s1 fun s₃ i₃ => ?_)
  have s2 := sd 2 (by decide) s₃ i₃
  refine WP.seq (WP.mono s2 fun s₄ i₄ => ?_)
  have s3 := sd 3 (by decide) s₄ i₄
  refine WP.seq (WP.mono s3 fun s₅ i₅ => ?_)
  have hsm := W.sm0
  simp only [Bool.and_eq_true] at hsm
  obtain ⟨hkc, hr⟩ := keepAll_spec hsm.2
  have L₅ := i₅.km.kc.lay W.toKgWfB hp
  rw [Top16.aP, Nat.mul_zero, Nat.add_zero]
  refine WP.mono (sampleHAtP16_ok (v.batchP16 p hb) (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have km₆ := i₅.km.keep W hp h₆.b hkc hr
  refine ⟨km₆, fun _ h => absurd h (Nat.not_lt_zero _), ?_, fun N hN => ?_, fun h => absurd h (by decide)⟩
  · have m₀ := MatB16.zero K.L.k K.oA (rhoK K.L σ) i₅.r15
    have := EkF16.MatB16.three (K := K) m₀ L₅ h₆.b (fun e' he' => absurd he' (Nat.not_lt_zero _)) ?_ fun t ht f hf => ?_
    · simpa using this
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega)]; simpa using hf)
      rwa [poly4W, pBytes_true, pa_off] at this
  · have e := h₆.pout N hN
    rw [pa_off, pa_off, i₅.ps] at e
    rw [h₆.b.pa rbx_bases, poP, Nat.add_assoc]; exact e

/-- The sponge's state zeroed. -/
theorem hzG_ok {s : State} (h : KG K σ 0 false s) : WP isa (.block (Encaps16.hzero K)) s (KG K σ 0 true) := by
  have hc := W.hz
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (EkF16.hzero16_ok L₀ hc.1) fun s' ⟨hP, hz⟩ => ?_
  refine ⟨h.toKM.keep W hp hP.b hkc fun r hr' => hr r (List.mem_append_left _ (List.mem_append_left _ hr')),
    fun _ h => absurd h (Nat.not_lt_zero _),
    ⟨by rw [hP.cs .r15 (by decide)]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP.b
      (hr (aP K e', 512) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))))
      (h.mat.mat e' he' f hf)⟩, fun N hN => ?_, fun _ => ?_⟩
  · rw [L₀.keepBytes hP.b (hr (poP K N, 128) (List.mem_append_right _ (List.mem_map.2 ⟨N, List.mem_range.2 hN, rfl⟩)))]
    exact h.pout N hN
  · rw [hP.pa rbx_cs, hz]; exact (HSponge.hstate_zero _).symm

/-- `s ‖ e`, polynomial `N < 2`, from row 0's outputs of `PRF₂`. -/
theorem cbdP_ok {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2) {s : State} (h : KG K σ N true s) :
    WP isa (cbdP K A N) s (KG K σ (N + 1) true) := by
  have hc := W.cP N hN
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hc.1) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.pout N hN, ← hP₁.pa rbx_cs] at hp₁
  have mx : ∀ N' < 6, N' ≠ N → (rP K N', 512) ∈ rRx K N := fun N' h₁ h₂ =>
    List.mem_map.2 ⟨N', List.mem_filter.2 ⟨List.mem_range.2 h₁, by simpa using h₂⟩, rfl⟩
  refine ⟨⟨h.kc.step W.toKgWfB hp hP₁.b hkc, ?_, ?_, ?_, fun N' hN' h2 => ?_⟩, fun N' hN' => ?_,
    ⟨by rw [hP₁.cs .r15 (by decide)]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP₁.b
      (hr (aP K e', 512) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))))) (h.mat.mat e' he' f hf)⟩, fun N' hN' => ?_, fun _ => ?_⟩
  · rw [L₀.keepBytes hP₁.b (hr (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP₁.b (hr (sigP, 32) (by simp))]; exact h.sig
  · rw [L₀.keepBytes hP₁.b (hr (sc oSB, 32) (by simp))]; exact h.sb
  · exact L₀.keepPoly16 hP₁.b (hr (rP K N', 512) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mx N' hN' (by omega))))))) (h.se N' hN' h2)
  · rcases (by omega : N' < N ∨ N' = N) with hN'' | rfl
    · exact L₀.keepPoly16 hP₁.b (hr (rP K N', 512) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (mx N' (by omega) (by omega))))))) (h.se0 N' hN'')
    · exact hp₁
  · rw [L₀.keepBytes hP₁.b (hr (poP K N', 128) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨N', List.mem_range.2 hN', rfl⟩))))]
    exact h.pout N' hN'
  · rw [EkF.stateAt_keep L₀ hP₁.b (hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _)))]
    exact h.hs rfl

/-- `vg_mlkem768_kpke_keygen_ntt`: `ŝ`, `ê` and `dk_PKE`; before row 0's `t̂`. -/
theorem nttG_ok (hK : KgRowsOk K.L) {s : State} (h : KG K σ 2 true s) : WP isa (nttAt K) s (KH K σ 0 3) := by
  have hc := W.nt
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  have k3 := W.k3
  have se : ∀ N < 6, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N) := fun N hN => by
    rcases (by omega : N < 2 ∨ 2 ≤ N) with h2 | h2
    exacts [h.se0 N h2, h.se N hN h2]
  have red : VecReducedW 16 s.mem (pa s (sc K.oR)) (2 * K.L.k) := fun N hN => by
    rw [sc_w16]; exact (se N (by omega)).1
  rw [← k3] at hc
  refine WP.mono (kgNttAt_okL hK L₀ rbx_na rbx_na rbx_na rbx_na hc.1 red) fun s' ⟨hP, hS, hE, hD⟩ => ?_
  have eS : (vecAtW 16 s.mem (pa s (sc K.oR)) K.L.k).map ntt = (List.range 3).map (KPke.kgS K.L.p (kgD σ)) := by
    rw [k3]; simp only [vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgS]
    rw [sc_w16, (se j (by have := List.mem_range.mp hj; omega)).2]
  have eE : (vecAtW 16 s.mem (pa s (sc K.oR) + BitVec.ofNat 64 (512 * K.L.k)) K.L.k).map ntt =
      (List.range 3).map (KPke.kgE K.L.p (kgD σ)) := by
    rw [k3]; simp only [vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgE]
    rw [w16_off, pa_off, show K.oR + (512 * 3 + 512 * j) = K.oR + 512 * (3 + j) by omega]
    have := (se (3 + j) (by have := List.mem_range.mp hj; omega)).2
    rw [Top16.rP] at this
    rw [this, show K.L.p.k = 3 from k3]
  rw [eS, k3] at hS; rw [eE, k3] at hE; rw [eS, k3] at hD
  have hA : ∀ e' < 3, keepB (kgB K.L) ntW (aP K e') 512 = true := fun e' he' =>
    hr (aP K e', 512) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩)))
  refine ⟨h.kc.step W.toKgWfB hp hP.b (by rw [k3]; exact hkc), ?_, ?_, fun j hj => ?_, fun j hj _ => ?_, ?_,
    ⟨by rw [hP.cs .r15 (by decide)]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP.b
      (by rw [k3]; exact hA e' he') (h.mat.mat e' he' f hf)⟩,
    fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩⟩
  · rw [L₀.keepBytes hP.b (by rw [k3]; exact hr (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP.b (by rw [k3]; exact hr (sc oSB, 32) (by simp))]; exact h.sb
  · rw [hP.pa rbx_cs, ← pa_off]; exact vecIs_get hS hj
  · rw [hP.pa rbx_cs, ← pa_off]; exact vecIs_get hE hj
  · rw [hP.pa r13_cs, hD, KPke.dkPKE, KPke.catK_eq, show K.L.p.k = 3 from k3]
    simp only [encodeVec, List.flatMap_map]
  · rw [EkF.stateAt_keep L₀ hP.b (by rw [k3]; exact hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _)))]
    exact h.hs rfl

/-- The rows, and the tail if every `SampleNTT` succeeded. -/
theorem rows_ok (hK : KgRowsOk K.L) (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b)
    {p : Prog isa} (hpb : v.callee.batchP16 = some p) {s : State} (h : KN K 6 σ s) :
    WP isa (rows K b p v.callee.arith) s (KEnd K.L σ) := by
  unfold rows
  refine WP.seq (WP.mono (frag0_ok W hp v hpb h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (hzG_ok W hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (cbdP_ok W hp v.arith (N := 0) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (cbdP_ok W hp v.arith (N := 1) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (nttG_ok W hp hK h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (rowIf_ok W hp hK (i := 0) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (frag_ok W hp v hb (i := 1) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (rowIf_ok W hp hK (i := 1) (by decide) h₇) fun s₈ h₈ => ?_)
  exact WP.seq (WP.mono (frag_ok W hp v hb (i := 2) (by decide) h₈) fun s₉ h₉ => last_ok W hp hK h₉)

end

theorem kemKeyGenH16_correct {K : Kem16} (hK : KgRowsOk K.L) (v : Sample4Impl) (W : KgH16Wf K)
    {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {p : Prog isa} (hpb : v.callee.batchP16 = some p)
    (hctl : ctlOk (kemKeyGenH16 K v.callee b p) = true) (σ : State) (hp : (keyGenK K.L).pre σ) :
    ∃ t s', Exec isa (kemKeyGenH16 K v.callee b p) σ t s' ∧ abiPreserved σ s' ∧ (keyGenK K.L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toKgWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (gRho_ok W.toKgWfB hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (prfs_ok W hp v h₂ h15') fun s₃ h₃ =>
        WP.seq (WP.mono (seqR_ok (I := fun k => KN K k σ) 4 2 (fun k hk hk' s hs => se_ok W hp v.arith (by omega) hk hs)
            s₃ h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (rows_ok W hp hK v hb hpb h₄) fun s₆ h₆ =>
            WP.mono (topEpi_ok h₆.kc.top (h₆.hin W.toKgWfB hp)) fun s₇ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toKgWfB h₆ hr hm⟩ : gprPreserved σ s₇ ∧ (keyGenK K.L).post σ s₇))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end KeyGenH

end VG.Proof.MlKem.X86_64
