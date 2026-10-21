module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Base
public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Bits
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

end KeyGenH

end VG.Proof.MlKem.X86_64
