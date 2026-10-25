module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeBody

/-!
# `vg_ffdh_exchange` on PPC64LE: correctness

`exchange` loads the working space's address from the stack (`loadS1_ok`),
saves the nonvolatile registers in its header, stores x, `x_len` and `out`
in the header's words 8–10 (`hdr_ok`), sets up the registers, loads and
checks p (`loadP_ok`), computes z (`exPower_ok`), writes it or zeros
(`exOut_ok`) and restores the registers (`ex_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- The second argument on the stack, `scratch`, into `r11`. -/
theorem loadS1_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    WP isa (.block ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr)) s fun t =>
      (t.gpr .r11 = stackArg s 1 ∧ t.mem = s.mem) ∧ Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r11 104) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 104)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- x, `x_len` and `out` into the header's words 8–10 at `S`, the peer into
`r9` and the domain's arguments into `r3`–`r5`. -/
theorem hdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r3 .r23 80, .addi .r9 .r10 0,
      .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r8 ∧ word t.mem S 72 = s.gpr .r9 ∧ word t.mem S 80 = s.gpr .r3 ∧
        t.gpr .r9 = s.gpr .r10 ∧ t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
        Outside S 64 24 s.mem t.mem) ∧ Keep [.r3, .r4, .r5, .r9] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  prun [h23, i0, i1, i2, BitVec.add_zero]
  have o0 := writeW_outside s.mem S (d := 64) (s.gpr .r8) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r8)) S (d := 72) (s.gpr .r9) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r8)).writeW (off S 72) (s.gpr .r9)) S (d := 80)
    (s.gpr .r3) (by omega_arith)
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · exact ((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))

/-- Bytes apart from the working space are kept by a change in it. -/
theorem outside_bytesAt {B Q : Addr} {o n Z k : Nat} {m m' : Mem} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off Q i ≠ x) : Spec.Rsa.bytesAt m' Q k = Spec.Rsa.bytesAt m Q k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  have := hsep i (List.mem_range.mp hi) (off Q i)
  show o + n ≤ ofs B (off Q i)
  by_contra hc
  exact this (by omega_arith) rfl

theorem saved_ne11' : ∀ i < 18, Impl.Ffdh.PPC64LE.Domain.saved i ∉ ([.r11] : List Reg) := by decide

theorem ex_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r11] : List Reg) ++ ([.r23] : List Reg) ++ ([.r3, .r4, .r5, .r9] : List Reg) ++
      ([.r10, .r11, .r21, .r27, .r28, .r29, .r31] : List Reg) ++
      ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
        (exPowRegs ++ exOutRegs ++ ([.r3] : List Reg)) := by
  decide

theorem ret_bv (c : Prop) [Decidable c] :
    (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if c then 1 else 0 := by
  split <;> rfl

theorem ex_correct (s : State) (h : exContract.pre s) :
    ∃ tr t, Exec isa exchange s tr t ∧ abiPreserved s t ∧ exContract.post s t := by
  show WP isa exchange s fun t => abiPreserved s t ∧ exContract.post s t
  obtain ⟨hsp, hrd, hwr, dOD, dOX, dOP, dOS, dOA, dDS, dXS, dPS, dSA, nwO, nwD, nwX, nwP, nwS, ⟨hk, hk'⟩, hL,
    hol, hpl, hx1, hxk, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨exStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 104) 8
    rw [show s.sp + BitVec.ofNat 64 104 = s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [Offset.add_add]]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [hol] at hwr dOD dOX dOP dOS dOA nwO
  rw [hpl] at hrd dOP dPS nwP
  generalize hOd : s.gpr .r3 = O at hwr dOD dOX dOP dOS dOA nwO
  generalize hDd : s.gpr .r5 = D at hrd dOD dDS nwD
  generalize hLd : (s.gpr .r6).toNat = L at hrd dOD dDS nwD hL
  generalize hkd : (s.gpr .r7).toNat = k at hk hk' hL hxk hsl hwr dOD dOX dOP dOS dOA nwO hrd dPS nwP
  generalize hXd : s.gpr .r8 = X at hrd dOX dXS nwX
  generalize hxd : (s.gpr .r9).toNat = xl at hrd dOX dXS nwX hx1 hxk
  generalize hPd : s.gpr .r10 = P at hrd dOP dPS nwP
  generalize hSd : stackArg s 1 = S at hwr dOS dDS dXS dPS dSA nwS
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dOS dDS dXS dPS dSA nwS
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hZ256 : 256 ≤ Z := by omega_arith
  generalize hwd : (k + 7) / 8 = w
  have hw4 : 4 ≤ w := by omega_arith
  have hw' : w ≤ 128 := by omega_arith
  have hZw : slot w 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hwd, hk', hk]
  have e0 : slot w 0 = 256 := by rw [slot_eq]; omega_arith
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  have hinH : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  have sepD := sep_of_disjoint dDS (by omega_arith)
  have sepX := sep_of_disjoint dXS (by omega_arith)
  have sepP := sep_of_disjoint dPS (by omega_arith)
  have rdD := rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega_arith)
  have rdX := rd_of_mem (s := s) (D := X) (L := xl) (by rw [hrd]; simp) (by omega_arith)
  have rdP := rd_of_mem (s := s) (D := P) (L := k) (by rw [hrd]; simp) (by omega_arith)
  have sepO : ∀ x, ofs O x < k → Z ≤ ofs S x := Pub.sep_of_disjoint dOS
  have sepSO : ∀ x, ofs S x < Z → k ≤ ofs O x := Pub.sep_of_disjoint dOS.symm
  unfold exchange exFront
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadS1_ok s hA1) fun s₀ ⟨⟨a11, m0⟩, k0⟩ => ?_)
  have a11' : s₀.gpr .r11 = S := a11.trans hSd
  refine WP.block_append (WP.mono (save_ok (ws := .r11) (by decide) s₀ (by rw [a11', k0.wr]; exact hin))
    fun s₁ hS => ?_)
  have k1 := k0.trans hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans a11'
  have hfr₁ : Frame [savR S] s.mem s₁.mem := by rw [← m0, ← a11']; exact hS.frame
  refine WP.block_append (WP.mono (hdr_ok h23₁ (by rw [k1.wr]; exact hinH))
    fun s₂ ⟨⟨w8, w9, w10, b9, b3, b4, b5, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) (b3.trans ((k1.gpr .r5 (by decide)).trans hDd))
    (by rw [b4, k1.gpr .r6 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [b5, k1.gpr .r7 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m3⟩, k3⟩ => ?_
  rw [hwd] at a11 a29 a10
  have k123 := k12.trans k3
  have e3 : Env s₃ S Z w := ⟨hs.congr k123.wr, a10, a29, a11, a31, hw4, hw', hZw⟩
  have hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [m3, outside_bytesAt o2 (by omega_arith) hsep]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    have hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega_arith)) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  have g23 : s₃.gpr .r23 = S := (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁)
  refine WP.seq (WP.mono (loadP_ok e3 a21 a28 hwd.symm hk hk' (fun i hi => by
      rw [k123.rd, k123.wr]; exact rdD i (by omega_arith)) (fun i hi => sepD i (by omega_arith)))
    fun s₄ ⟨⟨p4, c4, b4'⟩, k4⟩ => ?_)
  rw [hb3 D k fun i hi => sepD i (by omega_arith)] at p4 c4
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) = p at p4 c4
  have e4 : Env s₄ S Z w := e3.keep k4 (by decide)
  have k1234 := k123.trans k4
  have hpk : p < 256 ^ k := by
    rw [← hp]; have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem D k)
    rwa [bytesAt_length] at this
  -- The header's words.
  have hw4' : ∀ d, d + 8 ≤ 256 → word s₄.mem S d = word s₂.mem S d := fun d hd => by
    rw [Outside.word b4' (by omega_arith) (by omega_arith), m3]
  generalize hz : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) % p = z
  have hite : WP isa (.ite (.zero .d .r0) (.seq exPower exOut) (.block [.li .r3 0])) s₄ fun t =>
      (Spec.Rsa.modulusValid p k = true →
        Spec.Rsa.bytesAt t.mem O k = (if 1 < z ∧ z < p - 1 then Spec.Rsa.i2osp z k else List.replicate k 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if 1 < z ∧ z < p - 1 then 1 else 0)) ∧
      (∀ i < 18, word t.mem S (112 + 8 * i) = word s₄.mem S (112 + 8 * i)) ∧
      Keep (exPowRegs ++ exOutRegs ++ ([.r3] : List Reg)) s₄ t := by
    refine WP.ite (s₄.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · have hv := c4.mp (by simpa using hb)
      have hf := modulus_facts hv
      have hX₄ : s₄.mem.readW (off S 64) 64 = off X 0 := by
        show word s₄.mem S 64 = _
        rw [hw4' 64 (by omega_arith), w8, k1.gpr .r8 (by decide), hXd]; simp [off]
      have hXL₄ : s₄.mem.readW (off S 72) 64 = BitVec.ofNat 64 xl := by
        show word s₄.mem S 72 = _
        rw [hw4' 72 (by omega_arith), w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
      refine WP.seq (WP.mono (exPower_ok (Y := P) (X := X) (k := k) (xl := xl) e4
        ((k4.gpr .r23 (by decide)).trans g23)
        ((k4.gpr .r9 (by decide)).trans ((k3.gpr .r9 (by decide)).trans (b9.trans
          ((k1.gpr .r10 (by decide)).trans hPd))))
        ((k4.gpr .r28 (by decide)).trans a28) (by omega_arith) (by omega_arith) hx1 (by omega_arith)
        (fun i hi => by rw [k1234.rd, k1234.wr]; exact rdP i hi) sepP
        (fun i hi => by rw [k1234.rd, k1234.wr]; exact rdX i hi) sepX hX₄ hXL₄
        (by rw [p4]; exact hf.1) (by rw [p4]; exact hf.2)) fun s₅ ⟨⟨z5, p5, b5', r10₅⟩, k5⟩ => ?_)
      rw [Body.bytesAt b4' hZw sepP, Body.bytesAt b4' hZw sepX, hb3 P k sepP, hb3 X xl sepX, p4, hz] at z5
      have hO5 : s₅.mem.readW (off S 80) 64 = off O 0 := by
        show word s₅.mem S 80 = _
        rw [Outside.word b5' (by omega_arith) (by omega_arith), hw4' 80 (by omega_arith), w10, k1.gpr .r3 (by decide), hOd]
        simp [off]
      have k45 := k1234.trans k5
      refine WP.mono (exOut_ok (O := O) (k := k) (e4.hs.congr k5.wr)
        (Scr.of_mem (by rw [k45.wr, hwr]; simp) nwO) r10₅
        ((k5.gpr .r29 (by decide)).trans e4.h29) ((k5.gpr .r11 (by decide)).trans e4.h11)
        ((k5.gpr .r23 (by decide)).trans ((k4.gpr .r23 (by decide)).trans g23))
        ((k5.gpr .r28 (by decide)).trans ((k4.gpr .r28 (by decide)).trans a28)) hw4 hw' hZw (by omega_arith) (by omega_arith)
        hO5 sepO (by rw [p5, p4]; omega_arith) (by rw [z5, p5, p4, ← hz]; exact Nat.mod_lt _ (by omega_arith))
        (by rw [p5, p4]; exact hpk)) fun t ⟨⟨tb, t3, m, bm, om⟩, kt⟩ => ⟨fun _ => ?_, fun i hi => ?_,
          (k5.trans kt).mono (by decide)⟩
      · rw [z5, p5, p4] at tb t3
        exact ⟨tb, t3⟩
      · refine (Pub.Outside.word_apart (d := 112 + 8 * i) om sepSO (by omega_arith) (by omega_arith) hs.nowrap).trans ?_
        show Mont.word m S (112 + 8 * i) = Mont.word s₄.mem S (112 + 8 * i)
        rw [Outside.word bm (by omega_arith) (by omega_arith), Outside.word b5' (by omega_arith) (by omega_arith)]
    · refine WP.mono (li_ok s₄ 0 (by decide)) fun t ⟨⟨_, tm⟩, kt⟩ =>
        ⟨fun hv => absurd (c4.mpr hv) (by simpa using hb), fun i hi => by rw [tm], kt.mono (by decide)⟩
  refine WP.seq (WP.mono hite fun t₅ ⟨tpost, tw, k5⟩ => ?_)
  have kall := k1234.trans k5
  have hsav : ∀ i < 18, t₅.mem.readW (off (savW S) (8 * i)) 64 = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) :=
      fun i hi => by
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← k0.gpr _ (saved_ne11' i hi), ← hS.saved i hi, a11', ea]
    show word t₅.mem S (112 + 8 * i) = word s₁.mem S (112 + 8 * i)
    rw [tw i hi, hw4' _ (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
  refine WP.mono (restore_ok t₅ ((k5.gpr .r23 (by decide)).trans ((k4.gpr .r23 (by decide)).trans g23))
    (by rw [kall.wr]; exact hin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (ex_pres_not_written r hr hn)]
  · dsimp only [exContract]
    intro hdv hpv
    rw [hDd, hLd, hkd] at hdv hpv
    rw [hpl, hkd, hPd] at hpv
    have hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp] at hmod
    have hlo : 256 ^ (k - 1) ≤ p := by
      simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hmod; exact hmod.2
    have hf := modulus_facts hmod
    rw [hDd, hLd, hkd, hpl, hkd, hPd, hXd, hxd, hOd, hol, hkd]
    rw [Proof.Ffdh.exchangeOp_eq (k := k) hpv (by rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp]; omega_arith)
      (by rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp]; exact Proof.Ffdh.octets_bitLength (by omega_arith) hlo hpk),
      Proof.Ffdh.domainOf_p _ _ hLk.1, hp, hz, um, uot .r3 (by decide)]
    obtain ⟨tb, t3⟩ := tpost hmod
    rw [t3, ret_bv]
    by_cases hc : 1 < z ∧ z < p - 1
    · simp only [hc, and_self, ↓reduceIte, Spec.Rsa.written, true_and]
      rw [tb]; simp only [hc, and_self, ↓reduceIte]
    · simp only [hc, ↓reduceIte, Spec.Rsa.written, true_and]
      rw [tb]; simp only [hc, ↓reduceIte]

end VG.Proof.Ffdh.PPC64LE.Domain
