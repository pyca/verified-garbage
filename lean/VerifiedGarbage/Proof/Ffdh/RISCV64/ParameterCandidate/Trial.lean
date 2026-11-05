module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on RISC-V: RSA's trial division

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{Trial,MainShape}.lean`):
`trialSieve_ok`, the count of entries for p's width in `hTrialN`, the
table's address (`lla`), RSA's loop (`Trial.loop_ok`), and its flag or'ed
into `hBad`: clear exactly when no entry of the first `trialN bits` divides
the value in array 0; `sieved_shape_iff`, the shape's flags and the trial
divisions of p and q all clear exactly when the sieved specification's
shape checks pass.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64.Search (rw_self frm_writeW)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.entry)

/-! ## The entries tried -/

/-- The entries of RSA's table trial division uses for a candidate of
`bits` bits: 512, or 1024 above 1024 bits. -/
def trialN (bits : Nat) : Nat := if (bits + 63) / 64 ≤ 16 then 512 else 1024

/-- Trial division by them is `obviouslyComposite` for `bits`. -/
theorem trialN_spec {bits c : Nat} (large : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (trialN bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  unfold trialN
  rw [VG.Proof.RsaKeyGen.trialPrefix_spec large]
  unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
  have : (1024 < 64 * ((bits + 63) / 64)) = (1024 < bits) := propext (by omega)
  simp only [this]

/-- The shape's flags, and trial division of p and q, all clear exactly when
the sieved specification's shape checks pass. -/
theorem sieved_shape_iff {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    (goodRes g (Spec.Ffdh.candidateOf bits x) ∧ (∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x % d ≠ 0) ∧
        VG.Proof.RsaKeyGen.trialPrefix (Spec.Ffdh.candidateOf bits x) (trialN bits) = false ∧
        Spec.Ffdh.candidateOf bits x / 2 % 2 = 1 ∧ (∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x / 2 % d ≠ 0) ∧
        VG.Proof.RsaKeyGen.trialPrefix (Spec.Ffdh.candidateOf bits x / 2) (trialN bits) = false) ↔
      (Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits x - 1) / 2) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (Spec.Ffdh.candidateOf bits x) &&
        !Spec.RsaKeyGen.obviouslyComposite bits ((Spec.Ffdh.candidateOf bits x - 1) / 2)) = true := by
  have hs := shape_iff (x := x) hb1 hb2 hg
  obtain ⟨ho, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  obtain ⟨hql, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) ho hl hu
  generalize Spec.Ffdh.candidateOf bits x = c at hs ho hl hu hql ⊢
  have hq : (c - 1) / 2 = c / 2 := by omega_arith
  have big : 8161 < c := Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 1)) hl)
  have bigq : 8161 < c / 2 := by
    rw [← hq]
    exact Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 2)) hql)
  rw [trialN_spec big, trialN_spec bigq, ← hq]
  rw [hq] at hs
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs ⊢
  rw [hq]
  constructor
  · rintro ⟨a, b, c', d, e, f⟩
    exact ⟨⟨hs.mp ⟨a, b, d, e⟩, c'⟩, f⟩
  · rintro ⟨⟨h1, c'⟩, f⟩
    obtain ⟨a, b, d, e⟩ := hs.mpr h1
    exact ⟨a, b, c', d, e, f⟩

/-! ## Trial division of array 0 -/

/-- The count of entries, `1024 − 512 [bits ≤ 1024]`. -/
theorem trialCount_eq {bits : Nat} (hb : bits ≤ 8192) :
    BitVec.ofNat 64 1024 - (BitVec.ofNat 64 bits - BitVec.ofNat 64 1025) >>> 63 <<< 9 =
      BitVec.ofNat 64 (trialN bits) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, trialN]
  split <;> omega

/-- `MB` survives a change of header words `hBad` and `hTrialN` and of
registers but `a7`, `t0`, `s5` and `s6`, with `hBad` then zero iff `B'`. -/
theorem MB.step {p : PP} {T : Addr} {x : Nat} {B B' : Prop} {s t : State} {regs : List Reg} (h : MB p T x B s)
    (hf : Frm p.B [(208, 8), (200, 8)] s.mem t.mem) (k : Keep regs s t) (ksp : t.sp = s.sp)
    (h7 : Reg.a7 ∉ regs) (h0 : Reg.t0 ∉ regs) (h5 : Reg.s5 ∉ regs) (h6 : Reg.s6 ∉ regs)
    (hb : word t.mem p.B (8 * hBad) = 0#64 ↔ B') (sy : t.syms = s.syms) : MB p T x B' t := by
  have hdn := h.st.dims.n
  have hb2 := h.st.dims.b2
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have st := h.st.step (Frm.toMut hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact InMut.hdr (i := 26) (by decide)
    · exact InMut.hdr (i := 25) (by decide)) k ksp h6
  have ew : ∀ d, d + 8 ≤ 200 ∨ (216 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have hp := h.ph
  refine ⟨st, ⟨(k.gpr h7).trans hp.a7, (k.gpr h0).trans hp.t0, (k.gpr h5).trans hp.s5,
    (ew 248 (by decide)).trans hp.mbW, (ew 216 (by decide)).trans hp.kW, (ew 48 (by decide)).trans hp.wW,
    (ew 224 (by decide)).trans hp.strideW, fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj),
    (ew 168 (by decide)).trans hp.checksW, hp.k1, hp.k2, (ew 192 (by decide)).trans hp.topW⟩,
    (ew 152 (by decide)).trans h.u, ?_, hb, h.tab.step sy hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) k.2.1⟩
  rw [hf.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [hsl] <;> exact .inr (by decide)) (by rw [hsl]; omega_arith)]
  exact h.n

/-- The count of entries into `hTrialN`. -/
theorem MB.count {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} (h : MB p T x B s) :
    WP isa (.block [ldh .t3 hBits, .addi .t3 .t3 (-1025), .shift .srl .d .t3 .t3 63, .shift .sll .d .t3 .t3 9,
      .li .t4 1024, .sub .t3 .t4 .t3, sth .t3 hTrialN]) s fun u =>
      MB p T x B u ∧ u.mem.readW (p.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (trialN p.bits) := by
  have hb2 := h.st.dims.b2
  refine WP.mono_syms (WP.rdwr (WP.keep [.t3, .t4] (Q := fun u =>
      u.mem = s.mem.writeW (p.B + BitVec.ofNat 64 208) (BitVec.ofNat 64 (trialN p.bits)))
    (by simp only [ldh, sth, hBits, hTrialN]
        brun [h.st.s6, h.st.ld (d := 40) (by decide), h.st.al (d := 40) (by decide) (by decide),
          h.st.st (d := 208) (by decide), h.st.al (d := 208) (by decide) (by decide), h.st.args.bits',
          exec_li (show imm12 1024 by decide), trialCount_eq hb2])
    (by rfl) (by rfl))) fun u ⟨⟨um, ku⟩, _, _, usp⟩ syu => ⟨?_, by rw [um, rw_self]⟩
  have fu : Frm p.B [(208, 8)] s.mem u.mem := by
    rw [um]; exact frm_writeW (a := 208) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  exact h.step (fu.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp) ku usp
    (by decide) (by decide) (by decide) (by decide) (by
      rw [show word u.mem p.B (8 * hBad) = word s.mem p.B (8 * hBad) by
        rw [um]; exact rw_off _ _ _ (by decide) (by decide) (by decide)]
      exact h.bad) syu

/-- The table's address and the count. -/
theorem MB.trialA {p : PP} {x : Nat} {B : Prop} {T : Addr} {u : State} (h : MB p T x B u)
    (h208 : u.mem.readW (p.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (trialN p.bits)) :
    WP isa (.block [.lla .s9 TrialTable32.symbol, ldh .s10 hTrialN]) u fun v =>
      ((v.gpr .s9 = T ∧ v.gpr .s10 = BitVec.ofNat 64 (trialN p.bits) ∧ v.mem = u.mem) ∧
        Keep [.s9, .s10] u v) ∧ v.sp = u.sp := by
  refine WP.rdwr (WP.keep [.s9, .s10] ?_ (by rfl) (by rfl)) |>.mono fun v ⟨a, _, _, b⟩ => ⟨a, b⟩
  refine Steps.WP.cons exec_lla ?_
  simp only [ldh, hTrialN]
  brun [h.st.s6, h.st.ld (d := 208) (by decide), h.st.al (d := 208) (by decide) (by decide), h208, h.tab.sym]

/-- What RSA's loop needs, once the table's address and the count are in
`s9` and `s10`. -/
theorem MB.loopArgs {p : PP} {x : Nat} {B : Prop} {T : Addr} {u v : State} (h : MB p T x B u)
    (vm : v.mem = u.mem) (kv : Keep [.s9, .s10] u v) :
    Scr v p.B p.Z ∧ v.gpr .a7 = off p.B (slot (wOf p.bits) 0) ∧ v.gpr .t0 = BitVec.ofNat 64 (wOf p.bits) ∧
      VG.Proof.Mont.val32 v.mem p.B (slot (wOf p.bits) 0) (2 * wOf p.bits) = x ∧ 1 ≤ wOf p.bits ∧
      wOf p.bits < 2 ^ 31 ∧ slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z ∧ slot (wOf p.bits) 0 % 4 = 0 ∧
      1 ≤ trialN p.bits ∧ trialN p.bits ≤ 1024 ∧
      VG.Proof.RsaKeyGen.RISCV64.Trial.Tab v T (trialN p.bits) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hN : 1 ≤ trialN p.bits ∧ trialN p.bits ≤ 1024 := by unfold trialN; split <;> decide
  have hfit := h.tab.fit
  have hal := h.tab.al
  refine ⟨h.st.scr.congr kv.2.2, (kv.gpr (by decide)).trans h.ph.a7, (kv.gpr (by decide)).trans h.ph.t0,
    by rw [vm, ← VG.Proof.Mont.wordsVal_eq_val32, Pre.wordsVal_eq_wv]; exact h.n, by omega_arith, by omega_arith,
    by rw [hsl]; omega_arith, by rw [hsl], hN.1, hN.2, fun i hi => ⟨by rw [vm]; exact h.tab.tab i (by omega_arith),
      ⟨_, by rw [kv.2.1]; exact List.mem_append_left _ h.tab.rd, ?_⟩, ?_⟩⟩
  · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · have e8 : (T + BitVec.ofNat 64 (8 * i)).toNat = T.toNat + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_arith)]
      exact Nat.mod_eq_of_lt (by omega_arith)
    rw [e8]; omega_arith

/-- The loop's flag or'ed into `hBad`. -/
theorem MB.orBad {p : PP} {x : Nat} {B : Prop} {T : Addr} {u w : State} {n : Nat} (h : MB p T x B u)
    (w4 : w.gpr .a4 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix x n then 1 else 0))
    (wm : w.mem = u.mem) (kw : Keep (([.s9, .s10] : List Reg) ++ VG.Proof.RsaKeyGen.RISCV64.Trial.entryRegs) u w)
    (wsp : w.sp = u.sp) (syw : w.syms = u.syms) :
    WP isa (.block [ldh .t3 hBad, .logic .or .t3 .t3 .a4, sth .t3 hBad]) w
      (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false)) := by
  have l200 : InRegions (w.rd ++ w.wr) (p.B + BitVec.ofNat 64 200) 8 := by
    rw [kw.2.1, kw.2.2]; exact h.st.ld (d := 200) (by decide)
  have s200 : InRegions w.wr (p.B + BitVec.ofNat 64 200) 8 := by rw [kw.2.2]; exact h.st.st (d := 200) (by decide)
  have a200 := h.st.al (d := 200) (by decide) (by decide)
  have w6 : w.gpr .s6 = p.B := (kw.gpr (by decide)).trans h.st.s6
  have hold : w.mem.readW (p.B + BitVec.ofNat 64 200) 64 = word u.mem p.B 200 := by rw [wm]
  refine WP.mono_syms (WP.rdwr (WP.keep [.t3] (Q := fun t => t.mem = w.mem.writeW (p.B + BitVec.ofNat 64 200)
      (word u.mem p.B 200 ||| w.gpr .a4))
    (by simp only [ldh, sth, hBad]; brun [w6, l200, s200, a200, hold]) (by rfl) (by rfl)))
    fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ syt => ?_
  have fst : Frm p.B [(208, 8), (200, 8)] u.mem t.mem := by
    rw [tm, wm]
    exact frm_writeW (Frm.refl _ _ _) _ ⟨(200, 8), by simp, by decide, by decide⟩ (by decide)
  have hbad : word t.mem p.B (8 * hBad) = 0#64 ↔ B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false := by
    show t.mem.readW (p.B + BitVec.ofNat 64 200) 64 = 0#64 ↔ _
    rw [tm, rw_self, BitVec.or_eq_zero_iff, w4, ← h.bad]
    refine and_congr Iff.rfl ?_
    cases VG.Proof.RsaKeyGen.trialPrefix x n <;> decide
  exact h.step (regs := ([.s9, .s10] ++ VG.Proof.RsaKeyGen.RISCV64.Trial.entryRegs) ++ [.t3]) fst
    ((kw.trans kt).mono (by decide)) (tsp.trans wsp) (by decide) (by decide) (by decide) (by decide) hbad
    (syt.trans syw)

/-- Trial division of array 0: `hBad |=` the flag of one of the first
`trialN bits` entries dividing it. -/
theorem trialSieve_ok {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} (h : MB p T x B s) :
    WP isa trialSieve s (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x (trialN p.bits) = false)) := by
  unfold trialSieve VG.Impl.RsaKeyGen.RISCV64.Trial.trial
  refine WP.seq (WP.mono h.count fun u ⟨hu, h208⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono_syms (hu.trialA h208) fun v ⟨⟨⟨v9, v10, vm⟩, kv⟩, vsp⟩ syv => ?_))
  obtain ⟨vs, v7, v0, vc, w1, w2, hZ, ho, n1, n2, htab⟩ := hu.loopArgs vm kv
  refine WP.mono_syms (WP.rdwr (VG.Proof.RsaKeyGen.RISCV64.Trial.loop_ok vs v7 v0 vc w1 w2 hZ ho n1 n2 v9 htab
    v10)) fun w ⟨⟨⟨w4, wm⟩, kw⟩, _, _, wsp⟩ syw => ?_
  exact hu.orBad w4 (wm.trans vm) ((kv.trans kw).mono (by decide)) (wsp.trans vsp) (syw.trans syv)

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
