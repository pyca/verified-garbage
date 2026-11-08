module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Keep
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.MainShape
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests

-- separate module: its proofs build in parallel with those of `TestsFn`, which `Main` also imports

/-!
# An FFDH parameter candidate on PPC64LE: RSA's trial division

`TabIn`: RSA's table of trial division (`VG_RSA_KEYGEN_TRIAL32`) at `T`, its
region readable and apart from the working space, which no piece of the
candidate changes (`TabIn.step`). `trialSieve_ok`: the count of entries for
p's width in `hTrialN`, the table's address (`adrSym`), RSA's loop
(`Trial.loop_ok`), and its flag or'ed into `hBad`: clear exactly when no entry
of the first `trialN bits` divides the value in array 0.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.entry)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- The table at `T`, where the state names it, readable, and apart from
the working space of `Z` bytes at `B`. -/
structure TabIn (B : Addr) (Z : Nat) (T : Addr) (s : State) : Prop where
  sym : s.syms TrialTable32.symbol = T
  tab : TabAt T s.mem
  rd : (⟨T, 8192⟩ : Region) ∈ s.rd
  fit : T.toNat + 8192 ≤ 2 ^ 64
  dj : (⟨T, 8192⟩ : Region).Disjoint ⟨B, Z⟩

/-- The table survives a change of the working space. -/
theorem TabIn.step {B T : Addr} {Z : Nat} {s t : State} {rs : List (Nat × Nat)}
    (h : TabIn B Z T s) (sy : t.syms = s.syms) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (krd : t.rd = s.rd) : TabIn B Z T t := by
  refine ⟨sy ▸ h.sym, fun i hi => ?_, by rw [krd]; exact h.rd, h.fit, h.dj⟩
  rw [← h.tab i hi]
  refine Mem.readW_congr fun j hj => (hf _ fun r hr' => .inr ?_)
  have hj' : j < 8 := by omega
  have hc : (⟨T, 8192⟩ : Region).Contains (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) 1 := by
    simp only [Region.Contains, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.ofNat_add_ofNat,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hn := h.dj _ hc
  simp only [Region.Contains, Nat.not_le] at hn
  have := hr r hr'
  unfold ofs
  omega

theorem trialN_range {bits : Nat} : 1 ≤ trialN bits ∧ trialN bits ≤ 1024 := by unfold trialN; split <;> decide

/-- The count of entries, `1024 − 512 [bits ≤ 1024]`. -/
theorem trialCount_eq {bits : Nat} (hb : bits ≤ 8192) :
    BitVec.ofNat 64 1024 - (BitVec.ofNat 64 bits - BitVec.ofNat 64 1025) >>> 63 <<< 9 =
      BitVec.ofNat 64 (trialN bits) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, trialN]
  split <;> omega

/-- In p's working space, with `x` in array 0, `hBad` zero iff `B`, and
the table at `T`. -/
structure MB (p : PP) (T : Addr) (x : Nat) (B : Prop) (t : State) : Prop where
  st : St p t
  ph : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t
  u : word t.mem p.B 152 = BitVec.ofNat 64 p.L
  n : wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = x
  bad : word t.mem p.B (8 * hBad) = 0#64 ↔ B
  tab : TabIn p.B p.Z T t

/-- `St.step` without the link register, which `adrSym` writes. -/
theorem St.step' {p : PP} {s t : State} {regs : List Reg} (h : St p s) (hf : Frm p.B (mutR p.n) s.mem t.mem)
    (kg : ∀ r, r ∉ regs → t.gpr r = s.gpr r) (krd : t.rd = s.rd) (kwr : t.wr = s.wr) (ksp : t.sp = s.sp)
    (h31 : Reg.r31 ∉ regs := by decide) (h2 : Reg.r2 ∉ regs := by decide) : St p t where
  scr := h.scr.congr kwr
  r31 := (kg .r31 h31).trans h.r31
  args := h.args.frm hf rfl
  bufs := by
    have hr : ∀ r ∈ mutR p.n, r.1 + r.2 ≤ p.Z := fun r hr => by
      have := h.dims.n
      simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only [PP.Z, saveBytes] <;> omega_arith
    have b := h.bufs
    exact ⟨by rw [krd, kwr]; exact b.rdR, b.sepR, by rw [bytes_frm hf hr b.sepR]; exact b.bR,
      by rw [out_frm hf hr b.sepO (by have := b.scrO.nowrap; omega_arith)]; exact b.bO, b.scrO.congr kwr, b.sepO,
      b.scrU.congr kwr, b.sepU, b.stkR, b.stkO, b.stkU, b.dOU⟩
  dims := h.dims
  ws := by rw [kwr]; exact h.ws
  sp := ksp.trans h.sp
  stk := h.stk
  stkB := h.stkB
  save := fun i hi => by
    have := h.dims.n; have := h.dims.n'; have := h.dims.b1
    refine (hf.word_eq (fun r hr => .inr ?_) (by simp only [saveBytes]; omega_arith)).trans (h.save i hi)
    simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [saveBytes, PP.L] at * <;> omega_arith
  r2 := (kg .r2 h2).trans h.r2

/-- `MB` survives a change of header words `hBad` and `hTrialN` and of
registers but `r2`, `r10`, `r11`, `r29` and `r31`, with `hBad` then zero iff
`B'`. -/
theorem MB.step {p : PP} {T : Addr} {x : Nat} {B B' : Prop} {s t : State} {regs : List Reg} (h : MB p T x B s)
    (hf : Frm p.B [(208, 8), (200, 8)] s.mem t.mem) (kg : ∀ r, r ∉ regs → t.gpr r = s.gpr r)
    (krd : t.rd = s.rd) (kwr : t.wr = s.wr) (ksp : t.sp = s.sp) (h2 : Reg.r2 ∉ regs)
    (h10 : Reg.r10 ∉ regs) (h11 : Reg.r11 ∉ regs) (h29 : Reg.r29 ∉ regs) (h31 : Reg.r31 ∉ regs)
    (hb : word t.mem p.B (8 * hBad) = 0#64 ↔ B') (sy : t.syms = s.syms) : MB p T x B' t := by
  have hdn := h.st.dims.n
  have hn' := h.st.dims.n'
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hsl : slot (wOf p.bits) 0 = 256 := by simp [slot, hdrBytes]
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hw128 : wOf p.bits ≤ 128 := by rw [hwe]; omega_arith
  have st := h.st.step' (Frm.toMut hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact InMut.hdr (i := 26) (by decide)
    · exact InMut.hdr (i := 25) (by decide)) kg krd kwr ksp h31 h2
  have ew : ∀ d, d + 8 ≤ 200 ∨ 216 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.B d = word s.mem p.B d := fun d hd hd' =>
    hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) hd'
  refine ⟨st, h.ph.keep (kg _ h10) (kg _ h11) (kg _ h29) fun d hd => ew d ?_ ?_,
    (ew 152 (by decide) (by decide)).trans h.u, ?_, hb, h.tab.step sy hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) krd⟩
  · have es : ∀ j, slot (wOf p.bits) j = 256 + j * (8 * (wOf p.bits + 2)) := fun _ => rfl
    unfold Read at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      first | omega_arith | (rw [es]; omega_arith)
  · have es : ∀ j, slot (wOf p.bits) j = 256 + j * (8 * (wOf p.bits + 2)) := fun _ => rfl
    unfold Read at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      first | omega_arith | (rw [es]; simp only [PP.Z] at *; omega_arith)
  · rw [hf.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [hsl] <;> exact .inr (by decide)) (by rw [hsl]; omega_arith)]
    exact h.n

/-- The count of entries into `hTrialN`. -/
theorem MB.count {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} (h : MB p T x B s) :
    WP isa (.block [ldh .r3 hBits, .subi .r3 .r3 1025, .lsr .d .r3 .r3 63, .lsl .r3 .r3 9, .li .r4 1024,
      .sub .r3 .r4 .r3, sth .r3 hTrialN]) s fun u =>
      MB p T x B u ∧ u.mem.readW (p.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (trialN p.bits) := by
  have hb2 := h.st.dims.b2
  have l40 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 40) 8 := h.st.ld (d := 40) (by decide)
  have s208 : InRegions s.wr (p.B + BitVec.ofNat 64 208) 8 := h.st.st (d := 208) (by decide)
  have hbits : s.mem.readW (p.B + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 p.bits := h.st.args.bits'
  refine WP.mono_syms (WP.mono (WP.keep [.r3, .r4] (Q := fun u =>
      u.mem = s.mem.writeW (p.B + BitVec.ofNat 64 208) (BitVec.ofNat 64 (trialN p.bits)))
    (by simp only [ldh, sth, hBits, hTrialN]; prun [h.st.r31, l40, s208, hbits, trialCount_eq hb2]) (by decide))
    fun u hu => hu) fun u ⟨um, ku⟩ syu => ⟨?_, by rw [um, rw_self]⟩
  have fu : Frm p.B [(208, 8)] s.mem u.mem := by
    rw [um]; exact frm_writeW (a := 208) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  exact h.step (fu.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp) ku.gpr ku.rd ku.wr ku.sp
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      rw [show word u.mem p.B (8 * hBad) = word s.mem p.B (8 * hBad) by
        rw [um]; exact rw_off _ _ _ (by decide) (by decide) (by decide)]
      exact h.bad) syu

/-- The table's address and the count. -/
theorem MB.trialA {p : PP} {x : Nat} {B : Prop} {T : Addr} {u : State} {N : Nat} (h : MB p T x B u)
    (h208 : u.mem.readW (p.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 N) :
    WP isa (.block [.adrSym .r23 TrialTable32.symbol, ldh .r24 hTrialN]) u fun v =>
      (v.gpr .r23 = T ∧ v.gpr .r24 = BitVec.ofNat 64 N ∧ v.mem = u.mem) ∧
      (∀ r, r ∉ [Reg.r23, Reg.r24] → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      v.syms = u.syms := by
  have l208 : InRegions (u.rd ++ u.wr) (p.B + BitVec.ofNat 64 208) 8 := h.st.ld (d := 208) (by decide)
  refine WP.cons (exec_adrSym (by decide)) ?_
  simp only [ldh, hTrialN]
  prun [h.st.r31, l208, h208, h.tab.sym]
  refine ⟨fun r hr => ?_, rfl⟩
  have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
  have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
  simp only [h1, h2, ↓reduceIte]

/-- What RSA's loop needs, once the table's address and the count are in
`r23` and `r24`. -/
theorem MB.loopArgs {p : PP} {x : Nat} {B : Prop} {T : Addr} {u v : State} {N : Nat} (h : MB p T x B u)
    (vm : v.mem = u.mem) (vg : ∀ r, r ∉ [Reg.r23, Reg.r24] → v.gpr r = u.gpr r) (vrd : v.rd = u.rd)
    (vwr : v.wr = u.wr) (hN : 1 ≤ N ∧ N ≤ 1024) :
    Scr v p.B p.Z ∧ v.gpr .r10 = off p.B (slot (wOf p.bits) 0) ∧
      v.gpr .r11 = BitVec.ofNat 64 (2 * wOf p.bits) ∧
      VG.Proof.Mont.val32 v.mem p.B (slot (wOf p.bits) 0) (2 * wOf p.bits) = x ∧ 1 ≤ wOf p.bits ∧
      wOf p.bits < 2 ^ 31 ∧ slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z ∧ 1 ≤ N ∧
      N ≤ 1024 ∧
      (∀ i < N, v.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 =
          BitVec.ofNat 64 (TrialTable32.entry i) ∧ InRegions (v.rd ++ v.wr) (T + BitVec.ofNat 64 (8 * i)) 8) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hn' := h.st.dims.n'
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := by simp [slot, hdrBytes]
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  refine ⟨h.st.scr.congr vwr, by rw [vg _ (by decide)]; exact h.ph.r10, by rw [vg _ (by decide)]; exact h.ph.r11,
    by rw [vm, Pre.val32_eq_wv]; exact h.n, by omega_arith, by omega_arith, by rw [hsl]; omega_arith, hN.1, hN.2,
    fun i hi => ⟨by rw [vm]; exact h.tab.tab i (by omega_arith), ?_⟩⟩
  refine ⟨_, by rw [vrd]; exact List.mem_append_left _ h.tab.rd, ?_⟩
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := h.tab.fit
  rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- The loop's flag or'ed into `hBad`. -/
theorem MB.orBad {p : PP} {x : Nat} {B : Prop} {T : Addr} {u w : State} {n : Nat} (h : MB p T x B u)
    (w22 : w.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix x n then 1 else 0))
    (wm : w.mem = u.mem)
    (wg : ∀ r, r ∉ [Reg.r23, Reg.r24] ++ VG.Proof.RsaKeyGen.PPC64LE.Trial.entryRegs → w.gpr r = u.gpr r)
    (wrd : w.rd = u.rd) (wwr : w.wr = u.wr) (wsp : w.sp = u.sp) (syw : w.syms = u.syms) :
    WP isa (.block [ldh .r5 hBad, .logic .or .r5 .r5 .r22, sth .r5 hBad]) w
      (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false)) := by
  have l200 : InRegions (w.rd ++ w.wr) (p.B + BitVec.ofNat 64 200) 8 := by
    rw [wrd, wwr]; exact h.st.ld (d := 200) (by decide)
  have s200 : InRegions w.wr (p.B + BitVec.ofNat 64 200) 8 := by rw [wwr]; exact h.st.st (d := 200) (by decide)
  have w31 : w.gpr .r31 = p.B := (wg _ (by decide)).trans h.st.r31
  have hold : w.mem.readW (p.B + BitVec.ofNat 64 200) 64 = word u.mem p.B 200 := by rw [wm]
  refine WP.mono_syms (WP.mono (WP.keep [.r5] (Q := fun t => t.mem = w.mem.writeW (p.B + BitVec.ofNat 64 200)
      (word u.mem p.B 200 ||| w.gpr .r22))
    (by simp only [ldh, sth, hBad]; prun [w31, l200, s200, hold]) (by decide)) fun t h => h)
    fun t ⟨tm, kt⟩ syt => ?_
  have fst : Frm p.B [(208, 8), (200, 8)] u.mem t.mem := by
    rw [tm, wm]
    exact frm_writeW (Frm.refl _ _ _) _ ⟨(200, 8), by simp, by decide, by decide⟩ (by decide)
  have hbad : word t.mem p.B (8 * hBad) = 0#64 ↔ B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false := by
    show t.mem.readW (p.B + BitVec.ofNat 64 200) 64 = 0#64 ↔ _
    rw [tm, rw_self, BitVec.or_eq_zero_iff, w22, ← h.bad]
    refine and_congr Iff.rfl ?_
    cases VG.Proof.RsaKeyGen.trialPrefix x n <;> decide
  exact h.step (regs := ([.r23, .r24] ++ VG.Proof.RsaKeyGen.PPC64LE.Trial.entryRegs) ++ [.r5]) fst
    (fun r hr => (kt.gpr r fun h' => hr (List.mem_append_right _ h')).trans (wg r fun h' => hr
      (List.mem_append_left _ h')))
    (kt.rd.trans wrd) (kt.wr.trans wwr) (kt.sp.trans wsp)
    (by decide) (by decide) (by decide) (by decide) (by decide) hbad (syt.trans syw)

/-- Trial division of array 0: `hBad |=` the flag of one of the first
`trialN bits` entries dividing it. -/
theorem trialSieve_ok {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} (h : MB p T x B s) :
    WP isa trialSieve s (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x (trialN p.bits) = false)) := by
  unfold trialSieve VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine WP.seq (WP.mono h.count fun u ⟨hu, h208⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (hu.trialA h208) fun v ⟨⟨v23, v24, vm⟩, vg, vrd, vwr, vsp, syv⟩ => ?_))
  obtain ⟨vs, v10, v11, vc, w1, w2, hZ, n1, n2, htab⟩ := hu.loopArgs vm vg vrd vwr trialN_range
  refine WP.mono_syms (VG.Proof.RsaKeyGen.PPC64LE.Trial.loop_ok vs v10 v11 vc w1 w2 hZ n1 n2 v23 htab v24)
    fun w ⟨⟨w22, wm⟩, kw⟩ syw => ?_
  exact hu.orBad w22 (wm.trans vm) (fun r hr => (kw.gpr r fun h' => hr (List.mem_append_right _ h')).trans
    (vg r fun h' => hr (List.mem_append_left _ h'))) (kw.rd.trans vrd) (kw.wr.trans vwr) (kw.sp.trans vsp)
    (syw.trans syv)

/-- `hTrialN := n`. -/
theorem MB.countN {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} (h : MB p T x B s) (n : Nat)
    (hn : n < 2 ^ 15) :
    WP isa (.block [.li .r3 n, sth .r3 hTrialN]) s fun u =>
      MB p T x B u ∧ u.mem.readW (p.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by
  have s208 : InRegions s.wr (p.B + BitVec.ofNat 64 208) 8 := h.st.st (d := 208) (by decide)
  refine WP.mono_syms (WP.mono (WP.keep [.r3] (Q := fun u =>
      u.mem = s.mem.writeW (p.B + BitVec.ofNat 64 208) (BitVec.ofNat 64 n))
    (by simp only [sth, hTrialN]; prun [h.st.r31, s208, exec_li hn]) (by rfl))
    fun u hu => hu) fun u ⟨um, ku⟩ syu => ⟨?_, by rw [um, rw_self]⟩
  have fu : Frm p.B [(208, 8)] s.mem u.mem := by
    rw [um]; exact frm_writeW (a := 208) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  exact h.step (fu.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp) ku.gpr ku.rd ku.wr ku.sp
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      rw [show word u.mem p.B (8 * hBad) = word s.mem p.B (8 * hBad) by
        rw [um]; exact rw_off _ _ _ (by decide) (by decide) (by decide)]
      exact h.bad) syu

/-- Trial division of array 0 by the first `n` entries only. -/
theorem trialSieveN_ok {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} {n : Nat} (h : MB p T x B s)
    (hn : 1 ≤ n) (hn' : n ≤ 1024) :
    WP isa (trialSieveN n) s (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false)) := by
  unfold trialSieveN VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine WP.seq (WP.mono (h.countN n (by omega)) fun u ⟨hu, h208⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (hu.trialA h208) fun v ⟨⟨v23, v24, vm⟩, vg, vrd, vwr, vsp, syv⟩ => ?_))
  obtain ⟨vs, v10, v11, vc, w1, w2, hZ, n1, n2, htab⟩ := hu.loopArgs vm vg vrd vwr ⟨hn, hn'⟩
  refine WP.mono_syms (VG.Proof.RsaKeyGen.PPC64LE.Trial.loop_ok vs v10 v11 vc w1 w2 hZ n1 n2 v23 htab v24)
    fun w ⟨⟨w22, wm⟩, kw⟩ syw => ?_
  exact hu.orBad w22 (wm.trans vm) (fun r hr => (kw.gpr r fun h' => hr (List.mem_append_right _ h')).trans
    (vg r fun h' => hr (List.mem_append_left _ h'))) (kw.rd.trans vrd) (kw.wr.trans vwr) (kw.sp.trans vsp)
    (syw.trans syv)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
