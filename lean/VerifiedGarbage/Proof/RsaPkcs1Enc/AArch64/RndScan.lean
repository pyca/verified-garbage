module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndSetup
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the scan

After `i` octets of the tape `randB s`, the scan has kept their nonzero
octets, `kept s i`, at the start of `PS` (`At`); one octet more (`step_ok`);
and the whole scan (`scan_ok`), which ends with `PS` full, the padding string
of `nonzeroPrefix`, or with the tape read.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Enc (nz nz_zero nz_ne nz_length_le)

/-- The kept octets after `i` octets of the tape. -/
abbrev kept (s : State) (i : Nat) : List Byte := nz ((randB s).take i)

theorem randB_getD {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) :
    (randB s).getD i 0 = s.mem (stackArg s 1 + BitVec.ofNat 64 i) := by
  simp [randB, Spec.Rsa.bytesAt, hi]

theorem randB_length (s : State) : (randB s).length = (stackArg s 2).toNat := by
  simp [randB, Spec.Rsa.bytesAt]

theorem take_succ_eq {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) :
    (randB s).take (i + 1) = (randB s).take i ++ [(randB s).getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]

theorem kept_succ {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) :
    kept s (i + 1) = if (randB s).getD i 0 = 0 then kept s i else kept s i ++ [(randB s).getD i 0] := by
  simp only [kept, take_succ_eq hi]
  split
  · rename_i h; rw [h, nz_zero]
  · rename_i h; exact nz_ne h _

theorem kept_zero (s : State) : kept s 0 = [] := by simp [kept, VG.Proof.RsaPkcs1Enc.nz_nil]

theorem getD_append_lt {l : List Byte} {j : Nat} (b : Byte) (h : j < l.length) :
    (l ++ [b]).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_eq (l : List Byte) (b : Byte) : (l ++ [b]).getD l.length 0 = b := by
  simp [List.getD_eq_getElem?_getD]

theorem ofNat_sub_one {n j : Nat} (hj : j < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (j + 1)) :=
  Bytes.counter_step hj hn

/-- After `i` octets of the tape, from the state `t₀` after `setup`. -/
structure At (s t₀ : State) (i : Nat) (u : State) : Prop where
  fr : InFrame s u
  keep : Keeps [.x9, .x11, .x12, .x14, .x16, .x17] t₀ u
  buf : ∀ j < (kept s i).length, u.mem (off (Q s) (oBuf + j)) = (kept s i).getD j 0
  x11 : u.gpr .x11 = stackArg s 1 + BitVec.ofNat 64 i
  x12 : u.gpr .x12 = BitVec.ofNat 64 ((stackArg s 2).toNat - i)
  x14 : u.gpr .x14 = off (Q s) (oBuf + (kept s i).length)
  x16 : u.gpr .x16 = BitVec.ofNat 64 (psLen s - (kept s i).length)
  hi : i ≤ (stackArg s 2).toNat
  hc : (kept s i).length ≤ psLen s

theorem zero_byte (b : Byte) : (b.setWidth 64 == 0) = decide (b = 0) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq, Bytes.setWidth64_eq_zero]

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  show eval (.zero .x r) s = _
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- After `load`, from `t`. -/
structure LoadStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  x17 : u.gpr .x17 = (t.mem (t.gpr .x11)).setWidth 64
  x11 : u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1
  x12 : u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x17 → u.gpr r = t.gpr r

theorem load_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block load) t (LoadStep t) := by
  apply WP.of_runBlock
  simp only [load, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.load,
    State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, reduceCtorEq, ite_false, hr,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h11 h12 h17 => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, BitVec.add_zero,
      Bytes.read_one, Bytes.byte64]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h11, h12, h17, ite_false]

/-- After `keep`, from `t`. -/
structure KeepStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr .x14) 1 ((t.gpr .x17).setWidth 8)
  x14 : u.gpr .x14 = t.gpr .x14 + BitVec.ofNat 64 1
  x16 : u.gpr .x16 = t.gpr .x16 - BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x14 → r ≠ .x16 → u.gpr r = t.gpr r

theorem keep_ok {t : State} (hw : InRegions t.wr (t.gpr .x14 + BitVec.ofNat 64 0) 1) :
    WP isa (.block keep) t (KeepStep t) := by
  apply WP.of_runBlock
  simp only [keep, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, reduceCtorEq, ite_false, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h14 h16 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h14, h16, ite_false]

theorem mul_ok (t : State) :
    WP isa (.block [.mul .x .x9 .x12 .x16]) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.v = t.v ∧ u.mem = t.mem ∧ u.gpr .x9 = t.gpr .x12 * t.gpr .x16 ∧ ∀ r, r ≠ .x9 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write,
    RegUpd.v_write, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, fun r h9 => ?_⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h9, ite_false]

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem byte_rt8 (b : Byte) : BitVec.setWidth 8 (b.setWidth 64) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

theorem mul_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 a * BitVec.ofNat 64 b != 0) = decide (¬ (a = 0 ∨ b = 0)) := by
  have hab : a * b < 2 ^ 64 := by
    calc a * b < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by decide
  have ht : (BitVec.ofNat 64 a * BitVec.ofNat 64 b).toNat = a * b := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt hab]
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_eq, BitVec.toNat_eq, ht, ← Nat.mul_eq_zero]
  rfl

/-- The rand octet `i`, unchanged in `u`. -/
theorem rand_byte' {P : Nat} {s u : State} (hp : RPre P s) (hf : InFrame s u) {i : Nat}
    (hi : i < (stackArg s 2).toNat) : u.mem (stackArg s 1 + BitVec.ofNat 64 i) = (randB s).getD i 0 := by
  rw [randB_getD hi]
  have hd : (randR s).Disjoint ⟨Q s, 1104⟩ := fun x h₁ h₂ =>
    hp.dKr x (frame_sub (P := P) s (d := 0) (n := 1104) (by decide) x (by rw [off, add_zero']; exact h₂)) h₁
  have hw := hp.wR
  have hc : (randR s).Contains (stackArg s 1 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  exact hf.fr _ fun r hr => by rw [List.mem_singleton.mp hr]; exact hd _ hc

theorem keeps_load {u v : State} (hv : LoadStep u v) : Keeps [.x11, .x12, .x17] u v := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hv.other r hr.1 hr.2.1 hr.2.2

theorem keeps_keep {v w : State} (hw : KeepStep v w) : Keeps [.x14, .x16] v w := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact hw.other r hr.1 hr.2

/-- The branch on octet `i`, after its load. -/
theorem branch_ok {P : Nat} {s t₀ u v : State} (hp : RPre P s) {i : Nat} (hI : At s t₀ i u)
    (hv : LoadStep u v) (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) :
    WP isa (.ite (.zero .x .x17) (.block []) (.block keep)) v (At s t₀ (i + 1)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hlen := (stackArg s 2).isLt
  have hoB : oBuf = 64 := rfl
  have hoP : oPs = 48 := rfl
  have h17 : v.gpr .x17 = ((randB s).getD i 0).setWidth 64 := by
    rw [hv.x17, hI.x11, rand_byte' hp hI.fr hi]
  have kv := keeps_load hv
  have kuv : Keeps [.x9, .x11, .x12, .x14, .x16, .x17] t₀ v :=
    (hI.keep.trans kv).mono (by simp)
  have hx11 : v.gpr .x11 = stackArg s 1 + BitVec.ofNat 64 (i + 1) := by rw [hv.x11, hI.x11, add_add']
  have hx12 : v.gpr .x12 = BitVec.ofNat 64 ((stackArg s 2).toNat - (i + 1)) := by
    rw [hv.x12, hI.x12, Bytes.counter_step hi hlen]
  have hx14 : v.gpr .x14 = off (Q s) (oBuf + (kept s i).length) :=
    (hv.other _ (by decide) (by decide) (by decide)).trans hI.x14
  have hx16 : v.gpr .x16 = BitVec.ofNat 64 (psLen s - (kept s i).length) :=
    (hv.other _ (by decide) (by decide) (by decide)).trans hI.x16
  have hfv : InFrame s v := ⟨hv.sp.trans hI.fr.sp, hv.rd.trans hI.fr.rd, hv.wr.trans hI.fr.wr,
    hv.v.trans hI.fr.v, by rw [hv.mem]; exact hI.fr.fr, by rw [hv.mem]; exact hI.fr.ps,
    by rw [hv.mem]; exact hI.fr.lr⟩
  by_cases hz : (randB s).getD i 0 = 0
  · have hk : kept s (i + 1) = kept s i := by rw [kept_succ hi, ite_eq_left hz]
    refine WP.ite true (by rw [eval_zero, h17, zero_byte, decide_eq_true hz]) (fun _ => WP.block_nil ?_)
      (fun h => absurd h (by decide))
    refine ⟨hfv, kuv, fun j hj => ?_, hx11, hx12, by rw [hk]; exact hx14, by rw [hk]; exact hx16, by omega,
      by rw [hk]; exact hI.hc⟩
    rw [hk] at hj ⊢; rw [hv.mem]; exact hI.buf j hj
  · have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    have hl : (kept s (i + 1)).length = (kept s i).length + 1 := by rw [hk]; simp
    have hw : InRegions v.wr (v.gpr .x14 + BitVec.ofNat 64 0) 1 := by
      rw [add_zero', hx14, hfv.wr]
      exact frame_in (by unfold oBuf frameBytes; omega)
    refine WP.ite false (by rw [eval_zero, h17, zero_byte, decide_eq_false hz]) (fun h => absurd h (by decide))
      fun _ => WP.mono (keep_ok hw) fun w hw' => ?_
    have hm : w.mem = v.mem.write (off (Q s) (oBuf + (kept s i).length)) 1 ((randB s).getD i 0) := by
      rw [hw'.mem, hx14, h17, byte_rt8]
    have kw := keeps_keep hw'
    refine ⟨⟨hw'.sp.trans hfv.sp, hw'.rd.trans hfv.rd, hw'.wr.trans hfv.wr, hw'.v.trans hfv.v, ?_, ?_, ?_⟩,
      (kuv.trans kw).mono (by simp), fun j hj => ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
    · rw [hm]
      exact hfv.fr.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold oBuf; omega) (by omega))
    · rw [hm, Bytes.readW_write_sep (Offset.sep _ (.inl (by unfold oPs oBuf; omega)) (by omega) (by omega))
        (by decide)]
      exact hfv.ps
    · rw [hm, Bytes.readW_write_sep (Offset.sep _ (.inr (by unfold oBuf; omega)) (by omega) (by omega))
        (by decide)]
      exact hfv.lr
    · rw [hm, hk]
      rw [hl] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)), getD_append_lt _ hj]
        rw [hv.mem]; exact hI.buf j hj
      · rw [Bytes.write1_self, getD_append_eq]
    · rw [hw'.other _ (by decide) (by decide)]; exact hx11
    · rw [hw'.other _ (by decide) (by decide)]; exact hx12
    · rw [hw'.x14, hx14, hl, off, off, add_add', Nat.add_assoc]
    · rw [hw'.x16, hx16, hl, Bytes.counter_step hc (by omega)]

/-- One octet of the scan, with fewer than `psLen` octets kept and octets
left: `At` for `i + 1`, and `x9` zero if `PS` is full or the tape has
ended. -/
theorem step_ok {P : Nat} {s t₀ u : State} (hp : RPre P s) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) :
    WP isa step u fun x => At s t₀ (i + 1) x ∧
      (x.gpr .x9 != 0) = decide (¬ ((kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat)) := by
  have hP := hp.ps
  have hrl := hp.randLen
  have hwR := hp.wR
  have hr : InRegions (u.rd ++ u.wr) (u.gpr .x11 + BitVec.ofNat 64 0) 1 :=
    ⟨randR s, by rw [hI.fr.rd, hp.hrd]; simp, by
      rw [add_zero', hI.x11]; exact Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (load_ok hr) fun v hv => WP.seq (WP.mono (branch_ok hp hI hv hi hc) fun w hw =>
    WP.mono (mul_ok w) fun x ⟨hrd, hwr, hsp, hvv, hmem, h9, ho⟩ => ?_))
  have k9 : Keeps [.x9] w x := fun r hr => ho r (by simpa using hr)
  refine ⟨⟨⟨hsp.trans hw.fr.sp, hrd.trans hw.fr.rd, hwr.trans hw.fr.wr, hvv.trans hw.fr.v,
    by rw [hmem]; exact hw.fr.fr, by rw [hmem]; exact hw.fr.ps, by rw [hmem]; exact hw.fr.lr⟩,
    (hw.keep.trans k9).mono (by simp), fun j hj => by rw [hmem]; exact hw.buf j hj,
    by rw [ho _ (by decide)]; exact hw.x11, by rw [ho _ (by decide)]; exact hw.x12,
    by rw [ho _ (by decide)]; exact hw.x14, by rw [ho _ (by decide)]; exact hw.x16, hw.hi, hw.hc⟩, ?_⟩
  have := hw.hi
  have := hw.hc
  rw [h9, hw.x12, hw.x16, mul_ne (by omega) (by omega), decide_eq_decide]
  omega

/-- `PS` filled at octet `i`: the padding string of `nonzeroPrefix`. -/
theorem prefix_of_fill {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat)
    (hc : (kept s i).length < psLen s) (hf : (kept s (i + 1)).length = psLen s) :
    Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s (i + 1), i + 1) := by
  have hz : (randB s).getD i 0 ≠ 0 := by
    intro hz; rw [kept_succ hi, ite_eq_left hz] at hf; omega
  have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
  have hl : i < (randB s).length := by rw [randB_length]; exact hi
  have e : randB s = (randB s).take i ++ (randB s).getD i 0 :: (randB s).drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i (randB s)]
    congr 1
    rw [List.drop_eq_getElem_cons hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have hlen : ((randB s).take i).length = i := by rw [List.length_take]; omega
  rw [e, VG.Proof.RsaPkcs1Enc.nonzeroPrefix_last _ hz (by rw [hk] at hf; simpa using hf), hk, hlen]

/-- What the scan leaves: after `i` octets, `PS` full with the padding
string, or the tape read with fewer nonzero octets. -/
def Done (s t₀ : State) (u : State) : Prop :=
  ∃ i, At s t₀ i u ∧ (((kept s i).length = psLen s ∧
      Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) ∨
    (i = (stackArg s 2).toNat ∧ (kept s i).length < psLen s))

/-- The loop's invariant, with the octets left as its measure. -/
def LoopInv (s t₀ : State) (n : Nat) (u : State) : Prop :=
  ∃ i, n = (stackArg s 2).toNat - i ∧ At s t₀ i u ∧ i < (stackArg s 2).toNat ∧ (kept s i).length < psLen s

theorem at_zero {P : Nat} {s t₀ : State} (hp : RPre P s) (hb : Before s t₀) : At s t₀ 0 t₀ := by
  have hP := hp.ps
  refine ⟨hb.toInFrame, Keeps.refl _ _, fun j hj => absurd hj (by simp [kept_zero]), ?_, ?_, ?_, ?_,
    Nat.zero_le _, by rw [kept_zero]; simp⟩
  · rw [hb.x11, add_zero']
  · rw [hb.x12, Nat.sub_zero]; exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  · rw [hb.x14, kept_zero]; rfl
  · rw [hb.x16, kept_zero]; rfl

theorem scan_ok {P : Nat} {s t₀ : State} (hp : RPre P s) (hb : Before s t₀) :
    WP isa scan t₀ (Done s t₀) := by
  have hP := hp.ps
  have h0 := at_zero hp hb
  by_cases hl : stackArg s 2 = 0
  · refine WP.ite false (by rw [Bytes.eval_nonzero, hb.x12, hl]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ?_
    have hl' : (stackArg s 2).toNat = 0 := by rw [hl]; rfl
    exact ⟨0, h0, .inr ⟨hl'.symm, by rw [kept_zero]; simp; omega⟩⟩
  have hl' : 0 < (stackArg s 2).toNat := by
    rcases Nat.eq_zero_or_pos (stackArg s 2).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
    · exact h
  refine WP.ite true (by rw [Bytes.eval_nonzero, hb.x12, bne_iff_ne.mpr hl]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hinit : LoopInv s t₀ ((stackArg s 2).toNat - 0) t₀ := ⟨0, rfl, h0, hl', by rw [kept_zero]; simp; omega⟩
  refine WP.loop (LoopInv s t₀) ?_ _ _ hinit
  rintro n u ⟨i, rfl, hI, hi, hc⟩
  refine WP.mono (step_ok hp hI hi hc) fun u' ⟨hI', hz'⟩ => ?_
  by_cases hstop : (kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat
  · refine .inl ⟨by rw [Bytes.eval_nonzero, hz', decide_eq_false (not_not_intro hstop)], ⟨i + 1, hI', ?_⟩⟩
    by_cases hf : (kept s (i + 1)).length = psLen s
    · exact .inl ⟨hf, prefix_of_fill hi hc hf⟩
    · exact .inr ⟨hstop.resolve_left hf, by have := hI'.hc; omega⟩
  · refine .inr ⟨by rw [Bytes.eval_nonzero, hz', decide_eq_true hstop], _, by omega, i + 1, rfl, hI', by omega,
      by have := hI'.hc; omega⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
