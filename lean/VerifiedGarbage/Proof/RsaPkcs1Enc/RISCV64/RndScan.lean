module

-- separate module: the scan's proofs build in parallel with those of the call and the two ends (`RndCalls`)

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on RISC-V: the setup and the scan

`InF s t`: in the frame, what the restores need and memory changed only in
the stack and the writable buffers. `setup_ok`: the saves, `psLen` in `s1`
and the scan's registers (`Before`). After `i` octets of the tape, the scan
has kept their nonzero octets, `kept s i`, at the start of `PS` (`At`); it
goes on while it has kept fewer than `psLen s` and has octets left
(`step_ok`), and ends with `PS` full, the padding string of
`nonzeroPrefix`, or with the tape read (`scan_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Rnd

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64 VG.WriteBytes
open VG.Impl.RsaPkcs1Enc.RISCV64.Random
open VG.Proof.RsaPkcs1Enc (nz nz_zero nz_ne nz_length_le)

/-! ## The setup -/

/-- After the setup. -/
structure Before (s t : State) : Prop extends InF s t where
  g : ∀ r ∈ argRegs, t.gpr r = s.gpr r
  s1 : t.gpr .s1 = BitVec.ofNat 64 (psLen s)
  t1 : t.gpr .t1 = psA s
  t3 : t.gpr .t3 = stackArg s 1
  t4 : t.gpr .t4 = stackArg s 2
  frK : Frame [kR s] s.mem t.mem

theorem psLen_eq {s : State} (hp : RPre s) :
    s.gpr .a4 - stackArg s 0 - BitVec.ofNat 64 3 = BitVec.ofNat 64 (psLen s) := by
  have := hp.ml
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h4 := (s.gpr .a4).isLt
  have h0 := (stackArg s 0).isLt
  unfold psLen
  omega

theorem setup_ok {s u : State} (hp : RPre s) (hsp : u.sp = fb s) (hwr : u.wr = kR s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, u.gpr r = s.gpr r) :
    WP isa (.block setup) u fun t => Before s t ∧ t.gpr .t2 = 0 ∧ t.gpr .t5 = 0 := by
  have hfa := fb_al hp.spal (sp1' hp)
  unfold setup argBase
  simp only [List.append_assoc]
  refine save_ok hsp hwr (by omega) hm (fun r _ => hg r) fun v kv v0 fv sv => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun v₁ o₁ e₁ => wp_addi fun v₂ o₂ e₂ => ?_
  have sp₂ : v₂.sp = fb s := by rw [o₂.sp, o₁.sp, kv.sp, hsp]
  have rd₂ : v₂.rd = s.rd := by rw [o₂.rd, o₁.rd, kv.rd, hrd]
  have t6₂ : v₂.gpr .t6 = stackArgAddr s 0 := by rw [e₂, e₁, kv.sp, hsp]; exact Enc.t6_eq rfl
  have mem₂ : v₂.mem = v.mem := by rw [o₂.mem, o₁.mem]
  have fW : Frame (W s) s.mem v.mem := fv.mono (by simp)
  have arg : ∀ {j : Nat}, j < 7 → v₂.mem.readW (stackArgAddr s j) 64 = stackArg s j := fun hj => by
    rw [mem₂]; exact arg_mem hp fW hj
  refine wp_ld (a := stackArgAddr s 0) (by rw [t6₂, BitVec.add_zero]) (arg_al hp.spal 0)
    (by rw [rd₂]; exact arg_rd hp _ (by decide)) fun v₃ o₃ e₃ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by rw [o₃.get .t6, t6₂, stackArgAddr_eq s 1]) (arg_al hp.spal 1)
    (by rw [o₃.rd, rd₂]; exact arg_rd hp _ (by decide)) fun v₄ o₄ e₄ => ?_
  refine wp_ld (a := stackArgAddr s 2) (by rw [o₄.get .t6, o₃.get .t6, t6₂, stackArgAddr_eq s 2])
    (arg_al hp.spal 2) (by rw [o₄.rd, o₃.rd, rd₂]; exact arg_rd hp _ (by decide)) fun v₅ o₅ e₅ => ?_
  refine wp_sub fun v₆ o₆ e₆ => wp_subi (imm := 3) fun v₇ o₇ e₇ => wp_addi (imm := oPS) fun v₈ o₈ e₈ =>
    wp_li (imm := 0) (by decide) fun v₉ o₉ e₉ => wp_li (imm := 0) (by decide) fun v₁₀ o₁₀ e₁₀ => wp_nil ?_
  have O : Only [.t6, .t6, .t2, .t3, .t4, .t5, .s1, .t1, .t2, .t5] v v₁₀ :=
    o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))
  have K : Kept ([Reg.t0] ++ [.t6, .t6, .t2, .t3, .t4, .t5, .s1, .t1, .t2, .t5]) u v₁₀ := kv.trans O.keep
  have hF : InF s v₁₀ := {
    sp := by rw [K.sp, hsp]
    rd := by rw [K.rd, hrd]
    wr := by rw [K.wr, hwr]
    hi := fun r hr => by rw [K.gpr r (by revert r; decide), hg]
    sv := by rw [O.mem]; exact sv
    fr := by rw [O.mem]; exact fW }
  have hgA : ∀ r ∈ argRegs, v₁₀.gpr r = s.gpr r := fun r hr => by
    have hr' : r ∉ [Reg.t0] ++ [.t6, .t6, .t2, .t3, .t4, .t5, .s1, .t1, .t2, .t5] := by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [K.gpr r hr', hg]
  refine ⟨{ hF with
    g := hgA
    s1 := by
      rw [o₁₀.get .s1, o₉.get .s1, o₈.get .s1, e₇, e₆, o₅.get .a4, o₄.get .a4, o₃.get .a4, o₂.get .a4,
        o₁.get .a4, kv.get .a4, hg, o₅.get .t2, o₄.get .t2, e₃, arg (by decide)]
      exact psLen_eq hp
    t1 := by
      rw [o₁₀.get .t1, o₉.get .t1, e₈, o₇.get .t0, o₆.get .t0, o₅.get .t0, o₄.get .t0, o₃.get .t0, o₂.get .t0,
        o₁.get .t0, v0]; rfl
    t3 := by
      rw [o₁₀.get .t3, o₉.get .t3, o₈.get .t3, o₇.get .t3, o₆.get .t3, o₅.get .t3, e₄, o₃.mem]
      exact arg (by decide)
    t4 := by
      rw [o₁₀.get .t4, o₉.get .t4, o₈.get .t4, o₇.get .t4, o₆.get .t4, e₅, o₄.mem, o₃.mem]
      exact arg (by decide)
    frK := by rw [O.mem]; exact fv }, ?_, ?_⟩
  · rw [o₁₀.get .t2, e₉]; rfl
  · rw [e₁₀]; rfl

/-! ## The scan -/

/-- After `i` octets of the tape, from the state `t₀` before the scan. -/
structure At (s t₀ : State) (i : Nat) (u : State) : Prop where
  keep : Kept [.t6, .t2, .t0, .t5] t₀ u
  mem : u.mem = writeBytes t₀.mem (psA s) (kept s i)
  t2 : u.gpr .t2 = BitVec.ofNat 64 i
  t5 : u.gpr .t5 = BitVec.ofNat 64 (kept s i).length
  hi : i ≤ (stackArg s 2).toNat
  hc : (kept s i).length ≤ psLen s

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

/-- The octet of the tape, in the memory of the scan. -/
theorem rand_val {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 2).toNat) :
    u.mem (stackArg s 1 + BitVec.ofNat 64 i) = (randB s).getD i 0 := by
  have hP := psLen_le hp
  have hrl := hp.wr
  have hx : (rR s).Contains (stackArg s 1 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  rw [randB_getD hi, hI.mem]
  rw [Proof.RsaPkcs1Sig.writeBytes_out _ _ _ _ (psLen s) (fun j hj e => ?_) hI.hc]
  · exact hb.frK _ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact fun h => (k_dis hp.kr) _ h hx
  · have hj' : (kR s).Contains (psA s + BitVec.ofNat 64 j) 1 := by
      rw [psA, Enc.add_ofNat_ofNat]
      exact frame_contains s (by unfold oEM1 frameBytes; omega)
    exact (k_dis hp.kr) _ hj' (e ▸ hx)

/-- After the load of octet `i`. -/
structure Loaded (s t₀ : State) (i : Nat) (v : State) : Prop where
  keep : Kept [.t6, .t2, .t0, .t5] t₀ v
  mem : v.mem = writeBytes t₀.mem (psA s) (kept s i)
  t2 : v.gpr .t2 = BitVec.ofNat 64 (i + 1)
  t5 : v.gpr .t5 = BitVec.ofNat 64 (kept s i).length
  t6 : v.gpr .t6 = ((randB s).getD i 0).setWidth 64

/-- After octet `i` is kept or rejected. -/
structure Placed (s t₀ : State) (i : Nat) (x : State) : Prop where
  keep : Kept [.t6, .t2, .t0, .t5] t₀ x
  mem : x.mem = writeBytes t₀.mem (psA s) (kept s (i + 1))
  t2 : x.gpr .t2 = BitVec.ofNat 64 (i + 1)
  t5 : x.gpr .t5 = BitVec.ofNat 64 (kept s (i + 1)).length
  hc : (kept s (i + 1)).length ≤ psLen s

/-- The block loading octet `i`. -/
def loadB : List Instr := [.add .t6 .t3 .t2, .load .b .t6 .t6 0, .addi .t2 .t2 1]
/-- Keeping it, if it is not zero. -/
def keepB : Prog isa := .ite (.nonzero .t6) (.block [.add .t0 .t1 .t5, .store .b .t6 .t0 0, .addi .t5 .t5 1]) (.block [])
/-- Whether to go on. -/
def moreB : Prog isa := .ite (.eq .t5 .s1) (.block [.li .t0 0]) (.block [.sub .t0 .t4 .t2])

theorem step_eq : step = .seq (.block loadB) (.seq keepB moreB) := rfl

theorem load_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 2).toNat) : WP isa (.block loadB) u (Loaded s t₀ i) := by
  have hw := hp.wr
  have hrd : u.rd = s.rd := by rw [hI.keep.rd, hb.rd]
  have g3 : u.gpr .t3 = stackArg s 1 := by rw [hI.keep.get .t3, hb.t3]
  unfold loadB
  refine wp_add fun v₁ o₁ e₁ => ?_
  rw [g3, hI.t2] at e₁
  refine wp_lbu (a := stackArg s 1 + BitVec.ofNat 64 i) (by rw [e₁, BitVec.add_zero])
    (by rw [o₁.rd, hrd, hp.hrd]
        exact ⟨rR s, by simp, Offset.contains_base _ (by omega) (by omega)⟩) fun v₂ o₂ e₂ => ?_
  rw [o₁.mem, rand_val hp hb hI hi] at e₂
  refine wp_addi (imm := 1) fun v₃ o₃ e₃ => wp_nil ?_
  have O₃ : Only [.t6, .t6, .t2] u v₃ := o₁.trans (o₂.trans o₃)
  exact ⟨(hI.keep.trans O₃.keep).mono, by rw [O₃.mem, hI.mem],
    by rw [e₃, o₂.get .t2, o₁.get .t2, hI.t2, BitVec.ofNat_add_ofNat], by rw [O₃.get .t5, hI.t5],
    by rw [o₃.get .t6, e₂]⟩

theorem keep_ok {s t₀ v : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hL : Loaded s t₀ i v)
    (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) : WP isa keepB v (Placed s t₀ i) := by
  have hP := psLen_le hp
  have hwr : v.wr = kR s :: s.wr := by rw [hL.keep.wr, hb.wr]
  have g1 : v.gpr .t1 = psA s := by rw [hL.keep.get .t1, hb.t1]
  have hev : isa.eval (.nonzero .t6) v = some (!decide ((randB s).getD i 0 = 0)) := by
    rw [eval_nonzero, hL.t6, nz_setWidth]
  unfold keepB
  by_cases hz : (randB s).getD i 0 = 0
  · have hk : kept s (i + 1) = kept s i := by rw [kept_succ hi, ite_eq_left hz]
    refine WP.ite false (by rw [hev, decide_eq_true hz]; rfl) (fun h => absurd h (by decide))
      fun _ => wp_nil ⟨hL.keep, by rw [hL.mem, hk], hL.t2, by rw [hL.t5, hk], by rw [hk]; omega⟩
  · have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    refine WP.ite true (by rw [hev, decide_eq_false hz]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine wp_add fun v₄ o₄ e₄ => ?_
    rw [g1, hL.t5] at e₄
    have hA : InRegions v₄.wr (psA s + BitVec.ofNat 64 (kept s i).length) 1 := by
      rw [o₄.wr, hwr, psA, Enc.add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM1 frameBytes; omega)
    refine wp_sb (a := psA s + BitVec.ofNat 64 (kept s i).length) (by rw [e₄, BitVec.add_zero]) hA
      fun v₅ m₅ => wp_addi (imm := 1) fun v₆ o₆ e₆ => wp_nil ?_
    refine ⟨(hL.keep.trans (o₄.keep.trans (m₅.keep.trans o₆.keep))).mono, ?_, ?_, ?_, by rw [hk]; simp; omega⟩
    · rw [o₆.mem, m₅.mem, o₄.get .t6, hL.t6, byte_setWidth64, o₄.mem, hL.mem, hk,
        writeBytes_snoc _ _ _ _ (by omega)]
    · rw [o₆.get .t2, m₅.gpr, o₄.get .t2, hL.t2]
    · rw [e₆, m₅.gpr, o₄.get .t5, hL.t5, hk, BitVec.ofNat_add_ofNat, List.length_append,
        List.length_singleton]

theorem more_ok {s t₀ x : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hX : Placed s t₀ i x)
    (hi : i < (stackArg s 2).toNat) :
    WP isa moreB x fun u' => At s t₀ (i + 1) u' ∧
      (u'.gpr .t0 != 0) = !decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat) := by
  have hP := psLen_le hp
  have hrl := hp.rl
  have s1x : x.gpr .s1 = BitVec.ofNat 64 (psLen s) := by rw [hX.keep.get .s1, hb.s1]
  have t4x : x.gpr .t4 = stackArg s 2 := by rw [hX.keep.get .t4, hb.t4]
  have hcx := hX.hc
  have hev : isa.eval (.eq .t5 .s1) x = some (decide ((kept s (i + 1)).length = psLen s)) := by
    show some (x.gpr .t5 == x.gpr .s1) = _
    rw [hX.t5, s1x, beq_ofNat (by omega) (by omega)]
  unfold moreB
  by_cases hf : (kept s (i + 1)).length = psLen s
  · refine WP.ite true (by rw [hev, decide_eq_true hf]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine wp_li (imm := 0) (by decide) fun y o e => wp_nil ⟨⟨(hX.keep.trans o.keep).mono, by rw [o.mem, hX.mem],
      by rw [o.get .t2, hX.t2], by rw [o.get .t5, hX.t5], by omega, hcx⟩, ?_⟩
    rw [e]; simp [hf]
  · refine WP.ite false (by rw [hev, decide_eq_false hf]) (fun h => absurd h (by decide)) fun _ => ?_
    refine wp_sub fun y o e => wp_nil ⟨⟨(hX.keep.trans o.keep).mono, by rw [o.mem, hX.mem],
      by rw [o.get .t2, hX.t2], by rw [o.get .t5, hX.t5], by omega, hcx⟩, ?_⟩
    rw [e, t4x, hX.t2, ← ofNat_toNat (stackArg s 2), sub_ne_zero (by omega) (by omega)]
    simp only [hf, false_or]
    by_cases h' : i + 1 = (stackArg s 2).toNat <;> simp [h', eq_comm]

/-- One octet of the scan, with fewer than `psLen` octets kept and octets
left: after it, `At` for `i + 1`, and `t0` zero if `PS` is full or the tape
has ended. -/
theorem step_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) :
    WP isa step u fun u' => At s t₀ (i + 1) u' ∧
      (u'.gpr .t0 != 0) = !decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat) := by
  rw [step_eq]
  exact WP.seq (WP.mono (load_ok hp hb hI hi) fun v hv =>
    WP.seq (WP.mono (keep_ok hp hb hv hi hc) fun x hx => more_ok hp hb hx hi))

/-- The loop's invariant, with the octets left as its measure. -/
def LoopInv (s t₀ : State) (n : Nat) (u : State) : Prop :=
  ∃ i, n = (stackArg s 2).toNat - i ∧ At s t₀ i u ∧ i < (stackArg s 2).toNat ∧ (kept s i).length < psLen s

theorem scan_ok {s t₀ : State} (hp : RPre s) (hb : Before s t₀) (h2 : t₀.gpr .t2 = 0) (h5 : t₀.gpr .t5 = 0) :
    WP isa scan t₀ (Done s t₀) := by
  have hP := psLen_le hp
  have hm := hp.ml
  have h0 : At s t₀ 0 t₀ := ⟨Kept.refl _ _, by rw [kept_zero, writeBytes_nil], h2,
    by rw [h5, kept_zero]; rfl, Nat.zero_le _, by rw [kept_zero]; simp⟩
  have hps : 0 < psLen s := by unfold psLen; omega
  have hev : isa.eval (.nonzero .t4) t₀ = some (stackArg s 2 != 0) := by rw [eval_nonzero, hb.t4]
  unfold scan
  by_cases hl : stackArg s 2 = 0
  · refine WP.ite false (by rw [hev, hl]; rfl) (fun h => absurd h (by decide)) fun _ => wp_nil ?_
    have hl' : (stackArg s 2).toNat = 0 := by rw [hl]; rfl
    exact ⟨0, h0, .inr ⟨hl'.symm, by rw [kept_zero]; simpa using hps⟩⟩
  have hl' : 0 < (stackArg s 2).toNat := by
    rcases Nat.eq_zero_or_pos (stackArg s 2).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
    · exact h
  refine WP.ite true (by rw [hev, bne_iff_ne.mpr hl]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hinit : LoopInv s t₀ ((stackArg s 2).toNat - 0) t₀ := ⟨0, rfl, h0, hl', by rw [kept_zero]; simpa using hps⟩
  refine WP.loop (LoopInv s t₀) ?_ _ _ hinit
  rintro n u ⟨i, rfl, hI, hi, hc⟩
  refine WP.mono (step_ok hp hb hI hi hc) fun u' ⟨hI', hz'⟩ => ?_
  by_cases hstop : (kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat
  · refine .inl ⟨by rw [eval_nonzero, hz', decide_eq_true hstop]; rfl, ⟨i + 1, hI', ?_⟩⟩
    by_cases hf : (kept s (i + 1)).length = psLen s
    · exact .inl ⟨hf, prefix_of_fill hi hc hf⟩
    · exact .inr ⟨hstop.resolve_left hf, by have := hI'.hc; omega⟩
  · refine .inr ⟨by rw [eval_nonzero, hz', decide_eq_false hstop]; rfl, _, by omega, i + 1, rfl, hI',
      by omega, by have := hI'.hc; omega⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Rnd
