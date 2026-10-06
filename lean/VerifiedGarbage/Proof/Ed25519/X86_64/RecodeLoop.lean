import VerifiedGarbage.Proof.Ed25519.X86_64.RecodeStep

/-!
# The recoding's loop on x86-64

`recode` runs `Recode.step` from bit 0 while the bit is below the bound `8 nb` (what `bound`
compares `rsi` with), then stores the last carry: the array `dst` then holds
`Recode.digits w X (8 nb)` (`recode_ok`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)

theorem Copied.of_keep {m m' : Mem} {base : Addr} {src nb X : Nat} (h : Copied m base src nb X)
    (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (k : ∀ x, (ofs base x < 2048 ∨ 3104 ≤ ofs base x) → m' x = m x) : Copied m' base src nb X := by
  intro b hb
  rw [← h b hb]
  congr 1
  exact Mem.readW_congr fun i hi => k _ (Or.inr (by
    rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))

/-- The recoding's loop: the state `st`, reached from the start, in the registers and the array. -/
structure RecInv (s₀ : State) (base : Addr) (nb X w dst : Nat) (st : St) (t : State) : Prop where
  reach : Reach w X (8 * nb) st
  good : Good w X st
  lt : st.i < 8 * nb + w
  rsi : t.gpr .rsi = BitVec.ofNat 64 st.i
  r8 : t.gpr .r8 = BitVec.ofNat 64 st.c
  dig : ∀ j < 528, dig t.mem base dst j = st.u j
  keep : RecKeep base dst s₀ t

/-- What `bound` does from any state the recoding reaches: CF set if the bit is below `8 nb`. -/
def BoundSpec (s₀ : State) (base : Addr) (dst nb : Nat) (bound : List Instr) : Prop :=
  ∀ t, RecKeep base dst s₀ t → ∀ i, t.gpr .rsi = BitVec.ofNat 64 i → i < 1024 →
    WP isa (.block bound) t fun u => u.cf = some (decide (i < 8 * nb)) ∧ Keeps [.rax] t u

/-- One step of the recoding loop, from bit `st.i < 8 nb`: CF set if it goes on. -/
theorem recodeBody_ok {s₀ s : State} {base : Addr} (hs : Scratch s₀ base) {src nb X w dst : Nat}
    (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hX : Copied s₀.mem base src nb X) (hnb : 8 * nb ≤ 512) {bound : List Instr}
    (hb : BoundSpec s₀ base dst nb bound) {st : St} (hi : st.i < 8 * nb)
    (ht : RecInv s₀ base nb X w dst st s) :
    WP isa (.seq (recodeStep src w dst) (.block bound)) s fun v =>
      RecInv s₀ base nb X w dst (step w X st) v ∧ v.cf = some (decide ((step w X st).i < 8 * nb)) := by
  have hst : Scratch s base := ht.keep.scratch hs
  have hX' : Copied s.mem base src nb X :=
    hX.of_keep hsrc hfit fun x hx => ht.keep.mem x (by omega)
  refine WP.seq (WP.mono (recodeStep_ok hst hw hdst hfit hX' hi hnb ht.good.c ht.rsi ht.r8 ht.dig)
    fun u ⟨ursi, ur8, udig, ku⟩ => ?_)
  have kt := ht.keep.trans ku
  have hsi := step_i (K := X) (by omega : 1 ≤ w) st
  refine WP.mono (hb u kt _ ursi (by omega)) fun v ⟨vcf, kv⟩ => ?_
  exact ⟨⟨reach_step (by omega) ht.reach hi, step_good hw.1 ht.good, by omega,
    by rw [kv.1 _ (by decide)]; exact ursi, by rw [kv.1 _ (by decide)]; exact ur8,
    fun j hj => by rw [kv.2.1]; exact udig j hj, kt.trans (RecKeep.of_keeps kv (by decide))⟩, vcf⟩

theorem recodeLoop_ok {s₀ s : State} {base : Addr} (hs : Scratch s₀ base) {src nb X w dst : Nat}
    (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hX : Copied s₀.mem base src nb X) (hnb : 8 * nb ≤ 512) {bound : List Instr}
    (hb : BoundSpec s₀ base dst nb bound) {st : St} (hi : st.i < 8 * nb)
    (h : RecInv s₀ base nb X w dst st s) :
    WP isa (.loop (.seq (recodeStep src w dst) (.block bound)) .b) s fun t =>
      RecInv s₀ base nb X w dst (run w X (8 * nb) (8 * nb) init) t := by
  apply WP.loop (fun m t => ∃ st, RecInv s₀ base nb X w dst st t ∧ st.i < 8 * nb ∧ m = 8 * nb - st.i)
    (n := 8 * nb - st.i)
  · rintro m t ⟨st, ht, hi, rfl⟩
    have hsi := step_i (K := X) (by omega : 1 ≤ w) st
    refine WP.mono (recodeBody_ok hs hw hdst hsrc hfit hX hnb hb hi ht) fun v ⟨hv, vcf⟩ => ?_
    by_cases hlt : (step w X st).i < 8 * nb
    · exact Or.inr ⟨by simp only [eval, vcf, decide_eq_true hlt], _, by omega, _, hv, hlt, rfl⟩
    · refine Or.inl ⟨by simp only [eval, vcf, decide_eq_false hlt], ?_⟩
      rw [← reach_end (reach_step (by omega) ht.reach hi) (by omega)]
      exact hv
  · exact ⟨st, h, hi, rfl⟩

theorem recodeStart_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.imm 0), .mov32 .r8 (.imm 0)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .r8 = BitVec.ofNat 64 0 ∧ Keeps [.rsi, .r8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-- The digit 1 at the bit `i`, for the last carry. -/
theorem recodeLast_ok {s : State} {base : Addr} (hs : Scratch s base) {i dst : Nat}
    (hi : i < 528) (hdst : dst < 2) (hrsi : s.gpr .rsi = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax), .mov32 .rbx (.imm 1),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx]) s fun t =>
      t.mem = s.mem.writeW (off base (2048 + 2 * i + dst)) (BitVec.ofNat 8 1) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hea : base + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 ((2048 + dst : Nat) : Int) = off base (2048 + 2 * i + dst) := by
    rw [BitVec.ofInt_natCast, BitVec.mul_one, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun n => off base n) (by omega)
  have hrg : InRegions s.wr (off base (2048 + 2 * i + dst)) 1 :=
    ⟨_, hs.wr, Offset.contains_base _ (show 2048 + 2 * i + dst + 1 ≤ 8192 by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.store8,
    State.ea, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg,
    RegUpd.rd_arithFlags, hrsi, hs.rdi, hea, hrg, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r ha hb => ?_, trivial, trivial⟩
  simp only [ha, hb, ite_false]

/-- ZF set if the last carry `c` is zero. -/
theorem testR8_ok (s : State) {c : Nat} (hc : c ≤ 1) (h8 : s.gpr .r8 = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .test .r8 (.reg .r8)]) s fun t => t.zf = some (decide (c = 0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.zf_arithFlags,
    h8, BitVec.and_self, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain h0 | h1 : c = 0 ∨ c = 1 := by omega
  · rw [h0]; rfl
  · rw [h1]; rfl

/-- The recoding of `X < 2 ^ (8 nb)` into the zeroed array `dst`: its digits' bytes. -/
theorem recode_ok {s : State} {base : Addr} (hs : Scratch s base) {src nb X w dst : Nat}
    (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hX : Copied s.mem base src nb X) (hnb : 0 < nb ∧ 8 * nb ≤ 512) {bound : List Instr}
    (hb : BoundSpec s base dst nb bound) (hz : ∀ j < 528, dig s.mem base dst j = 0) :
    WP isa (recode src w dst bound) s fun t =>
      (∀ j < 528, dig t.mem base dst j = digits w X (8 * nb) j) ∧ RecKeep base dst s t := by
  rw [recode]
  refine WP.seq (WP.mono (recodeStart_ok s) fun a ⟨arsi, ar8, ka⟩ => ?_)
  have ha : RecInv s base nb X w dst init a :=
    ⟨reach_init w X _, init_good w X, by simp only [init]; omega, arsi, ar8,
      fun j hj => by rw [ka.2.1]; exact hz j hj, RecKeep.of_keeps ka (by decide)⟩
  refine WP.seq (WP.mono (recodeLoop_ok hs hw hdst hsrc hfit hX hnb.2 hb (by simp only [init]; omega) ha)
    fun b hb' => ?_)
  generalize hF : run w X (8 * nb) (8 * nb) init = F at hb'
  have hFi : 8 * nb ≤ F.i := hF ▸ run_end (by omega) _ (by simp only [init]; omega)
  have hFl : F.i < 8 * nb + w := hb'.lt
  have hd : ∀ j, digits w X (8 * nb) j = fin F j := fun j => by rw [← hF]; rfl
  rw [recodeEnd]
  have hc := hb'.good.c
  refine WP.seq (WP.mono (testR8_ok b hc hb'.r8) fun c ⟨cz, kc⟩ => ?_)
  refine WP.ite (!decide (F.c = 0)) (by simp only [eval, cz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hc1 : F.c ≠ 0 := by simpa using h
    refine WP.mono (recodeLast_ok (hb'.keep.scratch hs |>.of_keeps kc (by decide)) (i := F.i) (by omega) hdst
      (by rw [kc.1 _ (by decide)]; exact hb'.rsi)) fun t ⟨tm, tg, trd, twr⟩ => ?_
    refine ⟨fun j hj => ?_, hb'.keep.trans (RecKeep.of_keeps kc (by decide)) |>.trans
      ⟨fun r hr => tg r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide)), trd, twr,
        fun x hx => by rw [tm, keep_write (by omega) hdst _ x hx]⟩⟩
    rw [tm, dig_write (by omega) hdst (by decide) hj, kc.2.1, hd, fin]
    by_cases hj' : j = F.i
    · rw [ite_eq_left hj', ite_eq_left ⟨hc1, hj'⟩]
    · rw [ite_eq_right hj', ite_eq_right (fun h => hj' h.2), hb'.dig j hj]
  · have hc0 : F.c = 0 := by simpa using h
    refine WP.block_nil ⟨fun j hj => ?_, hb'.keep.trans (RecKeep.of_keeps kc (by decide))⟩
    rw [kc.2.1, hd, fin, ite_eq_right (fun h => h.1 hc0), hb'.dig j hj]

end VG.Proof.Ed25519.X86_64
