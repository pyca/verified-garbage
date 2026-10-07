import VerifiedGarbage.Proof.Ed25519.X86_64.RecodeAll
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT

/-!
# The recoding: what its trace depends on

The recoding branches on the scalars' bits and the carry, and addresses the copies and the
digits' array by the bit's position, so its trace depends on the recoding's state alone (`St`),
the same in both runs of the same scalar: both runs are followed at the same state.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)
open VG.Impl.X25519.X86_64 (sc at_)

theorem agree_rdi_rsi {x y : State} (h : x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

theorem agree_none {x y : State} : VG.X86_64.Taint.Agree (Taint.ofRegs []) x y :=
  Taint.agree_ofRegs (by simp)

/-- A state at the bit `i`: the scratch's, `rsi = i`. -/
def AtBit (base : Addr) (i : Nat) (x : State) : Prop := Scratch x base ∧ x.gpr .rsi = BitVec.ofNat 64 i

/-- Code whose trace depends on `rdi` and `rsi`, from states at the same bit. -/
theorem atBit_ct {P : State → Prop} {base : Addr} {i : Nat} {c : Prog isa} (hP : ∀ x, P x → AtBit base i x)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => ⟨((hP x hh.1).1.rdi).trans (hP y hh.2).1.rdi.symm,
    ((hP x hh.1).2).trans (hP y hh.2).2.symm⟩) (fun _ _ h => h)

/-- The two recodings: `k`'s and `S`'s. -/
def RecParams (src w dst : Nat) : Prop := (src = 3104 ∧ w = 5 ∧ dst = 0) ∨ (src = 3176 ∧ w = 8 ∧ dst = 1)

theorem bitsTest_ct {src w dst : Nat} (hp : RecParams src w dst) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi)
    (.block (recodeBits src ++ recodeTest)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) (fun _ _ h => agree_rdi_rsi h)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeStore_ct {src w dst : Nat} (hp : RecParams src w dst) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi)
    (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx,
      .alu .add .rsi (.imm (BitVec.ofNat 32 w))]) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) (fun _ _ h => agree_rdi_rsi h)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeLast_ct {src w dst : Nat} (hp : RecParams src w dst) : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi)
    (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax), .mov32 .rbx (.imm 1),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx])
    (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) (fun _ _ h => agree_rdi_rsi h)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeW_ct {P : State → State → Prop} {src w dst : Nat} (hp : RecParams src w dst) :
    RelCT isa P (.block [.alu .and .rbx (.imm (BitVec.ofNat 32 (2 ^ w - 1))), .alu .add .rbx (.reg .r8),
      .alu .cmp .rbx (.imm (BitVec.ofNat 32 (2 ^ (w - 1))))]) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs []) (fun _ _ _ => agree_none)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

theorem recodeNeg_ct {P : State → State → Prop} {src w dst : Nat} (hp : RecParams src w dst) :
    RelCT isa P (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (2 ^ w + 1))), .alu .sub .rax (.reg .rbx),
      .mov .rbx (.reg .rax), .mov32 .r8 (.imm 1)]) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs []) (fun _ _ _ => agree_none)
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := hp <;> exact ⟨_, by taint_decide⟩

/-- Code that accesses no memory and does not branch. -/
theorem noMem_ct {P : State → State → Prop} (l : List Instr)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
      (VG.X86_64.taint.check (Taint.ofRegs []) (.block l) hc).isSome = true) :
    RelCT isa P (.block l) (fun _ _ => True) :=
  taintFld (Taint.ofRegs []) (fun _ _ _ => agree_none) h

section
variable (base : Addr) (src nb X w dst : Nat) (bound : List Instr)

/-- Where the recoding may start from: the scratch, the copy of `X`, the bound and the digits'
array zeroed. -/
structure RecStart (s : State) : Prop where
  scratch : Scratch s base
  copied : Copied s.mem base src nb X
  bound : BoundSpec s base dst nb bound

/-- A run of the recoding at the state `st`. -/
def RecRun (st : St) (x : State) : Prop :=
  ∃ s₀, RecStart base src nb X dst bound s₀ ∧ RecInv s₀ base nb X w dst st x

end

theorem RecRun.atBit {base : Addr} {src nb X w dst : Nat} {bound : List Instr} {st : St} {x : State}
    (h : RecRun base src nb X w dst bound st x) : AtBit base st.i x := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact ⟨h.keep.scratch h₀.scratch, h.rsi⟩

/-- One step: its branches are on the bit and on the window, functions of `X` and `st`. -/
theorem recodeStep_ct {base : Addr} {src nb X w dst : Nat} {bound : List Instr} {st : St}
    (hp : RecParams src w dst) (hw : 2 ≤ w ∧ w ≤ 8) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192) (hi : st.i < 8 * nb)
    (hnb : 8 * nb ≤ 512) :
    RelCT isa (fun x y => RecRun base src nb X w dst bound st x ∧ RecRun base src nb X w dst bound st y)
      (recodeStep src w dst) (fun _ _ => True) := by
  let W := X / 2 ^ st.i % 2 ^ w
  have hWl : W < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h8 : 2 ^ w ≤ 256 := (Nat.pow_le_pow_right (by decide) hw.2 : 2 ^ w ≤ 2 ^ 8)
  -- After the bits and the test.
  let F1 : State → Prop := fun u => u.zf = some (decide (X / 2 ^ st.i % 2 = st.c)) ∧ AtBit base st.i u ∧
    u.gpr .r8 = BitVec.ofNat 64 st.c ∧ (u.gpr .rbx).toNat % 2 ^ w = W ∧ st.c ≤ 1
  have w1 (x : State) (h : RecRun base src nb X w dst bound st x) :
      WP isa (.block (recodeBits src ++ recodeTest)) x F1 := by
    obtain ⟨s₀, h₀, ht⟩ := h
    have hs : Scratch x base := ht.keep.scratch h₀.scratch
    have hX : Copied x.mem base src nb X := h₀.copied.of_keep hsrc hfit fun y hy => ht.keep.mem y (by omega)
    have hc1 := ht.good.c
    rw [WP.block_append_iff]
    refine WP.mono (recodeBits_ok hs hfit hX hi ht.rsi (by omega)) fun a ⟨ab, ka⟩ => ?_
    have hbit : (a.gpr .rbx).toNat % 2 = X / 2 ^ st.i % 2 := by
      rw [ab]; exact bits_mod X st.i 1 (by decide)
    have hwin : (a.gpr .rbx).toNat % 2 ^ w = W := by
      rw [ab]; exact bits_mod X st.i w (by omega)
    refine WP.mono (recodeTest_ok a hbit hc1 (by rw [ka.1 _ (by decide)]; exact ht.r8)) fun b ⟨bz, kb⟩ => ?_
    have kab : Keeps [.rax, .rbx, .rcx, .rdx] x b := ka.trans (kb.mono (by decide))
    refine ⟨bz, ⟨hs.of_keeps kab (by decide), by rw [kab.1 _ (by decide)]; exact ht.rsi⟩,
      by rw [kab.1 _ (by decide)]; exact ht.r8, by rw [kb.1 _ (by decide)]; exact hwin, hc1⟩
  rw [recodeStep]
  refine seq_same (atBit_ct (fun x h => h.atBit) (bitsTest_ct hp)) w1 ?_
  have e1 (x : State) (h : F1 x) : isa.eval .e x = some (decide (X / 2 ^ st.i % 2 = st.c)) := by
    show eval .e x = _; simp only [eval, h.1]
  refine VG.RelCT.ite (fun x y h => (e1 x h.1).trans (e1 y h.2).symm) (noMem_ct _ ⟨_, by taint_decide⟩) ?_
  -- The window.
  rw [recodeWindow]
  let F1' : State → Prop := fun u => F1 u ∧ X / 2 ^ st.i % 2 ≠ st.c
  refine (show RelCT isa (fun x y => F1' x ∧ F1' y) _ _ from ?_).mono (fun x y h => by
    have hne : X / 2 ^ st.i % 2 ≠ st.c := by
      have := (e1 x h.1.1).symm.trans h.2
      simpa using this
    exact ⟨⟨h.1.1, hne⟩, ⟨h.1.2, hne⟩⟩) (fun _ _ h => h)
  let F2 : State → Prop := fun u => u.cf = some (decide (W + st.c < 2 ^ (w - 1))) ∧ AtBit base st.i u ∧
    u.gpr .rbx = BitVec.ofNat 64 (W + st.c) ∧ st.c ≤ 1
  have w2 (x : State) (h : F1' x) : WP isa (.block [.alu .and .rbx (.imm (BitVec.ofNat 32 (2 ^ w - 1))),
      .alu .add .rbx (.reg .r8), .alu .cmp .rbx (.imm (BitVec.ofNat 32 (2 ^ (w - 1))))]) x F2 := by
    obtain ⟨⟨_, ⟨hs, hr⟩, h8', hb, hc1⟩, _⟩ := h
    refine WP.mono (recodeW_ok x (by omega) hb hc1 h8') fun c ⟨cb, ccf, kc⟩ => ?_
    exact ⟨ccf, ⟨hs.of_keeps kc (by decide), by rw [kc.1 _ (by decide)]; exact hr⟩, cb, hc1⟩
  refine seq_same (recodeW_ct hp) w2 ?_
  have e2 (x : State) (h : F2 x) : isa.eval .b x = some (decide (W + st.c < 2 ^ (w - 1))) := by
    show eval .b x = _; simp only [eval, h.1]
  refine VG.RelCT.seq (R := fun x y => AtBit base st.i x ∧ AtBit base st.i y)
    (VG.RelCT.ite (fun x y h => (e2 x h.1).trans (e2 y h.2).symm) ?_ ?_)
    (atBit_ct (fun _ h => h) (recodeStore_ct hp))
  · have wp (x : State) (h : F2 x) : WP isa (.block [.mov32 .r8 (.imm 0)]) x (AtBit base st.i) :=
      WP.mono (recodePos_ok x) fun u ⟨_, _, ku⟩ =>
        ⟨h.2.1.1.of_keeps ku (by decide), by rw [ku.1 _ (by decide)]; exact h.2.1.2⟩
    exact ((VG.RelCT.wp (noMem_ct _ ⟨_, by taint_decide⟩) fun x y h => ⟨wp x h.1.1, wp y h.1.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2))
  · have wn (x : State) (h : F2 x) : WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (2 ^ w + 1))),
        .alu .sub .rax (.reg .rbx), .mov .rbx (.reg .rax), .mov32 .r8 (.imm 1)]) x (AtBit base st.i) :=
      WP.mono (recodeNeg_ok x (W := W + st.c) (by omega) (by have := h.2.2.2; omega) h.2.2.1)
        fun u ⟨_, _, ku⟩ => ⟨h.2.1.1.of_keeps ku (by decide), by rw [ku.1 _ (by decide)]; exact h.2.1.2⟩
    exact ((VG.RelCT.wp (recodeNeg_ct hp) fun x y h => ⟨wn x h.1.1, wn y h.1.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2))

/-- The recoding: its loop at the same state in both runs, then the last carry. -/
theorem recode_ct {P : State → Prop} {base : Addr} {src nb X w dst : Nat} {bound : List Instr}
    (hp : RecParams src w dst) (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hnb : 0 < nb ∧ 8 * nb ≤ 512)
    (hP : ∀ x, P x → RecStart base src nb X dst bound x ∧ ∀ j < 528, dig x.mem base dst j = 0)
    (hbct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block bound) (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) (recode src w dst bound) (fun _ _ => True) := by
  have w0 (x : State) (h : P x) : WP isa (.block [.mov32 .rsi (.imm 0), .mov32 .r8 (.imm 0)]) x
      (RecRun base src nb X w dst bound init) := by
    obtain ⟨h₀, hz⟩ := hP x h
    refine WP.mono (recodeStart_ok x) fun a ⟨arsi, ar8, ka⟩ => ⟨x, h₀, ?_⟩
    exact ⟨reach_init w X _, init_good w X, by simp only [init]; omega, arsi, ar8,
      fun j hj => by rw [ka.2.1]; exact hz j hj, RecKeep.of_keeps ka (by decide)⟩
  rw [recode]
  refine seq_same (noMem_ct _ ⟨_, by taint_decide⟩) w0 ?_
  -- The loop.
  let F := run w X (8 * nb) (8 * nb) init
  refine VG.RelCT.seq (R := fun x y => RecRun base src nb X w dst bound F x ∧
    RecRun base src nb X w dst bound F y) ?_ ?_
  · refine (VG.RelCT.loop (M := isa) (fun m x y => ∃ st, st.i < 8 * nb ∧ m = 8 * nb - st.i ∧
      RecRun base src nb X w dst bound st x ∧ RecRun base src nb X w dst bound st y) ?_ (8 * nb - init.i)).mono
      (fun x y h => ⟨init, by simp only [init]; omega, rfl, h⟩) (fun _ _ h => h)
    intro m
    refine VG.RelCT.exists_ fun st => ?_
    refine (VG.RelCT.exists_ (P := fun (hh : st.i < 8 * nb ∧ m = 8 * nb - st.i) x y =>
      RecRun base src nb X w dst bound st x ∧ RecRun base src nb X w dst bound st y) fun hh => ?_).mono
      (fun x y h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
    obtain ⟨hi, hm⟩ := hh
    have hsi := step_i (K := X) (by omega : 1 ≤ w) st
    have wb (x : State) (h : RecRun base src nb X w dst bound st x) :
        WP isa (.seq (recodeStep src w dst) (.block bound)) x fun v =>
          RecRun base src nb X w dst bound (step w X st) v ∧
          v.cf = some (decide ((step w X st).i < 8 * nb)) := by
      obtain ⟨s₀, h₀, ht⟩ := h
      exact WP.mono (recodeBody_ok h₀.scratch hw hdst hsrc hfit h₀.copied hnb.2 h₀.bound hi ht)
        fun v ⟨hv, vcf⟩ => ⟨⟨s₀, h₀, hv⟩, vcf⟩
    have bodyCT : RelCT isa (fun x y => RecRun base src nb X w dst bound st x ∧
        RecRun base src nb X w dst bound st y) (.seq (recodeStep src w dst) (.block bound)) (fun _ _ => True) :=
      seq_same (recodeStep_ct hp hw hsrc hfit hi hnb.2) (F := fun u => u.gpr .rdi = base)
        (fun x h => by
          obtain ⟨s₀, h₀, ht⟩ := h
          exact WP.mono (recodeStep_ok (ht.keep.scratch h₀.scratch) hw hdst hfit
            (h₀.copied.of_keep hsrc hfit fun y hy => ht.keep.mem y (by omega)) hi hnb.2 ht.good.c ht.rsi ht.r8
            ht.dig) fun u ⟨_, _, _, ku⟩ => (ku.scratch (ht.keep.scratch h₀.scratch)).rdi)
        (rdi_ct (fun _ h => h) hbct)
    refine (VG.RelCT.wp bodyCT fun x y h => ⟨wb x h.1, wb y h.2⟩).mono (fun x y h => h) ?_
    intro x y ⟨_, ⟨xr, xc⟩, ⟨yr, yc⟩⟩
    have ex : isa.eval .b x = some (decide ((step w X st).i < 8 * nb)) := by
      show eval .b x = _; simp only [eval, xc]
    have ey : isa.eval .b y = some (decide ((step w X st).i < 8 * nb)) := by
      show eval .b y = _; simp only [eval, yc]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have hlt : ¬ (step w X st).i < 8 * nb := by rw [ex] at he; simpa using he
      have e := reach_end (by obtain ⟨_, _, ht⟩ := xr; exact ht.reach) (by omega : 8 * nb ≤ (step w X st).i)
      show RecRun base src nb X w dst bound (run w X (8 * nb) (8 * nb) init) x ∧ RecRun base src nb X w dst bound (run w X (8 * nb) (8 * nb) init) y
      rw [← e]
      exact ⟨xr, yr⟩
    · have hlt : (step w X st).i < 8 * nb := by rw [ex] at he; simpa using he
      exact ⟨8 * nb - (step w X st).i, by omega, step w X st, hlt, rfl, xr, yr⟩
  -- The last carry.
  rw [recodeEnd]
  let G : State → Prop := fun u => u.zf = some (decide (F.c = 0)) ∧ AtBit base F.i u
  have wt (x : State) (h : RecRun base src nb X w dst bound F x) :
      WP isa (.block [.alu .test .r8 (.reg .r8)]) x G := by
    obtain ⟨s₀, h₀, hb'⟩ := h
    exact WP.mono (testR8_ok x hb'.good.c hb'.r8) fun t ⟨tz, kt⟩ =>
      ⟨tz, (hb'.keep.scratch h₀.scratch).of_keeps kt (by decide), by rw [kt.1 _ (by decide)]; exact hb'.rsi⟩
  refine seq_same (noMem_ct _ ⟨_, by taint_decide⟩) wt ?_
  have eG (x : State) (h : G x) : isa.eval .ne x = some (!decide (F.c = 0)) := by
    show eval .ne x = _; simp only [eval, h.1, Option.map_some]
  refine VG.RelCT.ite (fun x y h => (eG x h.1).trans (eG y h.2).symm) ?_ (VG.RelCT.block_nil fun _ _ _ => trivial)
  exact (atBit_ct (fun _ h => h) (recodeLast_ct hp)).mono (fun x y h => ⟨h.1.1.2, h.1.2.2⟩) (fun _ _ h => h)

/-! ## The copies -/

/-- A state with the scratch and `rsi = P`. -/
def AtPtr (base P : Addr) (x : State) : Prop := Scratch x base ∧ x.gpr .rsi = P

/-- What the copies need: the scratch, the scalars' pointers and their regions. -/
structure CopyPre (base kp sp : Addr) (x : State) : Prop where
  scratch : Scratch x base
  kPtr : x.mem.readW (off base 7952) 64 = kp
  sPtr : x.mem.readW (off base 7944) 64 = sp
  kr : ∀ j < 8, InRegions (x.rd ++ x.wr) (off kp (8 * j)) 8
  sr : ∀ j < 4, InRegions (x.rd ++ x.wr) (off sp (32 + 8 * j)) 8

theorem atPtr_ct {P : State → Prop} {base Q : Addr} {c : Prog isa} (hP : ∀ x, P x → AtPtr base Q x)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rsi = y.gpr .rsi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => ⟨((hP x hh.1).1.rdi).trans (hP y hh.2).1.rdi.symm,
    ((hP x hh.1).2).trans (hP y hh.2).2.symm⟩) (fun _ _ h => h)

/-- The copies load through the scalars' pointers, the same in both runs. -/
theorem recodeCopy_ct {P : State → Prop} {base kp sp : Addr}
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j)) (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j)))
    (hP : ∀ x, P x → CopyPre base kp sp x) :
    RelCT isa (fun x y => P x ∧ P y) (.block (zeroDigits ++ copyScalars)) (fun _ _ => True) := by
  rw [show zeroDigits ++ copyScalars = (zeroDigits ++ [.mov .rsi (.mem (sc 7952))]) ++
      (((List.range 8).flatMap fun j =>
        [.mov .rax (.mem (at_ .rsi (0 + 8 * j))), .store (sc (3104 + 8 * j)) .rax]) ++
      ([.mov .rsi (.mem (sc 7944))] ++ (((List.range 4).flatMap fun j =>
        [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax]) ++
      [.mov32 .rax (.imm 0), .store (sc 3168) .rax, .store (sc 3208) .rax]))) by
    simp only [copyScalars, Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append]]
  -- Up to `k`'s pointer.
  let Q1 : State → Prop := fun u => AtPtr base kp u ∧ u.mem.readW (off base 7944) 64 = sp ∧
    (∀ j < 8, InRegions (u.rd ++ u.wr) (off kp (8 * j)) 8) ∧
    (∀ j < 4, InRegions (u.rd ++ u.wr) (off sp (32 + 8 * j)) 8)
  have w1 (x : State) (h : P x) : WP isa (.block (zeroDigits ++ [.mov .rsi (.mem (sc 7952))])) x Q1 := by
    have c := hP x h
    have hs := c.scratch
    rw [WP.block_append_iff]
    refine WP.mono (zeroDigits_ok hs) fun a ⟨⟨_, ao⟩, ag, _, ar, aw⟩ => ?_
    have ha : Scratch a base := ⟨by rw [ag _ (by decide)]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
    have hb := hs.nowrap
    have aread (d : Nat) (hd : 3104 ≤ d) (hd' : d + 8 ≤ 8192) :
        a.mem.readW (off base d) 64 = x.mem.readW (off base d) 64 :=
      Mem.readW_congr fun i hi => ao _ (Or.inr (by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
    refine WP.mono (loadSc_ok ha .rsi 7952 (by decide)) fun u ⟨up, ku⟩ => ?_
    refine ⟨⟨ha.of_keeps ku (by decide), by rw [up, aread 7952 (by decide) (by decide)]; exact c.kPtr⟩,
      by rw [ku.2.1, aread 7944 (by decide) (by decide)]; exact c.sPtr,
      fun j hj => by rw [ku.2.2.1, ku.2.2.2, ar, aw]; exact c.kr j hj,
      fun j hj => by rw [ku.2.2.1, ku.2.2.2, ar, aw]; exact c.sr j hj⟩
  apply RelCT.block_append
  refine seq_same (rdi_ct (fun x h => (hP x h).scratch.rdi)
    (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩)) w1 ?_
  -- `k`'s copy.
  let Q2 : State → Prop := fun u => Scratch u base ∧ u.mem.readW (off base 7944) 64 = sp ∧
    (∀ j < 4, InRegions (u.rd ++ u.wr) (off sp (32 + 8 * j)) 8)
  have w2 (x : State) (h : Q1 x) : WP isa (.block ((List.range 8).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (0 + 8 * j))), .store (sc (3104 + 8 * j)) .rax])) x Q2 := by
    obtain ⟨⟨hs, hr⟩, hsp, hkr, hsr⟩ := h
    have hb := hs.nowrap
    refine WP.mono (copyPrefix_ok hs hr 0 3104 8 (by decide) (fun j hj => by simpa using hkr j hj)
      (fun j hj => by simpa using hkf j hj)) fun b ⟨⟨_, bo⟩, bg, br, bw⟩ => ?_
    refine ⟨⟨by rw [bg _ (by decide)]; exact hs.rdi, bw ▸ hs.wr, hb⟩, ?_,
      fun j hj => by rw [br, bw]; exact hsr j hj⟩
    rw [← hsp]
    exact Mem.readW_congr fun i hi => bo _ (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
  apply RelCT.block_append
  refine seq_same (atPtr_ct (fun x h => h.1) (taintFld (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => agree_rdi_rsi h) ⟨_, by taint_decide⟩)) w2 ?_
  -- `S`'s pointer.
  let Q3 : State → Prop := fun u => AtPtr base sp u ∧ (∀ j < 4, InRegions (u.rd ++ u.wr) (off sp (32 + 8 * j)) 8)
  have w3 (x : State) (h : Q2 x) : WP isa (.block [.mov .rsi (.mem (sc 7944))]) x Q3 := by
    obtain ⟨hs, hsp, hsr⟩ := h
    refine WP.mono (loadSc_ok hs .rsi 7944 (by decide)) fun u ⟨up, ku⟩ =>
      ⟨⟨hs.of_keeps ku (by decide), by rw [up]; exact hsp⟩, fun j hj => by rw [ku.2.2.1, ku.2.2.2]; exact hsr j hj⟩
  apply RelCT.block_append
  refine seq_same (rdi_ct (fun x h => h.1.rdi)
    (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩)) w3 ?_
  -- `S`'s copy, then the zeros after the copies.
  have w4 (x : State) (h : Q3 x) : WP isa (.block ((List.range 4).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax])) x (Scratch · base) := by
    obtain ⟨⟨hs, hr⟩, hsr⟩ := h
    exact WP.mono (copyPrefix_ok hs hr 32 3176 4 (by decide) hsr hsf) fun b ⟨_, bg, _, bw⟩ =>
      ⟨by rw [bg _ (by decide)]; exact hs.rdi, bw ▸ hs.wr, hs.nowrap⟩
  apply RelCT.block_append
  exact seq_same (atPtr_ct (fun x h => h.1) (taintFld (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => agree_rdi_rsi h) ⟨_, by taint_decide⟩)) w4
    (rdi_ct (fun x h => h.rdi) (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩))

/-! ## Both recodings -/

/-- `k`'s and `S`'s recodings, of the same scalars in both runs, after the same number `c` of
`k`'s bytes: their trace depends on those alone. -/
theorem recodeAll_ct {P : State → Prop} {base kp sp : Addr} {c K S : Nat} (hc32 : 32 ≤ c) (hc64 : c ≤ 64)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j)) (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j)))
    (hP : ∀ x, P x → CopyPre base kp sp x ∧ x.mem.readW (off base 56) 64 = BitVec.ofNat 64 c ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt x.mem kp 64) = K ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt x.mem (off sp 32) 32) = S) :
    RelCT isa (fun x y => P x ∧ P y) recodeAll (fun _ _ => True) := by
  have w1 (x : State) (h : P x) : WP isa (.block (zeroDigits ++ copyScalars)) x (Copies base c K S) := by
    obtain ⟨cp, hc, hK, hS⟩ := hP x h
    refine WP.mono (recodeCopy_ok cp.scratch hc hc64 cp.kPtr cp.sPtr cp.kr cp.sr hkf hsf) fun b hb => ?_
    rw [hK, hS] at hb
    exact hb.1
  rw [recodeAll]
  refine seq_same (recodeCopy_ct hkf hsf fun x h => (hP x h).1) w1 ?_
  -- `k`'s digits.
  let F2 : State → Prop := fun u => Scratch u base ∧ u.mem.readW (off base 56) 64 = BitVec.ofNat 64 c ∧
    Copied u.mem base 3176 32 S ∧ ∀ j < 528, dig u.mem base 1 j = 0
  have w2 (x : State) (h : Copies base c K S x) : WP isa (recode 3104 5 0 boundK) x F2 := by
    have hb := h.scratch.nowrap
    refine WP.mono (recode_ok h.scratch (by decide) (by decide) (by decide) (by omega) h.cK (by omega)
      (boundK_spec h.scratch hc64 h.counter 0) (h.zero 0 (by decide))) fun d ⟨_, kd⟩ => ?_
    refine ⟨kd.scratch h.scratch, ?_, h.cS.of_keep (by decide) (by decide) fun y hy => kd.mem y (by omega),
      fun j hj => ?_⟩
    · rw [← h.counter]
      exact Mem.readW_congr fun i hi => kd.mem _ (Or.inl (by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega))
    · simp only [dig]
      rw [kd.mem _ (Or.inr (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)))]
      exact h.zero 1 (by decide) j hj
  have boundK_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block boundK) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩
  refine seq_same (recode_ct (Or.inl ⟨rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by omega) (by omega)
    (fun x h => ⟨⟨h.scratch, h.cK, boundK_spec h.scratch hc64 h.counter 0⟩, h.zero 0 (by decide)⟩) boundK_ct)
    w2 ?_
  -- `S`'s digits.
  have w3 (x : State) (h : F2 x) : WP isa (recode 3176 8 1 boundS) x (Scratch · base) :=
    WP.mono (recode_ok h.1 (by decide) (by decide) (by decide) (by decide) h.2.2.1 (by decide)
      (boundS_spec x base 1) h.2.2.2) fun _ ⟨_, ke⟩ => ke.scratch h.1
  refine seq_same (recode_ct (Or.inr ⟨rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun x h => ⟨⟨h.1, h.2.2.1, boundS_spec x base 1⟩, h.2.2.2⟩)
    (noMem_ct _ ⟨_, by taint_decide⟩)) w3 ?_
  exact rdi_ct (fun x h => h.rdi) (taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) ⟨_, by taint_decide⟩)

end VG.Proof.Ed25519.X86_64
