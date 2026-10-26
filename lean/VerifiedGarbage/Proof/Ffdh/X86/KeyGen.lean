module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86.KeyCut
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
public import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-!
# `vg_ffdh_generate_key` on i686: the key pair

`export_ok`: a wide slot's number, or zeros unless accepted, to an output.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- An output of `len` bytes at synthetic argument `p`. -/
structure OutAt (args : Nat → BitVec 32) (base : Addr) (bytes len p : Nat) (sp : BitVec 32) (wr : List Region) :
    Prop where
  fit : (args p).toNat + len ≤ 2 ^ 32
  wr : InRegions wr (byteAddr (args p)) len
  apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args p), len⟩
  frame : Region.Disjoint ⟨sp.setWidth 64, 76⟩ ⟨byteAddr (args p), len⟩
  below : Region.Disjoint ⟨byteAddr (args p), len⟩ (below sp 96)

theorem OutAt.keep {p : Nat} {sp : BitVec 32} {wr : List Region} (O : OutAt args base bytes len p sp wr) {t : State}
    {rs : List Reg} (e : s.wr = wr) (K : Keeps rs s t) : OutAt args base bytes len p sp t.wr := by
  rw [K.2.2, e]; exact O

/-- The working space through a write apart from it. -/
theorem out_val32 {r : Region} {m m' : Mem} (F : Frame [r] m m') (hr : Region.Disjoint ⟨base, bytes⟩ r)
    (nw : base.toNat + bytes ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 * k ≤ bytes) :
    val32 m' base d k = val32 m base d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) (fun r' hr' => ?_)
    (by omega_arith))
  obtain rfl := List.mem_singleton.mp hr'
  exact hr.sub_left (Offset.sub_base base (by omega_arith))

/-- The slots and the header through a write apart from the working space. -/
theorem kept_out (h : In Ex base bytes len args s) {r : Region} {m m' : Mem} (F : Frame [r] m m')
    (hr : Region.Disjoint ⟨base, bytes⟩ r) : Kept base len [] [] m m' := by
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine ⟨fun j hj9 hj _ => ?_, fun d hd hd' _ _ => ?_⟩
  · have := slot_fit1 h (j := j) (by omega_arith)
    have bw := bc_eq_cwc len .wide
    rw [cb1] at this
    exact out_val32 F hr nw (by omega_arith)
  · rw [← w32_val32_one, ← w32_val32_one]
    exact out_val32 F hr nw (by omega_arith)

/-- The wide slot 19's number, or zeros unless the acceptance word is set, to the output at `p`. -/
theorem export_ok (h : In Ex base bytes len args s) {p l : Nat} (hp : p < 18) (hl : l < 18)
    (lenArg : args l = BitVec.ofNat 32 len) (O : OutAt args base bytes len p (s.gpr .esp) s.wr) {c : Bool}
    (hm : s.mem.readW (off base accOff) 32 = cmask c) {v : Nat}
    (hv : val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) = v) (vlt : c = true → v < 2 ^ (8 * len)) :
    WP isa (exportTo p l) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args p)) len = Spec.Rsa.i2osp (if c then v else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 c.toNat ∧
      Frame (⟨byteAddr (args p), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ In Ex base bytes len args t ∧
      Kept base len [19] [] s.mem t.mem := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have e19 := lo_wide len 19
  unfold exportTo
  refine maskResult_ok h (c := c) hm fun u₉ O₉ V₉ K₉ => ?_
  have S₉ : Step Ex base bytes len args s u₉ := Step.slot h (by decide) O₉ K₉
  refine WP.mono (writeTo_ok S₉.inp hp hl lenArg O.fit ((O.keep rfl S₉.keeps).wr) O.apart)
    fun t ⟨B, A, Ft, Kt⟩ => ⟨?_, ?_, ?_, S₉.keeps.trans (Kt.mono (by decide)),
      KeyCut.in_keepOut S₉.inp Kt (by decide) (by decide) Ft (by rw [S₉.esp]; exact O.frame),
      (kept_slot h (a := 19) O₉).trans ((kept_out S₉.inp Ft O.apart).mono)⟩
  · rw [V₉, hv] at B
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at B ⊢
      exact B (Nat.two_pow_pos _)
    · simp only [↓reduceIte] at B ⊢
      exact B (vlt rfl)
  · have a₉ : u₉.mem.readW (off base accOff) 32 = cmask c := by
      rw [show u₉.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 from
        BitVec.eq_of_toNat_eq (O₉.w32 (d := accOff) (.inl (by omega_arith)) (by omega_arith)), hm]
    rw [A, a₉, cmask_and_one]
  · refine (S₉.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans (Ft.mono fun r hr => ?_)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

/-- The wide slot `a` copied into 19. -/
theorem copy19_ok (h : In Ex base bytes len args s) {a : Nat} (ha : a ≤ 18) :
    WP isa (copy (.slot .wide a) (.slot .wide 19) (one .wide)) s fun u => Step Ex base bytes len args s u ∧
      val32 u.mem base (lo len (.slot .wide 19)) (cwc len .wide) = sv s.mem base len .wide a ∧
      Kept base len [19] [] s.mem u.mem := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ea := lo_wide len a
  have e19 := lo_wide len 19
  have := Nat.mul_le_mul_right (st len .wide) ha
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide 19) (one_ok .wide)
    (slot_fit1 h (by omega_arith)) (slot_fit1 h (by decide)) (by rw [cb1]; exact .inr (by omega_arith)))
    fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by decide) O K, V, kept_slot h O⟩

/-- x and y (the wide slots 13 and 12), or zeros unless accepted, to the outputs at 0 and 8. -/
theorem outputs_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr) (h9 : args 9 = BitVec.ofNat 32 len)
    (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩) {c : Bool}
    (hm : w32 s.mem base accOff = (cmask c).toNat) {x y : Nat} (hx : sv s.mem base len .wide 13 = x)
    (hy : sv s.mem base len .wide 12 = y) (xlt : c = true → x < 2 ^ (8 * len)) (ylt : c = true → y < 2 ^ (8 * len)) :
    WP isa GenerateKey.outputs s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if c then x else 0) len ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 8)) len = Spec.Rsa.i2osp (if c then y else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 c.toNat ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  have acc {m : Mem} (e : w32 m base accOff = (cmask c).toNat) : m.readW (off base accOff) 32 = cmask c :=
    BitVec.eq_of_toNat_eq e
  unfold GenerateKey.outputs
  refine WP.seq (WP.mono (copy19_ok h (a := 13) (by decide)) fun u₁ ⟨S₁, V₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (export_ok S₁.inp (p := 0) (l := 1) (c := c) (by decide) (by decide) h.outLen
    (by rw [S₁.esp]; exact Ox.keep rfl S₁.keeps) (acc (by rw [k₁.word_eq]; exact hm)) (by rw [V₁, hx]) xlt)
    fun u₂ ⟨Bx, _, F₂, K₂, I₂, k₂⟩ => ?_)
  have S₁₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := S₁.keeps.trans K₂
  refine WP.seq (WP.mono (copy19_ok I₂ (a := 12) (by decide)) fun u₃ ⟨S₃, V₃, k₃⟩ => ?_)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := by rw [S₃.esp, K₂.1 _ (by decide), S₁.esp]
  refine WP.mono (export_ok S₃.inp (p := 8) (l := 9) (c := c) (by decide) (by decide) h9
    (by rw [sp₃]; exact Oy.keep rfl (S₁₂.trans S₃.keeps)) (acc (by rw [k₃.word_eq, k₂.word_eq, k₁.word_eq]; exact hm))
    (by rw [V₃, k₂.slot_eq, k₁.slot_eq, hy]) ylt) fun t ⟨By, A, F₄, K₄, _, _⟩ => ?_
  have sp₁ : u₁.gpr .esp = s.gpr .esp := S₁.esp
  have sp₂ : u₂.gpr .esp = s.gpr .esp := by rw [K₂.1 _ (by decide), sp₁]
  rw [sp₁] at F₂
  rw [sp₃] at F₄
  have F₃ := S₃.frame
  rw [sp₂] at F₃
  refine ⟨?_, By, A, ?_, (S₁₂.trans S₃.keeps).trans K₄⟩
  · rw [← Bx]
    have := h.upper
    refine frame_bytes ((F₃.mono fun r hr => List.mem_cons_of_mem _ hr).trans F₄) (fun r hr => ?_) (by omega_arith)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact xy
    · rw [frameR, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨q, hq, rfl⟩
      · exact Ox.below
      · have := fR_fit h q hq
        exact Ox.apart.symm.sub_right (Offset.sub_base _ (by omega_arith))
  · have F₁ := S₁.frame
    refine ((F₁.mono fun r hr => ?_).trans (F₂.mono fun r hr => ?_)).trans
      ((F₃.mono fun r hr => ?_).trans (F₄.mono fun r hr => ?_))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

/-- The wide slot `a` copied into `b`. -/
theorem copyW_ok (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 19) (hb : b ≤ 19) (hab : a ≠ b) :
    WP isa (copy (.slot .wide a) (.slot .wide b) (one .wide)) s fun u => Step Ex base bytes len args s u ∧
      sv u.mem base len .wide b = sv s.mem base len .wide a ∧ Kept base len [b] [] s.mem u.mem := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ea := lo_wide len a
  have eb := lo_wide len b
  have apart : Apart (lo len (.slot .wide b)) (cb len (one .wide)) (lo len (.slot .wide a)) (cb len (one .wide)) := by
    rw [cb1]
    rcases Nat.lt_or_gt_of_ne hab with l | l
    · have := Nat.mul_le_mul_right (st len .wide) (Nat.succ_le_of_lt l); rw [Nat.succ_mul] at this
      exact .inr (by omega_arith)
    · have := Nat.mul_le_mul_right (st len .wide) (Nat.succ_le_of_lt l); rw [Nat.succ_mul] at this
      exact .inl (by omega_arith)
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide b) (one_ok .wide)
    (slot_fit1 h (by omega_arith)) (slot_fit1 h (by omega_arith)) apart) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by omega_arith) O K, V, kept_slot h O⟩

/-- The tail up to its branch on q. -/
abbrev tailFront : List (Prog isa) :=
  [powP 10 13, copy (.slot .wide 6) (.slot .wide 12) (one .wide), rangeMask 12, .block [.store (sc accOff) .ecx],
    .block qTest]

/-- The tail's branch on q. -/
abbrev qBranch : Prog isa :=
  .seq (powP 12 16) (.seq (equal (.slot .wide 6) (.slot .wide 3) (one .wide))
    (.block [.alu .and .ecx (.mem (sc accOff)), .store (sc accOff) .ecx]))

/-- The status from the acceptance's low bit. -/
abbrev statusOf : List Instr :=
  [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)]

theorem tail_eq : GenerateKey.tail =
    Prog.chain tailFront (.seq (.ite .e (.block []) qBranch) (.seq GenerateKey.outputs (.block statusOf))) := rfl

/-- `y = g^x mod P` into the wide slot 12, its range into the acceptance word, and ZF telling whether
there is no q. -/
theorem tailFront_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    {P : Nat} (hP : safeM (sv s.mem base len .wide 9) = P) :
    WP isa (Prog.chain tailFront (.block [])) s fun u =>
      Step Ex base bytes len args s u ∧ Kept base len [12] [maskOff, accOff] s.mem u.mem ∧
      sv u.mem base len .wide 12 = sv s.mem base len .wide 10 ^ sv s.mem base len .wide 13 % P ∧
      w32 u.mem base accOff = (cmask (decide (sv u.mem base len .wide 12 < sv s.mem base len .wide 15) &&
        decide (sv s.mem base len .wide 14 < sv u.mem base len .wide 12))).toNat ∧
      isa.eval .e u = some (decide (dlen = 2 * len)) := by
  have ao : accOff = 8 := rfl
  have mo : maskOff = 12 := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (powP_ok h (P := P) (b := 10) (e := 13) (by decide) (by decide) (by decide) (by decide) hP)
    fun u₁ ⟨C₁, Y₁, _, F₁, k₁, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u₁ := Step.ops h F₁ K₁
  refine WP.seq (WP.mono (copyW_ok C₁.inp (a := 6) (b := 12) (by decide) (by decide) (by decide))
    fun u₂ ⟨S₂, V₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (rangeMask_ok S₂.inp (a := 12) (by decide)) fun u₃ ⟨I₃, e₃, O₃, K₃⟩ => ?_)
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.word S₂.inp (by decide) O₃ K₃
  have k₃ := kept_word S₂.inp (d := maskOff) (by decide) (by decide) O₃
  refine WP.seq (WP.mono (storeMask_ok I₃ (d := accOff) (by omega_arith) e₃) fun u₄ ⟨I₄, O₄, W₄, _, K₄⟩ => ?_)
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.word I₃ (by omega_arith) O₄ K₄
  have k₄ := kept_word I₃ (d := accOff) (by omega_arith) (by decide) O₄
  have S₁₄ := ((S₁.trans S₂).trans S₃).trans S₄
  refine WP.seq (WP.mono (qTest_ok I₄ G.e3 G.e12 G.dl) fun t ⟨z, m, K⟩ => WP.block_nil ?_)
  have S₅ : Step Ex base bytes len args u₄ t := Step.regs I₄ m K
  have kk : Kept base len [12] [maskOff, accOff] s.mem t.mem :=
    (((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans (by rw [m]; exact (Kept.refl _).mono)
  have v12 : sv t.mem base len .wide 12 = sv u₂.mem base len .wide 12 := by
    rw [m, k₄.slot_eq, k₃.slot_eq]
  refine ⟨S₁₄.trans S₅, kk, ?_, ?_, z⟩
  · rw [v12, V₂, Y₁]
  · rw [show w32 t.mem base accOff = w32 u₄.mem base accOff by rw [m], W₄, v12,
      k₂.slot_eq (j := 15), k₂.slot_eq (j := 14), k₁.slot_eq (j := 15), k₁.slot_eq (j := 14)]

/-- With q: `y^q mod P = 1` and-ed into the acceptance word. -/
theorem qBranch_ok (h : In Ex base bytes len args s) {P : Nat} (hP : safeM (sv s.mem base len .wide 9) = P)
    {r : Bool} (hw : w32 s.mem base accOff = (cmask r).toNat) :
    WP isa (.seq (powP 12 16) (.seq (equal (.slot .wide 6) (.slot .wide 3) (one .wide))
      (.block [.alu .and .ecx (.mem (sc accOff)), .store (sc accOff) .ecx]))) s fun u =>
      Step Ex base bytes len args s u ∧ Kept base len [] [accOff] s.mem u.mem ∧
      w32 u.mem base accOff =
        (cmask (decide (sv s.mem base len .wide 12 ^ sv s.mem base len .wide 16 % P = 1) && r)).toNat := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (powP_ok h (P := P) (b := 12) (e := 16) (by decide) (by decide) (by decide) (by decide) hP)
    fun u₁ ⟨C₁, Y₁, one₁, F₁, k₁, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u₁ := Step.ops h F₁ K₁
  refine WP.seq (WP.mono (eqW_ok C₁.inp (a := 6) (b := 3) (by decide) (by decide)) fun u₂ ⟨m₂, e₂, K₂⟩ => ?_)
  rw [Y₁, one₁] at e₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.regs C₁.inp m₂ K₂
  refine (show WP isa (.block ([.alu .and .ecx (.mem (sc accOff))] ++ [.store (sc accOff) .ecx])) u₂ _ from
    WP.block_append (WP.mono (andMask_ok S₂.inp (d := accOff) (c' := r) (by omega_arith) e₂
      (by rw [m₂, k₁.word_eq]; exact hw)) fun u₃ ⟨e₃, m₃, K₃⟩ => ?_))
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp m₃ K₃
  refine WP.mono (storeMask_ok S₃.inp (d := accOff) (by omega_arith) e₃) fun t ⟨_, O₄, W₄, _, K₄⟩ => ?_
  have S₄ : Step Ex base bytes len args u₃ t := Step.word S₃.inp (by omega_arith) O₄ K₄
  have k₄ := kept_word S₃.inp (d := accOff) (by omega_arith) (by decide) O₄
  refine ⟨((S₁.trans S₂).trans S₃).trans S₄, k₁.mono.trans ?_, W₄⟩
  rw [m₃, m₂] at k₄
  exact k₄.mono

/-- The acceptance of `y`: its range and, with q, `y^q mod P = 1`. -/
abbrev accept (len dlen p q P y : Nat) : Bool :=
  (decide (y < pm1 len p) && decide (1 < y)) && (if dlen = 2 * len then true else decide (y ^ q % P = 1))

theorem statusOf_ok {c : Bool} (he : s.gpr .eax = BitVec.ofNat 32 c.toNat) :
    WP isa (.block statusOf) s fun t => t.gpr .eax = BitVec.ofNat 32 (if c then 1 else 3) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx] s t := by
  refine wp_addS rfl fun u1 a1 _ => wp_movS rfl fun u2 a2 _ => wp_subS rfl fun u3 a3 _ =>
    wp_movS rfl fun t a4 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [KeyScan.upd_get a4, KeyScan.upd_get a3, KeyScan.upd_get a2, KeyScan.upd_get a1, reduceCtorEq,
      ite_true, ite_false, he]
    cases c <;> rfl
  · rw [a4.mem, a3.mem, a2.mem, a1.mem]
  · exact (((a1.keeps.mono (by decide)).widen a2.keeps).widen a3.keeps).widen a4.keeps

/-- The tail: y, its acceptance, x and y written (zeros unless accepted), and `3 − 2 flag`. -/
theorem tail_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr)
    (h9a : args 9 = BitVec.ofNat 32 len) (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩)
    {p g x q P : Nat} (h9 : sv s.mem base len .wide 9 = p) (hP : safeM p = P) (h10 : sv s.mem base len .wide 10 = g)
    (h13 : sv s.mem base len .wide 13 = x) (h14 : sv s.mem base len .wide 14 = 1)
    (h15 : sv s.mem base len .wide 15 = pm1 len p) (h16 : ¬ dlen = 2 * len → sv s.mem base len .wide 16 = q)
    (xlt : x < 2 ^ (8 * len)) (Plt : P < 2 ^ (8 * len)) (Ppos : 0 < P) :
    WP isa GenerateKey.tail s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (if accept len dlen p q P (g ^ x % P) then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accept len dlen p q P (g ^ x % P) then x else 0) len ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 8)) len =
        Spec.Rsa.i2osp (if accept len dlen p q P (g ^ x % P) then g ^ x % P else 0) len ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ylt : g ^ x % P < 2 ^ (8 * len) := Nat.lt_trans (Nat.mod_lt _ Ppos) Plt
  rw [tail_eq]
  refine WP.chain_split (tailFront_ok h G (P := P) (by rw [h9, hP])) fun u ⟨S, k, V12, W, z⟩ => ?_
  rw [h10, h13] at V12
  rw [V12, h15, h14] at W
  have mid : WP isa (.ite .e (.block []) qBranch) u fun v => Step Ex base bytes len args u v ∧
      Kept base len [] [accOff] u.mem v.mem ∧
      w32 v.mem base accOff = (cmask (accept len dlen p q P (g ^ x % P))).toNat := by
    refine WP.ite _ z (fun hb => WP.block_nil ⟨⟨S.inp, Frame.refl _ _, Keeps.refl _ _⟩, (Kept.refl _).mono, ?_⟩)
      (fun hb => WP.mono (qBranch_ok S.inp (P := P) (by rw [k.slot_eq, h9, hP]) W) fun v ⟨Sv, kv, Wv⟩ =>
        ⟨Sv, kv, ?_⟩)
    · have e : dlen = 2 * len := of_decide_eq_true hb
      rw [W]; simp only [accept, e, ↓reduceIte, Bool.and_true]
    · have e : ¬ dlen = 2 * len := of_decide_eq_false hb
      rw [Wv, V12, k.slot_eq (j := 16), h16 e]
      simp only [accept, e, ↓reduceIte]; rw [Bool.and_comm]
  refine WP.seq (WP.mono mid fun v ⟨Sv, kv, Wv⟩ => ?_)
  have Su := S.trans Sv
  refine WP.seq (WP.mono (outputs_ok Su.inp (by rw [Su.esp]; exact Ox.keep rfl Su.keeps)
    (by rw [Su.esp]; exact Oy.keep rfl Su.keeps) h9a xy Wv (by rw [kv.slot_eq, k.slot_eq, h13])
    (by rw [kv.slot_eq, V12]) (fun _ => xlt) (fun _ => ylt)) fun w ⟨Bx, By, A, F, K⟩ => ?_)
  refine WP.mono (statusOf_ok A) fun t ⟨E, M, Kt⟩ => ⟨E, by rw [M]; exact Bx, by rw [M]; exact By, ?_,
    (Su.keeps.trans K).trans (Kt.mono (by decide))⟩
  rw [M, Su.esp] at *
  exact (Su.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans F

/-! ## The bound's octets -/

theorem boundAt_eq {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) :
    KeyScan.boundAt args = args 2 + BitVec.ofNat 32 (2 * (dlen - 2 * len)) := by
  have dl := G.dl
  have up := G.upper
  unfold KeyScan.boundAt
  rw [G.e12, G.e3, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith),
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega_arith

/-- The bound's octets are within the domain: q's, or p's. -/
theorem bound_geo {dlen : Nat} {sp : BitVec 32} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) :
    KeyScan.BGeo base bytes len (KeyScan.boundAt args) sp rd wr := by
  have dl := G.dl
  have up := G.upper
  have fit := G.fit
  have ho : 2 * (dlen - 2 * len) + len ≤ dlen := by omega_arith
  have ea : byteAddr (KeyScan.boundAt args) = byteAddr (args 2) + BitVec.ofNat 64 (2 * (dlen - 2 * len)) := by
    rw [boundAt_eq G]; exact addr_eq (by omega_arith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [boundAt_eq G, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * _) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [ea]; exact VG.CallLay.inRegions_sub G.rd ho (by omega_arith)
  · rw [ea]; exact G.apart.sub_left (Offset.sub_base _ ho)
  · rw [ea]; exact hb40.sub_left (Offset.sub_base _ ho)

theorem bound_bytes {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) (m : Mem) :
    Spec.Rsa.bytesAt m (byteAddr (KeyScan.boundAt args)) len =
      KeyScalar.bnd len (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen) := by
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have fit := G.fit
  have ea : byteAddr (KeyScan.boundAt args) = byteAddr (args 2) + BitVec.ofNat 64 (2 * (dlen - 2 * len)) := by
    rw [boundAt_eq G]; exact addr_eq (by omega_arith)
  rw [ea]
  unfold KeyScalar.bnd
  rw [VG.Proof.Bignum.bytesAt_length]
  rcases dl with e | e
  · have : ¬ dlen = 3 * len := by omega_arith
    rw [ite_eq_right this, VG.Proof.Ffdh.take_bytesAt m _ (k := len) (dl := dlen) (by omega_arith), show 2 * (dlen - 2 * len) = 0 by omega_arith,
      BitVec.add_zero]
  · rw [ite_eq_left e, VG.Proof.Dsa.bytesAt_slice m _ (total := dlen) (offset := 2 * len) (len := len) (by omega_arith), show 2 * (dlen - 2 * len) = 2 * len by omega_arith]

/-! ## The scalar -/

/-- The domain's octets. -/
abbrev domOf (m : Mem) (args : Nat → BitVec 32) (dlen : Nat) : List Byte :=
  Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen

/-- The bound's octets. -/
abbrev bndOf (m : Mem) (args : Nat → BitVec 32) (len dlen : Nat) : List Byte :=
  KeyScalar.bnd len (domOf m args dlen)

/-- The mask of the cut's first octet. -/
abbrev maskOf (m : Mem) (args : Nat → BitVec 32) (len dlen : Nat) : Byte :=
  BitVec.ofNat 8 (KeyScalar.smearN ((bndOf m args len dlen).getD (VG.Proof.Ffdh.lead (bndOf m args len dlen)) 0).toNat)

/-- The scalar the code cuts from `rand`. -/
abbrev scalarOf (m : Mem) (args : Nat → BitVec 32) (len dlen : Nat) : Nat :=
  Spec.Rsa.os2ip (KeyScalar.cut (Spec.Rsa.bytesAt m (byteAddr (args 10)) len)
    (VG.Proof.Ffdh.lead (bndOf m args len dlen)) (maskOf m args len dlen))

/-- The body up to its branch on the scalar. -/
abbrev mainFront : List (Prog isa) :=
  [pSetup, load (.slot .wide 10) (one .wide) 4 5, GenerateKey.scan, GenerateKey.cut,
    load (.slot .wide 13) (one .wide) 0 1, CheckPrivate.bound, CheckPrivate.scalarMask, testMask]

theorem main_eq : GenerateKey.main = Prog.chain mainFront (.ite .e GenerateKey.fail GenerateKey.tail) := rfl

/-- A component through a write of `x`, apart from the domain. -/
theorem comp_x {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩) {m m' : Mem}
    (F : Frame [⟨byteAddr (args 0), len⟩] m m') {k : Nat} (hk : k * len + len ≤ dlen) :
    comp m' args len k = comp m args len k := by
  have := G.fit
  unfold comp
  rw [frame_bytes F (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact domX.sub_left (Offset.sub_base _ hk)) (by omega_arith)]

theorem w32_ofNat {m : Mem} {d n : Nat} (h : w32 m base d = n) (hn : n < 2 ^ 32) :
    m.readW (off base d) 32 = BitVec.ofNat 32 n :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h)

/-- What the body's front leaves. -/
structure Front (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat)
    (args : Nat → BitVec 32) (s u : State) : Prop where
  inp : In Ex base bytes len args u
  frame : Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u
  gate : Gate u (Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) (scalarOf s.mem args len dlen) = false)
  v9 : sv u.mem base len .wide 9 = comp s.mem args len 0
  v10 : sv u.mem base len .wide 10 = comp s.mem args len 1
  v13 : sv u.mem base len .wide 13 = scalarOf s.mem args len dlen
  v14 : sv u.mem base len .wide 14 = 1
  v15 : sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0)
  v16 : ¬ dlen = 2 * len → sv u.mem base len .wide 16 = comp s.mem args len 2

/-- The front up to the bound. -/
abbrev prefixList : List (Prog isa) :=
  [pSetup, load (.slot .wide 10) (one .wide) 4 5, GenerateKey.scan, GenerateKey.cut,
    load (.slot .wide 13) (one .wide) 0 1]

/-- What the front leaves up to the bound. -/
structure Pref (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat)
    (args : Nat → BitVec 32) (s u : State) : Prop where
  inp : In Ex base bytes len args u
  frame : Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u
  v9 : sv u.mem base len .wide 9 = comp s.mem args len 0
  v10 : sv u.mem base len .wide 10 = comp s.mem args len 1
  v13 : sv u.mem base len .wide 13 = scalarOf s.mem args len dlen
  v14 : sv u.mem base len .wide 14 = 1
  v15 : sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0)
  q : ¬ dlen = 2 * len → comp u.mem args len 2 = comp s.mem args len 2

theorem prefix_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (C : KeyCut.CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr)
    (rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩)
    (r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below (s.gpr .esp) 96))
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩) :
    WP isa (Prog.chain prefixList (.block [])) s (Pref Ex base bytes len dlen args s) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have up := G.upper
  have h2 : 2 * len ≤ dlen := by omega_arith
  have hpa := comp_p s.mem args h2
  have hqa : (CheckPrivate.params s.mem args len dlen).q =
      if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
    · have : ¬ 3 * len = 2 * len := by omega_arith
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  have nb : numBase = 3336 := rfl
  generalize hP : comp s.mem args len 0 = p at hpa
  generalize hG : comp s.mem args len 1 = g
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega_arith)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega_arith))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [CheckDomain.argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega_arith)
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega_arith), hG] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 10) O₂
  have S₁₂ := S₁.trans S₂
  -- The scan.
  have G₂ := G.keep ⟨rfl, rfl⟩ S₁₂.keeps
  refine WP.seq (WP.mono (KeyScan.scan_ok S₂.inp G.e3 (bound_geo G₂ (by rw [S₁₂.esp]; exact hb40)))
    fun u₃ Sc => ?_)
  have bs : Spec.Rsa.bytesAt u₂.mem (byteAddr (KeyScan.boundAt args)) len = bndOf s.mem args len dlen := by
    rw [bound_bytes G, dom_keep h G hb40 S₁₂.frame]
  rw [bs] at Sc
  have S₁₃ := S₁₂.trans Sc.step
  -- The cut.
  have hl : (bndOf s.mem args len dlen).length = len :=
    KeyScalar.bnd_length (by rw [VG.Proof.Bignum.bytesAt_length]; exact dl)
  have ne : bndOf s.mem args len dlen ≠ [] := by
    intro e; rw [e] at hl; simp at hl; omega_arith
  have ldlt : VG.Proof.Ffdh.lead (bndOf s.mem args len dlen) < len := by
    have := VG.Proof.Ffdh.lead_lt ne; rw [hl] at this; exact this
  have tlt : KeyScalar.smearN ((bndOf s.mem args len dlen).getD (VG.Proof.Ffdh.lead (bndOf s.mem args len dlen)) 0).toNat
      < 256 := KeyScalar.smearN_lt _ (BitVec.isLt _)
  have C₃ : KeyCut.CutGeo base bytes len (args 10) (args 0) (u₃.gpr .esp) u₃.rd u₃.wr := by
    rw [S₁₃.esp, S₁₃.keeps.2.1, S₁₃.keeps.2.2]; exact C
  refine WP.seq (WP.mono (KeyCut.cut_ok Sc.step.inp ldlt C₃ G.e3 (w32_ofNat Sc.ld (by omega_arith))
    (tt := maskOf s.mem args len dlen) (by
      rw [w32_ofNat Sc.t (by omega_arith)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      omega_arith)) fun u₄ Ct => ?_)
  have rb : Spec.Rsa.bytesAt u₃.mem (byteAddr (args 10)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len :=
    KeyScan.bytes_keep h rWs (by omega_arith) r40 S₁₃.frame
  have Cxv := Ct.x
  rw [rb] at Cxv
  have kc := kept_out Sc.step.inp Ct.frame C.xWs.symm
  have S₁₄k : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₄ := S₁₃.keeps.trans Ct.keeps
  -- x.
  have xrd : InRegions (u₄.rd ++ u₄.wr) (byteAddr (args 0)) len := by
    rw [S₁₄k.2.1, S₁₄k.2.2]
    obtain ⟨r, hr, hc⟩ := C.xwr
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (load_ok Ct.inp (one_ok .wide) (slot_fit1 Ct.inp (j := 13) (by decide)) (p := 0) (l := 1)
    (L := len) (by decide) (by decide) h.outLen (by omega_arith) (by rw [cb1]; exact len_le_bc len) C.xfit xrd
    C.xWs) fun u₅ ⟨V₅, O₅, K₅⟩ => WP.block_nil ?_)
  rw [cw1, Cxv] at V₅
  rw [cb1] at O₅
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.slot Ct.inp (by decide) O₅ K₅
  have k₅ := kept_slot Ct.inp (a := 13) O₅
  have k₁₅ : Kept base len [9, 10, 13, 14, 15] [tbOff, foundOff, ldOff, tOff] s.mem u₅.mem :=
    (((k₁.mono.trans k₂.mono).trans Sc.kept.mono).trans kc.mono).trans k₅.mono
  have v9 : sv u₅.mem base len .wide 9 = p := by
    rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, k₂.slot_eq, V9]
  have v10 : sv u₅.mem base len .wide 10 = g := by rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, V₂]
  have v14 : sv u₅.mem base len .wide 14 = 1 := by
    rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, k₂.slot_eq, V14]
  have v15 : sv u₅.mem base len .wide 15 = pm1 len p := by
    rw [k₅.slot_eq, kc.slot_eq, Sc.kept.slot_eq, k₂.slot_eq, V15]
  have S₁₅k : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ := S₁₄k.trans S₅.keeps
  have sp₃ : u₃.gpr .esp = s.gpr .esp := S₁₃.esp
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [Ct.keeps.1 _ (by decide), sp₃]
  have q₅ : ¬ dlen = 2 * len → comp u₅.mem args len 2 = comp s.mem args len 2 := fun _ => by
    have F₅ := S₅.frame
    rw [sp₄] at F₅
    rw [comp_keep h G hb40 F₅ (by omega_arith), comp_x G domX Ct.frame (by omega_arith),
      comp_keep h G hb40 S₁₃.frame (by omega_arith)]
  have F₅ := S₅.frame
  rw [sp₄] at F₅
  have F₃ := S₁₃.frame
  refine ⟨S₅.inp, ?_, S₁₅k, ?_, ?_, V₅, v14, ?_, q₅⟩
  · refine ((F₃.mono fun r hr => List.mem_cons_of_mem _ hr).trans (Ct.frame.mono fun r hr => ?_)).trans
      (F₅.mono fun r hr => List.mem_cons_of_mem _ hr)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
  · rw [v9, hP]
  · rw [v10, hG]
  · rw [v15, hP]

theorem front_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (C : KeyCut.CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr)
    (rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩)
    (r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below (s.gpr .esp) 96))
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩) :
    WP isa (Prog.chain mainFront (.block [])) s (Front Ex base bytes len dlen args s) := by
  have dl := G.dl
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega_arith
  have hpa := comp_p s.mem args h2
  have hqa : (CheckPrivate.params s.mem args len dlen).q =
      if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
    · have : ¬ 3 * len = 2 * len := by omega_arith
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  show WP isa (Prog.chain prefixList (Prog.chain [CheckPrivate.bound, CheckPrivate.scalarMask, testMask]
    (.block []))) s _
  refine WP.chain_split (prefix_ok h G hb40 C rWs r40 domX) fun u₅ P => ?_
  refine WP.mono (CheckPrivate.boundTest_ok P.inp (G.keep ⟨rfl, rfl⟩ P.keeps) P.v15 P.v13 P.v9 P.q)
    fun u₆ ⟨S₆, k₆, z, v16⟩ => ?_
  have F₆ := S₆.frame
  rw [P.keeps.1 _ (by decide)] at F₆
  refine ⟨S₆.inp, P.frame.trans (F₆.mono fun r hr => List.mem_cons_of_mem _ hr), P.keeps.trans S₆.keeps,
    Gate.of_eval z (CheckPrivate.scalar_iff hpa.symm hqa), ?_, ?_, ?_, ?_, ?_, fun n2 => by rw [v16, ite_eq_right n2]⟩
  · rw [k₆.slot_eq, P.v9]
  · rw [k₆.slot_eq, P.v10]
  · rw [k₆.slot_eq]; exact P.v13
  · rw [k₆.slot_eq, P.v14]
  · rw [k₆.slot_eq, P.v15]

/-- For a valid modulus, the code's scalar is the attempt's. -/
theorem scalar_eq_mod {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) (m : Mem)
    (mv : Spec.Rsa.modulusValid (Spec.Ffdh.domainOf len (domOf m args dlen)).p len = true) :
    scalarOf m args len dlen =
      Spec.Ffdh.scalarOfOctets (CheckPrivate.params m args len dlen) (Spec.Rsa.bytesAt m (byteAddr (args 10)) len) := by
  have lw := G.lower
  have dl := G.dl
  have hd : (domOf m args dlen).length = 2 * len ∨ (domOf m args dlen).length = 3 * len := by
    rw [VG.Proof.Bignum.bytesAt_length]; exact dl
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  have hl : (bndOf m args len dlen).length = len := KeyScalar.bnd_length hd
  have ne : bndOf m args len dlen ≠ [] := by intro e; rw [e] at hl; simp at hl; omega_arith
  refine KeyScalar.cut_eq (by omega_arith) hd (fun _ => ⟨mv.1.1.1, ?_⟩) (VG.Proof.Bignum.bytesAt_length _ _ _) ?_
  · have := Nat.two_pow_pos 511; have := mv.1.1.2; change 1 < (Spec.Ffdh.domainOf len _).p; omega_arith
  · have b := ((bndOf m args len dlen)[VG.Proof.Ffdh.lead (bndOf m args len dlen)]'(VG.Proof.Ffdh.lead_lt ne)).isLt
    rw [BitVec.toNat_ofNat, ← VG.Proof.Ffdh.getD_of (VG.Proof.Ffdh.lead_lt ne),
      Nat.mod_eq_of_lt (KeyScalar.smearN_lt _ (BitVec.isLt _)), KeyScalar.smearN_eq _ (BitVec.isLt _)]

/-- For a valid domain, the code's scalar is the attempt's. -/
theorem scalar_eq {dlen : Nat} {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) (m : Mem)
    (v : Spec.Ffdh.domainValid len (domOf m args dlen) = true) :
    scalarOf m args len dlen =
      Spec.Ffdh.scalarOfOctets (CheckPrivate.params m args len dlen) (Spec.Rsa.bytesAt m (byteAddr (args 10)) len) :=
  scalar_eq_mod G m (VG.Proof.Ffdh.domainValid_mod v)

/-! ## The body -/

theorem fail_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr) (h9a : args 9 = BitVec.ofNat 32 len)
    (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩) :
    WP isa GenerateKey.fail s fun t =>
      t.gpr .eax = BitVec.ofNat 32 2 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = List.replicate len 0 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 8)) len = List.replicate len 0 ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold GenerateKey.fail
  refine WP.seq (show WP isa (.block ([.mov .ecx (.imm 0)] ++ [.store (sc accOff) .ecx])) s _ from
    WP.block_append (wp_movS rfl fun u a _ => WP.block_nil ?_))
  have hu : In Ex base bytes len args u := h.regs a.keeps a.mem
  refine WP.mono (storeMask_ok hu (d := accOff) (c := false) (by omega_arith) a.gpr) fun v ⟨I, O, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := (Step.regs h a.mem a.keeps).trans (Step.word hu (by omega_arith) O K)
  refine WP.seq (WP.mono (outputs_ok I (by rw [S.esp]; exact Ox.keep rfl S.keeps) (by rw [S.esp]; exact Oy.keep rfl S.keeps)
    h9a xy W rfl rfl (fun e => nomatch e) (fun e => nomatch e)) fun w ⟨Bx, By, _, F, Kw⟩ => ?_)
  refine WP.mono ret_ok fun t ⟨E, M, Kt⟩ => ⟨E, ?_, ?_, ?_, (S.keeps.trans Kw).trans (Kt.mono (by decide))⟩
  · rw [M, Bx]; exact VG.Proof.Bignum.i2osp_zero' _
  · rw [M, By]; exact VG.Proof.Bignum.i2osp_zero' _
  · rw [M]; rw [S.esp] at F
    exact (S.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans F

/-- What the contract asks of the status and the outputs, for a valid domain. -/
def KeyPost (len dlen : Nat) (m : Mem) (args : Nat → BitVec 32) (r : Nat) (m' : Mem) : Prop :=
  Spec.Ffdh.domainValid len (domOf m args dlen) = true →
    let a := CheckPrivate.params m args len dlen
    let x := Spec.Ffdh.scalarOfOctets a (Spec.Rsa.bytesAt m (byteAddr (args 10)) len)
    r = Spec.Ffdh.keyStatus a x ∧
      if Spec.Ffdh.keyStatus a x = 1 then
        Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = Spec.Rsa.i2osp x len ∧
          Spec.Rsa.bytesAt m' (byteAddr (args 8)) len = Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) len
      else Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = List.replicate len 0 ∧
        Spec.Rsa.bytesAt m' (byteAddr (args 8)) len = List.replicate len 0

/-- `y`'s acceptance is `publicValid`'s, for a valid p. -/
theorem accept_iff {dlen : Nat} {a : Spec.Ffdh.Parameters} {p q y : Nat} (hp : a.p = p) (p1 : 1 < p)
    (hq : a.q = if dlen = 2 * len then none else some q) :
    accept len dlen p q p y = true ↔ Spec.Ffdh.publicValid ⟨a, y⟩ = true := by
  simp only [accept]
  rw [VG.Proof.Ffdh.publicValid_eq, hp, hq, pm1_of (by omega_arith)]
  by_cases e : dlen = 2 * len
  · simp only [e, ↓reduceIte, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq,
      false_implies, implies_true, and_true]
    exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  · simp only [e, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, forall_eq']
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨b, a⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨⟨b, a⟩, c⟩⟩

/-- A component's number fits its `len` octets. -/
theorem comp_lt (m : Mem) (k : Nat) : comp m args len k < 2 ^ (8 * len) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args 2) + BitVec.ofNat 64 (k * len)) len)
  rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] at this
  exact this

theorem body_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (C : KeyCut.CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr)
    (rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩)
    (r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below (s.gpr .esp) 96))
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr)
    (h9a : args 9 = BitVec.ofNat 32 len) (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩) :
    WP isa GenerateKey.body s fun t => ∃ r, t.gpr .eax = BitVec.ofNat 32 r ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ KeyPost len dlen s.mem args r t.mem := by
  have fit := G.fit
  have dl := G.dl
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega_arith
  unfold GenerateKey.body
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
    (h.arg (i := 3) (by decide))) fun u ⟨P, Cc, M, K⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u := Step.regs h M K
  have rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
    rw [P, K.2.1, K.2.2]
    have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  refine WP.seq (WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega_arith) rd (by rw [Cc, G.e3]))
    fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have e0 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) = comp s.mem args len 0 :=
    CheckDomain.argNum_comp s.mem args len
  rw [e0] at Z
  have S := S₁.trans (Step.regs S₁.inp Mv Kv)
  have Mvs : v.mem = s.mem := Mv.trans M
  -- A domain that is valid has a valid modulus.
  have vmod : Spec.Ffdh.domainValid len (domOf s.mem args dlen) = true →
      Spec.Rsa.modulusValid (comp s.mem args len 0) len = true := fun e => by
    have := VG.Proof.Ffdh.domainValid_mod e
    rwa [← comp_p s.mem args h2] at this
  refine WP.ite _ Z (fun valid => ?_) (fun invalid => WP.mono ret_ok fun t ⟨E, Mt, Kt⟩ =>
    ⟨0, E, ?_, S.keeps.trans (Kt.mono (by decide)), fun e => absurd (vmod e) (by rw [invalid]; decide)⟩)
  swap
  · rw [Mt, Mvs]; exact Frame.refl _ _
  -- A valid modulus: the key pair.
  have sp : v.gpr .esp = s.gpr .esp := S.esp
  have G' := G.keep ⟨rfl, rfl⟩ S.keeps
  have Cv : KeyCut.CutGeo base bytes len (args 10) (args 0) (v.gpr .esp) v.rd v.wr := by
    rw [sp, S.keeps.2.1, S.keeps.2.2]; exact C
  rw [main_eq]
  refine WP.chain_split (front_ok S.inp G' (by rw [sp]; exact hb40) Cv rWs (by rw [sp]; exact r40) domX)
    fun u F => ?_
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := S.keeps.trans F.keeps
  have spu : u.gpr .esp = s.gpr .esp := by rw [F.keeps.1 _ (by decide), sp]
  have Ox' : OutAt args base bytes len 0 (u.gpr .esp) u.wr := by rw [spu]; exact Ox.keep rfl Ku
  have Oy' : OutAt args base bytes len 8 (u.gpr .esp) u.wr := by rw [spu]; exact Oy.keep rfl Ku
  have FF : ∀ {t : State}, Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ ::
      frameR base (u.gpr .esp) (fR len)) u.mem t.mem →
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem := fun {t} Ft => by
    have Fv := F.frame
    have Fs := S.frame
    rw [sp] at Fv
    rw [spu] at Ft
    refine ((Fs.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans
      (Fv.mono fun r hr => ?_)).trans Ft
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  have pvOf : Spec.Ffdh.domainValid len (domOf s.mem args dlen) = true →
      Spec.Ffdh.parametersValid (CheckPrivate.params s.mem args len dlen) = true := fun e => by
    unfold Spec.Ffdh.domainValid at e
    simp only [Bool.and_eq_true] at e
    exact e.1
  have gate := F.gate
  rw [Mvs] at gate
  refine WP.gate gate (fun inval => WP.mono (fail_ok F.inp Ox' Oy' h9a xy) fun t ⟨E, Bx, By, Ft, Kt⟩ =>
    ⟨2, E, FF Ft, Ku.trans Kt, fun e => ?_⟩) (fun val => ?_)
  · rw [scalar_eq G s.mem e] at inval
    have ks : Spec.Ffdh.keyStatus (CheckPrivate.params s.mem args len dlen)
        (Spec.Ffdh.scalarOfOctets (CheckPrivate.params s.mem args len dlen)
          (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len)) = 2 := by
      unfold Spec.Ffdh.keyStatus; rw [inval]; rfl
    refine ⟨ks.symm, ?_⟩
    simp only [ks]
    exact ⟨Bx, By⟩
  · have v9 := F.v9
    have v10 := F.v10
    have v13 := F.v13
    have v15 := F.v15
    have v16 := F.v16
    rw [Mvs] at v9 v10 v13 v15 v16
    have hl : (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len).length = len := VG.Proof.Bignum.bytesAt_length _ _ _
    have xlt : scalarOf s.mem args len dlen < 2 ^ (8 * len) := by
      have hb : (bndOf s.mem args len dlen).length = len :=
        KeyScalar.bnd_length (by rw [VG.Proof.Bignum.bytesAt_length]; exact dl)
      have ne : bndOf s.mem args len dlen ≠ [] := by intro e; rw [e] at hb; simp at hb; omega_arith
      have ll := VG.Proof.Ffdh.lead_lt ne
      have := VG.Proof.Bignum.os2ip_lt (KeyScalar.cut (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len)
        (VG.Proof.Ffdh.lead (bndOf s.mem args len dlen)) (maskOf s.mem args len dlen))
      rw [KeyScalar.cut_length _ (by omega_arith), hl, VG.Proof.Bignum.pow256_eq] at this
      exact this
    have Plt : safeM (comp s.mem args len 0) < 2 ^ (8 * len) := by
      unfold safeM
      split
      · exact comp_lt s.mem 0
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 ≤ 8 * len by omega_arith)
        have : (2 : Nat) ^ 8 = 256 := rfl
        omega_arith
    refine WP.mono (tail_ok F.inp (G.keep ⟨rfl, rfl⟩ Ku) Ox' Oy' h9a xy v9 rfl v10 v13 F.v14 v15 v16 xlt Plt
      (Nat.lt_trans Nat.zero_lt_one (safeM_gt _))) fun t ⟨E, Bx, By, Ft, Kt⟩ =>
      ⟨_, E, FF Ft, Ku.trans Kt, fun e => ?_⟩
    dsimp only
    have mv := vmod e
    unfold Spec.Rsa.modulusValid at mv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
    have p1 : 1 < comp s.mem args len 0 := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega_arith
    have sP : safeM (comp s.mem args len 0) = comp s.mem args len 0 := safeM_of p1 mv.1.1.1
    have hpa := comp_p s.mem args h2
    have hga := comp_g s.mem args h2
    have hqa : (CheckPrivate.params s.mem args len dlen).q =
        if dlen = 2 * len then none else some (comp s.mem args len 2) := by
      rcases dl with e | e
      · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
      · have : ¬ 3 * len = 2 * len := by omega_arith
        simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
    have pv : Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) (scalarOf s.mem args len dlen) = true := by
      cases c : Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) (scalarOf s.mem args len dlen)
      · exact absurd c val
      · rfl
    rw [sP] at E Bx By ⊢
    rw [scalar_eq G s.mem e] at E Bx By pv ⊢
    rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq (pvOf e), pv, VG.Proof.Bignum.powMod_eq]
    generalize Spec.Ffdh.scalarOfOctets (CheckPrivate.params s.mem args len dlen)
      (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) = x at E Bx By pv ⊢
    have ai := accept_iff (len := len) (dlen := dlen) (y := comp s.mem args len 1 ^ x % comp s.mem args len 0)
      hpa.symm p1 hqa
    rw [show (CheckPrivate.params s.mem args len dlen).g = comp s.mem args len 1 from hga.symm,
      show (CheckPrivate.params s.mem args len dlen).p = comp s.mem args len 0 from hpa.symm]
    simp only [Bool.true_eq_false, ↓reduceIte]
    by_cases hc : accept len dlen (comp s.mem args len 0) (comp s.mem args len 2) (comp s.mem args len 0)
      (comp s.mem args len 1 ^ x % comp s.mem args len 0) = true
    · rw [hc] at E Bx By ⊢
      rw [ai.mp hc]
      simp only [↓reduceIte] at E Bx By ⊢
      exact ⟨trivial, Bx, By⟩
    · have hc' : accept len dlen (comp s.mem args len 0) (comp s.mem args len 2) (comp s.mem args len 0)
          (comp s.mem args len 1 ^ x % comp s.mem args len 0) = false := by simpa using hc
      have hv : Spec.Ffdh.publicValid ⟨CheckPrivate.params s.mem args len dlen,
          comp s.mem args len 1 ^ x % comp s.mem args len 0⟩ = false := by
        cases c : Spec.Ffdh.publicValid ⟨CheckPrivate.params s.mem args len dlen,
          comp s.mem args len 1 ^ x % comp s.mem args len 0⟩
        · rfl
        · exact absurd (ai.mpr c) hc
      rw [hc'] at E Bx By ⊢
      rw [hv]
      simp only [Bool.false_eq_true, ↓reduceIte] at E Bx By ⊢
      exact ⟨trivial, by rw [Bx]; exact VG.Proof.Bignum.i2osp_zero' _, by rw [By]; exact VG.Proof.Bignum.i2osp_zero' _⟩

end VG.Proof.Ffdh.X86.KeyGen
