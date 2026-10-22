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
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.Stages

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
  below : Region.Disjoint ⟨byteAddr (args p), len⟩ (below sp 40)

theorem OutAt.keep {p : Nat} {sp : BitVec 32} {wr : List Region} (O : OutAt args base bytes len p sp wr) {t : State}
    {rs : List Reg} (e : s.wr = wr) (K : Keeps rs s t) : OutAt args base bytes len p sp t.wr := by
  rw [K.2.2, e]; exact O

/-- The working space through a write apart from it. -/
theorem out_val32 {r : Region} {m m' : Mem} (F : Frame [r] m m') (hr : Region.Disjoint ⟨base, bytes⟩ r)
    (nw : base.toNat + bytes ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 * k ≤ bytes) :
    val32 m' base d k = val32 m base d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) (fun r' hr' => ?_)
    (by omega))
  obtain rfl := List.mem_singleton.mp hr'
  exact hr.sub_left (Offset.sub_base base (by omega))

/-- The slots and the header through a write apart from the working space. -/
theorem kept_out (h : In Ex base bytes len args s) {r : Region} {m m' : Mem} (F : Frame [r] m m')
    (hr : Region.Disjoint ⟨base, bytes⟩ r) : Kept base len [] [] m m' := by
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine ⟨fun j hj9 hj _ => ?_, fun d hd hd' _ _ => ?_⟩
  · have := slot_fit1 h (j := j) (by omega)
    have bw := bc_eq_cwc len .wide
    rw [cb1] at this
    exact out_val32 F hr nw (by omega)
  · rw [← w32_val32_one, ← w32_val32_one]
    exact out_val32 F hr nw (by omega)

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
        BitVec.eq_of_toNat_eq (O₉.w32 (d := accOff) (.inl (by omega)) (by omega)), hm]
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
    (slot_fit1 h (by omega)) (slot_fit1 h (by decide)) (by rw [cb1]; exact .inr (by omega)))
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
    refine frame_bytes ((F₃.mono fun r hr => List.mem_cons_of_mem _ hr).trans F₄) (fun r hr => ?_) (by omega)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact xy
    · rw [frameR, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨q, hq, rfl⟩
      · exact Ox.below
      · have := fR_fit h q hq
        exact Ox.apart.symm.sub_right (Offset.sub_base _ (by omega))
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
      exact .inr (by omega)
    · have := Nat.mul_le_mul_right (st len .wide) (Nat.succ_le_of_lt l); rw [Nat.succ_mul] at this
      exact .inl (by omega)
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide b) (one_ok .wide)
    (slot_fit1 h (by omega)) (slot_fit1 h (by omega)) apart) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by omega) O K, V, kept_slot h O⟩

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
  refine WP.seq (WP.mono (storeMask_ok I₃ (d := accOff) (by omega) e₃) fun u₄ ⟨I₄, O₄, W₄, _, K₄⟩ => ?_)
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.word I₃ (by omega) O₄ K₄
  have k₄ := kept_word I₃ (d := accOff) (by omega) (by decide) O₄
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
    WP.block_append (WP.mono (andMask_ok S₂.inp (d := accOff) (c' := r) (by omega) e₂
      (by rw [m₂, k₁.word_eq]; exact hw)) fun u₃ ⟨e₃, m₃, K₃⟩ => ?_))
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp m₃ K₃
  refine WP.mono (storeMask_ok S₃.inp (d := accOff) (by omega) e₃) fun t ⟨_, O₄, W₄, _, K₄⟩ => ?_
  have S₄ : Step Ex base bytes len args u₃ t := Step.word S₃.inp (by omega) O₄ K₄
  have k₄ := kept_word S₃.inp (d := accOff) (by omega) (by decide) O₄
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

end VG.Proof.Ffdh.X86.KeyGen
