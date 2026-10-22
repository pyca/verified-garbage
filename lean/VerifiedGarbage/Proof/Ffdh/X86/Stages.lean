module

public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
public import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH on i686: the stages on the wide slots

`pSetup_ok`: p (from the bytes of argument 2) in wide slot 9, one in 14 and
`p − 1` in 15. A branch on ZF after a stage is a `Gate`: a condition
that ZF tells, which runs from the same public values agree on.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

theorem cb1 (len : Nat) : cb len (one .wide) = bc len .wide := by simp [cb, one]

theorem cw1 (len : Nat) : cw len (one .wide) = cwc len .wide := bc_cw .wide

/-- A wide slot to 27, and the number in it, within the working space. -/
theorem slot_fit1 (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) :
    lo len (.slot .wide j) + cb len (one .wide) ≤ bytes := by
  have := h.slot_fit .wide hj
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  rw [cb1]; omega

/-- Two distinct wide slots lie apart. -/
theorem apart1 (len : Nat) {a b : Nat} (hab : a ≠ b) :
    Apart (lo len (.slot .wide a)) (cb len (one .wide)) (lo len (.slot .wide b)) (cb len (one .wide)) := by
  rw [cb1]
  have := slot_apart len .wide hab
  simp only [Apart]
  omega

/-- The value of the bytes of argument `p`, `L` of them. -/
abbrev argNum (m : Mem) (args : Nat → BitVec 32) (p L : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args p)) L)

/-- What a stage keeps: the wide slots 9 to 19 but those it writes, and the header's words below
the first slot but the saved mask and acceptance words where it writes them. -/
structure Kept (base : Addr) (len : Nat) (js : List Nat) (ds : List Nat) (m m' : Mem) : Prop where
  slots : ∀ j, 9 ≤ j → j ≤ 19 → j ∉ js → sv m' base len .wide j = sv m base len .wide j
  words : ∀ d, 8 ≤ d → d + 4 ≤ numBase → d % 4 = 0 → d ∉ ds → w32 m' base d = w32 m base d

theorem Kept.trans {js ds : List Nat} {m₁ m₂ m₃ : Mem} (k₁ : Kept base len js ds m₁ m₂)
    (k₂ : Kept base len js ds m₂ m₃) : Kept base len js ds m₁ m₃ :=
  ⟨fun j a b c => (k₂.slots j a b c).trans (k₁.slots j a b c),
    fun d a b e c => (k₂.words d a b e c).trans (k₁.words d a b e c)⟩

theorem Kept.mono {js ds js' ds' : List Nat} {m m' : Mem} (k : Kept base len js ds m m')
    (hj : ∀ j ∈ js, j ∈ js' := by decide) (hd : ∀ d ∈ ds, d ∈ ds' := by decide) : Kept base len js' ds' m m' :=
  ⟨fun j a b c => k.slots j a b fun hm => c (hj j hm), fun d a b e c => k.words d a b e fun hm => c (hd d hm)⟩

theorem Kept.refl (m : Mem) : Kept base len [] [] m m := ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- A number written into wide slot `a`. -/
theorem kept_slot (h : In Ex base bytes len args s) {m m' : Mem} {a : Nat}
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') : Kept base len [a] [] m m' :=
  ⟨fun j _ hj hn => slotKeep h hj (fun e => hn (by simp [e])) O,
    fun _ _ hd _ _ => slotKeep_w32 h O hd⟩

/-- The operations of a context. -/
theorem kept_ops (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) : Kept base len [] [] m m' :=
  ⟨fun _ a b _ => opsKeep_sv h F R a b, fun _ a b _ _ => opsKeep_w32 h F R a b⟩

/-- One writes `ws` and keeps the others. -/
theorem Kept.slot_eq {js ds : List Nat} {m m' : Mem} (k : Kept base len js ds m m') {j : Nat}
    (hj : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ js := by decide) : sv m' base len .wide j = sv m base len .wide j :=
  k.slots j hj.1 hj.2.1 hj.2.2

theorem Kept.word_eq {js ds : List Nat} {m m' : Mem} (k : Kept base len js ds m m') {d : Nat}
    (hd : 8 ≤ d ∧ d + 4 ≤ numBase ∧ d % 4 = 0 ∧ d ∉ ds := by decide) : w32 m' base d = w32 m base d :=
  k.words d hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

/-- p into wide slot 9, one into 14 and `p − 1` into 15. -/
theorem pSetup_ok (h : In Ex base bytes len args s) (h3 : args 3 = BitVec.ofNat 32 len)
    (fit : (args 2).toNat + len ≤ 2 ^ 32) (rd : InRegions (s.rd ++ s.wr) (byteAddr (args 2)) len)
    (apart : Region.Disjoint ⟨byteAddr (args 2), len⟩ ⟨base, bytes⟩) (pos : 0 < argNum s.mem args 2 len) :
    WP isa Impl.Ffdh.X86.pSetup s fun u =>
      In Ex base bytes len args u ∧ Frame (frameR base (s.gpr .esp) (fR len)) s.mem u.mem ∧
      Kept base len [9, 14, 15] [] s.mem u.mem ∧
      sv u.mem base len .wide 9 = argNum s.mem args 2 len ∧ sv u.mem base len .wide 14 = 1 ∧
      sv u.mem base len .wide 15 = argNum s.mem args 2 len - 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have f9 := slot_fit1 h (j := 9) (by decide)
  have f14 := slot_fit1 h (j := 14) (by decide)
  have f15 := slot_fit1 h (j := 15) (by decide)
  have c1 := cb1 len
  have w1 := cw1 len
  have lb := len_le_bc len
  have lo' := h.lower'
  unfold Impl.Ffdh.X86.pSetup
  refine WP.seq (WP.mono (load_ok h (one_ok .wide) f9 (p := 2) (l := 3) (L := len) (by decide) (by decide) h3
    (by omega) (by omega) fit rd apart) fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  rw [c1] at O₁
  rw [w1] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (setSmall_ok h₁ (one_ok .wide) f14 (v := 1) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [c1] at O₂
  rw [w1] at V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.mono (chainSub_ok h₂ (one_ok .wide) f15 f9 f14 (apart1 len (by decide)) (apart1 len (by decide)))
    fun u ⟨O₃, _, ⟨c, _, V₃⟩, K₃⟩ => ?_
  rw [c1] at O₃
  rw [w1] at V₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega))
  have k₁ := kept_slot h (a := 9) O₁
  have k₂ := kept_slot h₁ (a := 14) O₂
  have k₃ := kept_slot h₂ (a := 15) O₃
  have e9 : sv u₂.mem base len .wide 9 = argNum s.mem args 2 len := (k₂.slot_eq).trans V₁
  have e14 : sv u₂.mem base len .wide 14 = 1 := V₂
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  refine ⟨h₃, ?_, ((k₁.mono).trans k₂.mono).trans k₃.mono, k₃.slot_eq.trans e9, k₃.slot_eq.trans e14, ?_,
    (K₁.mono (by decide)).trans ((K₂.mono (by decide)).trans (K₃.mono (by decide)))⟩
  · have bst : bc len .wide ≤ st len .wide := by have est : st len .wide = 2 * bc len .wide + 32 := rfl; omega
    have F₁ := fR_of_outside h (sp := s.gpr .esp) O₁ (slot_inF (by decide) bst)
    have F₂ := fR_of_outside h (sp := s.gpr .esp) O₂ (slot_inF (by decide) bst)
    have F₃ := fR_of_outside h (sp := s.gpr .esp) O₃ (slot_inF (by decide) bst)
    exact (F₁.trans F₂).trans F₃
  · have lt := val32_lt u.mem base (lo len (.slot .wide 15)) (cwc len .wide)
    have lt9 : argNum s.mem args 2 len < 2 ^ (32 * cwc len .wide) := by
      rw [← e9]; exact val32_lt _ _ _ _
    change sv u.mem base len .wide 15 < _ at lt
    rw [show val32 u₂.mem base (lo len (.slot .wide 14)) (cwc len .wide) = 1 from e14,
      show val32 u₂.mem base (lo len (.slot .wide 9)) (cwc len .wide) = argNum s.mem args 2 len from e9] at V₃
    change sv u.mem base len .wide 15 + 1 = _ at V₃
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at V₃ <;> omega

/-- Where the wide slots lie. -/
theorem lo_wide (len j : Nat) : lo len (.slot .wide j) = numBase + j * st len .wide := rfl

/-- A copy of the wide slot `j` (9 to 19) into the context's slot `d` (to 8). -/
theorem copyIn_ok (h : In Ex base bytes len args s) {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 19) (hd : d ≤ 8) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) s fun u =>
      Outside base (lo len (.slot .wide d)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide d = sv s.mem base len .wide j ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have f := h.slot_fit .wide (j := 19) (by decide)
  have := hi_fit (len := len) hj9 hj
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have b := Nat.mul_le_mul_right (st len .wide) (show d + 1 ≤ 9 by omega)
  rw [Nat.succ_mul] at b
  have ej := lo_wide len j
  have ed := lo_wide len d
  have e9 := lo_wide len 9
  have e20 := lo_wide len 20
  have e19 := lo_wide len 19
  refine WP.mono (copy_ok h (x := .slot .wide j) (d := .slot .wide d) (one_ok .wide) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; exact .inl (by omega))) fun u ⟨O, V, K⟩ => ⟨?_, ?_, K⟩
  · rw [cb1] at O; exact O
  · rw [cw1] at V; exact V

/-- The context of p, in the wide slot 9: p in slot 0, one in 3, `R² mod p` in 4 and the inverse. -/
theorem ctxP_ok (h : In Ex base bytes len args s) {P : Nat} (hP : sv s.mem base len .wide 9 = P) (gt : 1 < P)
    (odd : P % 2 = 1) :
    WP isa Impl.Ffdh.X86.ctxP s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧
      Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have f0 := h.slot_fit .wide (j := 0) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  unfold Impl.Ffdh.X86.ctxP
  refine WP.seq (WP.mono (copyIn_ok h (j := 9) (d := 0) (by decide) (by decide) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.mono (prepCtx_ok h₁ .wide) fun u ⟨C, one, R2, F, K⟩ => ?_
  rw [V₁, hP, safeM_of gt odd] at C R2
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F
  have F₁ : Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u₁.mem :=
    stR_of_outside h (by decide) O₁ ⟨_, by simp, slot_in h .wide (j := 0) (by decide)⟩
  have F₂ := stR_widen F (prepR_in h₁ .wide 0)
  exact ⟨C, one, R2, F₁.trans F₂, (kept_ops h F₁ h.room).trans (kept_ops h F₂ h.room),
    (K₁.mono (by decide)).trans K⟩

/-- A prepared context keeps one in its slot 3 through an exponentiation. -/
theorem pwR_sv3 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (pwR len .wide)) m m') (R : CallRoom sp base bytes) :
    sv m' base len .wide 3 = sv m base len .wide 3 := by
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have T := h.table_fit .wide
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have e20 := lo_wide len 20
  have e1 := lo_wide len 1
  have e3 := lo_wide len 3
  have e5 := lo_wide len 5
  have e6 := lo_wide len 6
  have e7 := lo_wide len 7
  have e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R nw (by omega) ?_ (pwR_fit h .wide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [winOff] <;> omega

/-- Slot 6 the wide slot `b` to the power of the wide slot `e`, modulo p (in the wide slot 9). -/
theorem powP_ok (h : In Ex base bytes len args s) {P b e : Nat} (hb9 : 9 ≤ b) (hb : b ≤ 19) (he9 : 9 ≤ e)
    (he : e ≤ 19) (hP : sv s.mem base len .wide 9 = P) (gt : 1 < P) (odd : P % 2 = 1) :
    WP isa (Impl.Ffdh.X86.powP b e) s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide b ^ sv s.mem base len .wide e % P ∧
      sv u.mem base len .wide 3 = 1 ∧
      Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e0 := lo_wide len 0
  have e3 := lo_wide len 3
  have e4 := lo_wide len 4
  have e5 := lo_wide len 5
  have e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  unfold Impl.Ffdh.X86.powP
  refine WP.seq (WP.mono (ctxP_ok h hP gt odd) fun u₁ ⟨C₁, one₁, R₁, F₁, k₁, K₁⟩ => ?_)
  have h₁ := C₁.inp
  refine WP.seq (WP.mono (copyIn_ok h₁ (j := b) (d := 5) hb9 hb (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copyIn_ok h₂ (j := e) (d := 8) he9 he (by decide)) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have G₂ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₁.mem u₂.mem :=
    stR_of_outside h (by decide) O₂ ⟨_, by simp, slot_in h .wide (j := 5) (by decide)⟩
  have G₃ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₂.mem u₃.mem :=
    stR_of_outside h (by decide) O₃ ⟨_, by simp, slot_in h .wide (j := 8) (by decide)⟩
  have C₃ : CtxOk Ex base bytes len args .wide P u₃ := by
    refine C₁.keepF (regs := [.eax, .ebx, .ecx, .edx, .ebp]) (K₂.trans K₃) (by decide) (by decide)
      (ws := [(lo len (.slot .wide 5), bc len .wide), (lo len (.slot .wide 8), bc len .wide)]) ?_ ?_ ?_
    · rw [sp₁]
      exact (frameR_of_outside O₂ (by omega) (by simp)).trans
        (by rw [← sp₁]; exact frameR_of_outside O₃ (by omega) (by simp))
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega
  have kb : sv u₁.mem base len .wide b = sv s.mem base len .wide b := k₁.slots b hb9 hb (by simp)
  have ke : sv u₂.mem base len .wide e = sv s.mem base len .wide e :=
    (slotKeep h₁ he (by omega) O₂).trans (k₁.slots e he9 he (by simp))
  have B₃ : sv u₃.mem base len .wide 5 = sv s.mem base len .wide b := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, V₂, kb]
  have E₃ : sv u₃.mem base len .wide 8 = sv s.mem base len .wide e := by rw [V₃, ke]
  have one₃ : sv u₃.mem base len .wide 3 = 1 := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h₁ (by decide) (by decide) O₂, one₁]
  have R₃ : sv u₃.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h₁ (by decide) (by decide) O₂, R₁]
  refine WP.mono (windowPower_ok C₃ one₃ R₃) fun u ⟨C, F, K, Y⟩ => ?_
  rw [B₃, E₃] at Y
  rw [sp₃] at F
  have G := stR_widen F (pwR_in C₃.inp .wide 0)
  refine ⟨C, Y, ?_, ((F₁.trans G₂).trans G₃).trans G, ?_, ?_⟩
  · rw [pwR_sv3 C₃.inp F (by rw [← sp₃]; exact C₃.inp.room), one₃]
  · exact (((k₁.trans (kept_ops h G₂ h.room)).trans (kept_ops h G₃ h.room)).trans (kept_ops h G h.room))
  · exact ((K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans K

/-! ## Single instructions -/

/-- `test d, src`: ZF is `d & src = 0`. -/
theorem wp_testS {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .test d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d &&& v) false false) (by simp only [exec, execAlu, h, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

/-- `sub d, src`, and ZF. -/
theorem wp_subZ {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.zf = some (s.gpr d - v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem cmask_and_one (c : Bool) : cmask c &&& 1 = BitVec.ofNat 32 c.toNat := by cases c <;> rfl

theorem cmask_test (c : Bool) : (cmask c &&& cmask c == 0) = !c := by cases c <;> rfl

/-- The status `r`. -/
theorem ret_ok {r : Nat} :
    WP isa (Impl.Ffdh.X86.ret r) s fun u => u.gpr .eax = BitVec.ofNat 32 r ∧ u.mem = s.mem ∧ Keeps [.eax] s u :=
  wp_movS rfl fun _ U _ => WP.block_nil ⟨U.gpr, U.mem, U.keeps⟩

/-- The status of a mask. -/
theorem retMask_ok {c : Bool} (hc : s.gpr .ecx = cmask c) :
    WP isa Impl.Ffdh.X86.retMask s fun u =>
      u.gpr .eax = BitVec.ofNat 32 c.toNat ∧ u.mem = s.mem ∧ Keeps [.eax] s u :=
  wp_movS rfl fun u U _ => wp_logicS (.inl rfl) rfl fun t T => WP.block_nil
    ⟨by rw [T.gpr]; simp only [↓reduceIte]; rw [U.gpr, hc, cmask_and_one], by rw [T.mem, U.mem],
      U.keeps.trans T.keeps⟩

/-- ZF set if the mask is zero. -/
theorem testMask_ok {c : Bool} (hc : s.gpr .ecx = cmask c) :
    WP isa Impl.Ffdh.X86.testMask s fun u => isa.eval .e u = some (!c) ∧ u.mem = s.mem ∧ Keeps [] s u :=
  wp_testS rfl fun t T z => WP.block_nil ⟨by show t.zf = _; rw [z, hc, cmask_test], T.mem, T.keeps []⟩

/-- A mask stored into the header word `d`. -/
theorem storeMask_ok (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) {c : Bool}
    (hc : s.gpr .ecx = cmask c) :
    WP isa (.block [.store (sc d) .ecx]) s fun u =>
      In Ex base bytes len args u ∧ Outside base d 4 s.mem u.mem ∧ w32 u.mem base d = (cmask c).toNat ∧
      u.zf = s.zf ∧ Keeps [] s u := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_storeS (h.scratch.ea (d := d) (by omega)) (h.scratch.write (d := d) (n := 4) (by omega)) fun u M =>
    WP.block_nil ?_
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega)
  refine ⟨h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega)), O, ?_, M.zf, M.keeps []⟩
  show (u.mem.readW (off base d) 32).toNat = _
  rw [M.mem, Mem.readW_writeW_self32, hc]

/-- `ecx` and-ed with the mask in the header word `d`. -/
theorem andMask_ok (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) {c c' : Bool}
    (hc : s.gpr .ecx = cmask c) (hw : w32 s.mem base d = (cmask c').toNat) :
    WP isa (.block [.alu .and .ecx (.mem (sc d))]) s fun u =>
      u.gpr .ecx = cmask (c && c') ∧ u.mem = s.mem ∧ Keeps [.ecx] s u := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_logicS (.inl rfl) (readSrc_sc h.scratch (d := d) (by omega)) fun u U => WP.block_nil ⟨?_, U.mem, U.keeps⟩
  rw [U.gpr]; simp only [↓reduceIte]
  rw [hc, show s.mem.readW (off base d) 32 = cmask c' from BitVec.eq_of_toNat_eq hw, cmask_and]

/-- `ecx` all ones if `1 < [a] < p − 1`, for one in the wide slot 14 and `p − 1` in 15. -/
theorem rangeMask_ok (h : In Ex base bytes len args s) {a : Nat} (ha : a ≤ 19) :
    WP isa (Impl.Ffdh.X86.rangeMask a) s fun u =>
      In Ex base bytes len args u ∧
      u.gpr .ecx = cmask (decide (sv s.mem base len .wide a < sv s.mem base len .wide 15) &&
        decide (sv s.mem base len .wide 14 < sv s.mem base len .wide a)) ∧
      Outside base maskOff 4 s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have fa := slot_fit1 h (j := a) (by omega)
  have f14 := slot_fit1 h (j := 14) (by decide)
  have f15 := slot_fit1 h (j := 15) (by decide)
  have ea := lo_wide len a
  have e14 := lo_wide len 14
  have e15 := lo_wide len 15
  have nb : numBase = 3336 := rfl
  have mo : maskOff = 12 := rfl
  have w1 := cw1 len
  unfold Impl.Ffdh.X86.rangeMask
  refine WP.seq (WP.mono (lessThan_ok h (a := .slot .wide 14) (b := .slot .wide a) (one_ok .wide) f14 fa)
    fun u₁ ⟨m₁, e₁, K₁⟩ => ?_)
  have h₁ := h.regs K₁ m₁
  refine WP.seq (WP.mono (storeMask_ok h₁ (d := maskOff) (by omega) e₁) fun u₂ ⟨h₂, O₂, W₂, _, K₂⟩ => ?_)
  refine WP.seq (WP.mono (lessThan_ok h₂ (a := .slot .wide a) (b := .slot .wide 15) (one_ok .wide) fa f15)
    fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
  have h₃ := h₂.regs K₃ m₃
  have W₃ := W₂
  rw [← m₃] at W₃
  refine WP.mono (andMask_ok h₃ (d := maskOff) (by omega) e₃ W₃) fun u ⟨E, M, K⟩ => ?_
  have ce := cb_eq (len := len) (one_ok .wide)
  have v : ∀ j, j ≤ 19 → val32 u₂.mem base (lo len (.slot .wide j)) (cw len (one .wide)) =
      sv s.mem base len .wide j := by
    intro j hj
    have := lo_wide len j
    have := slot_fit1 h (j := j) (by omega)
    rw [O₂.val32 (.inr (by omega)) (by omega), m₁, w1]
  refine ⟨h₃.regs K M, ?_, by rw [M, m₃, ← m₁]; exact O₂, ?_⟩
  · rw [E, v a ha, v 15 (by decide), w1]
  · exact ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans ((K₃.mono (by decide)).trans (K.mono (by decide)))

/-! ## The operations on wide slots, by value -/

theorem lessW_ok (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 27) (hb : b ≤ 27) :
    WP isa (lessThan (.slot .wide a) (.slot .wide b) (one .wide)) s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (sv s.mem base len .wide a < sv s.mem base len .wide b)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u :=
  WP.mono (lessThan_ok h (one_ok .wide) (slot_fit1 h ha) (slot_fit1 h hb)) fun u ⟨m, e, K⟩ =>
    ⟨m, by rw [e, cw1], K⟩

theorem eqW_ok (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 27) (hb : b ≤ 27) :
    WP isa (equal (.slot .wide a) (.slot .wide b) (one .wide)) s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (sv s.mem base len .wide a = sv s.mem base len .wide b)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u :=
  WP.mono (equal_ok h (one_ok .wide) (slot_fit1 h ha) (slot_fit1 h hb)) fun u ⟨m, e, K⟩ =>
    ⟨m, by rw [e, cw1], K⟩

theorem setW_ok (h : In Ex base bytes len args s) {a v : Nat} (ha : a ≤ 27) (hv : v < 2 ^ 32) :
    WP isa (setSmall (.slot .wide a) (one .wide) v) s fun u =>
      Outside base (lo len (.slot .wide a)) (bc len .wide) s.mem u.mem ∧ sv u.mem base len .wide a = v ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u :=
  WP.mono (setSmall_ok h (one_ok .wide) (slot_fit1 h ha) hv) fun u ⟨O, V, K⟩ =>
    ⟨by rw [cb1] at O; exact O, by rw [cw1] at V; exact V, K⟩

theorem zeroW_ok (h : In Ex base bytes len args s) {a : Nat} (ha : a ≤ 27) :
    WP isa (zero (.slot .wide a) (one .wide)) s fun u =>
      Outside base (lo len (.slot .wide a)) (bc len .wide) s.mem u.mem ∧ sv u.mem base len .wide a = 0 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u :=
  WP.mono (zero_ok h (one_ok .wide) (slot_fit1 h ha)) fun u ⟨O, V, K⟩ =>
    ⟨by rw [cb1] at O; exact O, by rw [cw1] at V; exact V, K⟩

/-- A number written into a wide slot (to 27), within `fR`. -/
theorem slotF (h : In Ex base bytes len args s) {sp : BitVec 32} {a : Nat} (ha : a ≤ 27) {m m' : Mem}
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') : Frame (frameR base sp (fR len)) m m' :=
  fR_of_outside h O (slot_inF ha (by have est : st len .wide = 2 * bc len .wide + 32 := rfl; omega))

/-- A header word written, within `fR`. -/
theorem wordF (h : In Ex base bytes len args s) {sp : BitVec 32} {d : Nat} (hd : d + 4 ≤ 32) {m m' : Mem}
    (O : Outside base d 4 m m') : Frame (frameR base sp (fR len)) m m' :=
  fR_of_outside h O (.inl hd)

/-- A header word written keeps the wide slots. -/
theorem kept_word (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) (h4 : d % 4 = 0) {m m' : Mem}
    (O : Outside base d 4 m m') : Kept base len [] [d] m m' := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  refine ⟨fun j hj9 hj _ => ?_, fun e he he' e4 hn => ?_⟩
  · have := slot_fit1 h (j := j) (by omega)
    have := lo_wide len j
    have ce := cb_eq (len := len) (one_ok .wide)
    rw [cw1] at ce
    rw [cb1] at *
    exact O.val32 (.inr (by omega)) (by omega)
  · exact O.w32 (by simp only [List.mem_singleton] at hn; omega) (by omega)

/-- What a stage leaves: the status `r`, the changes within `fR`, and the registers. -/
def Res (base : Addr) (len : Nat) (s : State) (r : Nat) (t : State) : Prop :=
  t.gpr .eax = BitVec.ofNat 32 r ∧ Frame (frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t

/-- A stage's result after one before it. -/
theorem Res.after {u t : State} {r : Nat} (R : Res base len u r t) {rs : List Reg} (K : Keeps rs s u)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide)
    (F : Frame (frameR base (s.gpr .esp) (fR len)) s.mem u.mem) : Res base len s r t := by
  obtain ⟨E, F', K'⟩ := R
  rw [K.1 _ (by intro hm; have := hrs _ hm; simp at this)] at F'
  exact ⟨E, F.trans F', (K.mono hrs).trans K'⟩

/-- The status `r`. -/
theorem ret_res {r : Nat} : WP isa (Impl.Ffdh.X86.ret r) s (Res base len s r) :=
  WP.mono ret_ok fun _ ⟨E, M, K⟩ => ⟨E, by rw [M]; exact Frame.refl _ _, K.mono (by decide)⟩

/-- The status of a comparison of two wide slots. -/
theorem eqStatus_res (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 27) (hb : b ≤ 27) :
    WP isa (Impl.Ffdh.X86.eqStatus a b) s
      (Res base len s (if sv s.mem base len .wide a = sv s.mem base len .wide b then 1 else 0)) := by
  refine WP.seq (WP.mono (eqW_ok h ha hb) fun u ⟨m, e, K⟩ => WP.mono (retMask_ok e) fun t ⟨E, M, K'⟩ => ?_)
  refine ⟨by rw [E]; split <;> simp_all, by rw [M, m]; exact Frame.refl _ _, K.trans (K'.mono (by decide))⟩

/-! ## Stages -/

/-- A stage from `s` to `u`: the inputs at `u`, the changes within `fR`, and the registers. -/
structure Step (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s u : State) : Prop where
  inp : In Ex base bytes len args u
  frame : Frame (frameR base (s.gpr .esp) (fR len)) s.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u

theorem Step.trans {u t : State} (A : Step Ex base bytes len args s u) (B : Step Ex base bytes len args u t) :
    Step Ex base bytes len args s t := by
  obtain ⟨I, F, K⟩ := B
  rw [A.keeps.1 _ (by decide)] at F
  exact ⟨I, A.frame.trans F, A.keeps.trans K⟩

theorem Step.res {u t : State} {r : Nat} (A : Step Ex base bytes len args s u) (R : Res base len u r t) :
    Res base len s r t :=
  R.after A.keeps (fun _ h => h) A.frame

theorem Step.esp {u : State} (A : Step Ex base bytes len args s u) : u.gpr .esp = s.gpr .esp := A.keeps.1 _ (by decide)

/-- A stage changing one wide slot. -/
theorem Step.slot (h : In Ex base bytes len args s) {u : State} {a : Nat} (ha : a ≤ 27)
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) s.mem u.mem) {rs : List Reg}
    (K : Keeps rs s u) (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    Step Ex base bytes len args s u := by
  have bl := h.bytes_lt
  have := slot_fit1 h ha
  rw [cb1] at this
  exact ⟨h.keep K (by intro hm; have := hrs _ hm; simp at this) (by intro hm; have := hrs _ hm; simp at this)
    (O.mono (Nat.zero_le _) (by omega)), slotF h ha O, K.mono hrs⟩

/-- A stage changing a header word below the saved registers. -/
theorem Step.word (h : In Ex base bytes len args s) {u : State} {d : Nat} (hd : d + 4 ≤ 32)
    (O : Outside base d 4 s.mem u.mem) {rs : List Reg} (K : Keeps rs s u)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    Step Ex base bytes len args s u := by
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  exact ⟨h.keep K (by intro hm; have := hrs _ hm; simp at this) (by intro hm; have := hrs _ hm; simp at this)
    (O.mono (Nat.zero_le _) (by omega)), wordF h hd O, K.mono hrs⟩

/-- A stage that changes no memory. -/
theorem Step.regs (h : In Ex base bytes len args s) {u : State} (m : u.mem = s.mem) {rs : List Reg}
    (K : Keeps rs s u) (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    Step Ex base bytes len args s u :=
  ⟨h.regs K m (by intro hm; have := hrs _ hm; simp at this) (by intro hm; have := hrs _ hm; simp at this),
    by rw [m]; exact Frame.refl _ _, K.mono hrs⟩

/-- A stage of the operations of a context. -/
theorem Step.ops (h : In Ex base bytes len args s) {u : State}
    (F : Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u.mem) {rs : List Reg} (K : Keeps rs s u)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    Step Ex base bytes len args s u :=
  ⟨h.keepF K (by intro hm; have := hrs _ hm; simp at this) (by intro hm; have := hrs _ hm; simp at this) F
    (stR_fit h (by decide)), fR_widen F (stR_inF h), K.mono hrs⟩

/-! ## Branches -/

/-- A chain of stages, then the rest. -/
theorem WP.chain_split {l : List (Prog isa)} {rest : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (Prog.chain l (.block [])) s P) (k : ∀ u, P u → WP isa rest u Q) :
    WP isa (Prog.chain l rest) s Q := by
  induction l generalizing s with
  | nil => exact k _ (WP.block_nil_iff.mp h)
  | cons c l ih => exact WP.seq (WP.mono (WP.seq_iff.mp h) fun u hu => ih hu)

/-- ZF tells whether `C` holds. -/
def Gate (u : State) (C : Prop) : Prop := ∃ b, isa.eval .e u = some b ∧ (b = true ↔ C)

theorem Gate.of_eval {u : State} {C : Prop} {b : Bool} (h : isa.eval .e u = some b) (hb : b = true ↔ C) :
    Gate u C := ⟨b, h, hb⟩

theorem Gate.keep {u v : State} {C : Prop} (G : Gate u C) (z : v.zf = u.zf) : Gate v C := by
  obtain ⟨b, h, hb⟩ := G
  exact ⟨b, by show v.zf = _; rw [z]; exact h, hb⟩

/-- Two states that tell the same condition branch alike. -/
theorem Gate.agree {u v : State} {C : Prop} (G₁ : Gate u C) (G₂ : Gate v C) : isa.eval .e u = isa.eval .e v := by
  obtain ⟨b₁, h₁, i₁⟩ := G₁
  obtain ⟨b₂, h₂, i₂⟩ := G₂
  rw [h₁, h₂]
  congr 1
  cases b₁ <;> cases b₂ <;> simp_all

/-- A branch on a gate: `th` when `C` holds, `el` otherwise. -/
theorem WP.gate {u : State} {C : Prop} (G : Gate u C) {th el : Prog isa} {Q : State → Prop}
    (ht : C → WP isa th u Q) (he : ¬ C → WP isa el u Q) : WP isa (.ite .e th el) u Q := by
  obtain ⟨b, h, hb⟩ := G
  refine WP.ite b h (fun e => ht (hb.mp e)) fun e => he fun c => ?_
  rw [hb.mpr c] at e; cases e

end VG.Proof.Ffdh.X86
