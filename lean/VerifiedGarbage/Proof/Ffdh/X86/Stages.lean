module

public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.PrepCall
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
public import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame

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
  rw [cb1]; omega_arith

/-- Two distinct wide slots lie apart. -/
theorem apart1 (len : Nat) {a b : Nat} (hab : a ≠ b) :
    Apart (lo len (.slot .wide a)) (cb len (one .wide)) (lo len (.slot .wide b)) (cb len (one .wide)) := by
  rw [cb1]
  have := slot_apart len .wide hab
  simp only [Apart]
  omega_arith

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

/-- The operations of a context, called, keep the FFDH slots and the header's words from 8 on. -/
theorem keptF_ops (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameF base sp (stR len 0)) m m') (R : RoomF sp base bytes) : Kept base len [] [] m m' := by
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine ⟨fun j a b _ => ?_, fun d a b _ _ => ?_⟩
  · have := hi_fit (len := len) a b
    exact opsKeepF h F R (.inl ⟨this.1, by omega_using [this, bw, est]⟩)
  · rw [← w32_val32_one, ← w32_val32_one]
    exact opsKeepF h F R (.inr ⟨a, by omega_using [b]⟩)

/-- One writes `ws` and keeps the others. -/
theorem Kept.slot_eq {js ds : List Nat} {m m' : Mem} (k : Kept base len js ds m m') {j : Nat}
    (hj : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ js := by decide) : sv m' base len .wide j = sv m base len .wide j :=
  k.slots j hj.1 hj.2.1 hj.2.2

theorem Kept.word_eq {js ds : List Nat} {m m' : Mem} (k : Kept base len js ds m m') {d : Nat}
    (hd : 8 ≤ d ∧ d + 4 ≤ numBase ∧ d % 4 = 0 ∧ d ∉ ds := by decide) : w32 m' base d = w32 m base d :=
  k.words d hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

/-- What `pSetup` leaves in slot 15: `p − 1`, or all ones for a p of zero. -/
def pm1 (len p : Nat) : Nat := if 0 < p then p - 1 else 2 ^ (32 * cwc len .wide) - 1

/-- p into wide slot 9, one into 14 and `p − 1` into 15. -/
theorem pSetup_ok (h : In Ex base bytes len args s) (h3 : args 3 = BitVec.ofNat 32 len)
    (fit : (args 2).toNat + len ≤ 2 ^ 32) (rd : InRegions (s.rd ++ s.wr) (byteAddr (args 2)) len)
    (apart : Region.Disjoint ⟨byteAddr (args 2), len⟩ ⟨base, bytes⟩) :
    WP isa Impl.Ffdh.X86.pSetup s fun u =>
      In Ex base bytes len args u ∧ Frame (frameF base (s.gpr .esp) (fR len)) s.mem u.mem ∧
      Kept base len [9, 14, 15] [] s.mem u.mem ∧
      sv u.mem base len .wide 9 = argNum s.mem args 2 len ∧ sv u.mem base len .wide 14 = 1 ∧
      sv u.mem base len .wide 15 = pm1 len (argNum s.mem args 2 len) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  obtain f9 := slot_fit1 h (j := 9) (by decide)
  obtain f14 := slot_fit1 h (j := 14) (by decide)
  obtain f15 := slot_fit1 h (j := 15) (by decide)
  obtain c1 := cb1 len
  obtain w1 := cw1 len
  obtain lb := len_le_bc len
  have lo' := h.lower'
  unfold Impl.Ffdh.X86.pSetup
  refine WP.seq (WP.mono (load_ok h (one_ok .wide) f9 (p := 2) (l := 3) (L := len) (by decide) (by decide) h3
    (by omega_arith) (by omega_arith) fit rd apart) fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  rw [c1] at O₁
  rw [w1] at V₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (setSmall_ok h₁ (one_ok .wide) f14 (v := 1) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [c1] at O₂
  rw [w1] at V₂
  obtain h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.mono (chainSub_ok h₂ (one_ok .wide) f15 f9 f14 (apart1 len (by decide)) (apart1 len (by decide)))
    fun u ⟨O₃, _, ⟨c, _, V₃⟩, K₃⟩ => ?_
  rw [c1] at O₃
  rw [w1] at V₃
  obtain h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  obtain k₁ := kept_slot h (a := 9) O₁
  obtain k₂ := kept_slot h₁ (a := 14) O₂
  obtain k₃ := kept_slot h₂ (a := 15) O₃
  obtain e9 : sv u₂.mem base len .wide 9 = argNum s.mem args 2 len := (k₂.slot_eq).trans V₁
  have e14 : sv u₂.mem base len .wide 14 = 1 := V₂
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  obtain sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  refine ⟨h₃, ?_, ((k₁.mono).trans k₂.mono).trans k₃.mono, k₃.slot_eq.trans e9, k₃.slot_eq.trans e14, ?_,
    (K₁.mono (by decide)).trans ((K₂.mono (by decide)).trans (K₃.mono (by decide)))⟩
  · have bst : bc len .wide ≤ st len .wide := by have est : st len .wide = 2 * bc len .wide + 32 := rfl; omega_arith
    obtain F₁ := fR_of_outside h (sp := s.gpr .esp) O₁ (slot_inF (by decide) bst)
    obtain F₂ := fR_of_outside h (sp := s.gpr .esp) O₂ (slot_inF (by decide) bst)
    obtain F₃ := fR_of_outside h (sp := s.gpr .esp) O₃ (slot_inF (by decide) bst)
    exact (F₁.trans F₂).trans F₃
  · have lt := val32_lt u.mem base (lo len (.slot .wide 15)) (cwc len .wide)
    obtain lt9 : argNum s.mem args 2 len < 2 ^ (32 * cwc len .wide) := by
      rw [← e9]; exact val32_lt _ _ _ _
    change sv u.mem base len .wide 15 < _ at lt
    rw [show val32 u₂.mem base (lo len (.slot .wide 14)) (cwc len .wide) = 1 from e14,
      show val32 u₂.mem base (lo len (.slot .wide 9)) (cwc len .wide) = argNum s.mem args 2 len from e9] at V₃
    change sv u.mem base len .wide 15 + 1 = _ at V₃
    have := Nat.two_pow_pos (32 * cwc len .wide)
    unfold pm1
    split <;> (cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      at V₃ <;> omega_arith)

theorem pm1_of {len p : Nat} (h : 0 < p) : pm1 len p = p - 1 := by simp [pm1, h]

/-- Where the wide slots lie. -/
theorem lo_wide (len j : Nat) : lo len (.slot .wide j) = numBase + j * st len .wide := rfl

/-- A copy of the wide slot `j` (9 to 19) into the context's slot `d` (to 8). -/
theorem copyIn_ok (h : In Ex base bytes len args s) {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 19) (hd : d ≤ 8) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) s fun u =>
      Outside base (lo len (.slot .wide d)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide d = sv s.mem base len .wide j ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  obtain f := h.slot_fit .wide (j := 19) (by decide)
  have := hi_fit (len := len) hj9 hj
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain b := Nat.mul_le_mul_right (st len .wide) (show d + 1 ≤ 9 by omega_arith)
  rw [Nat.succ_mul] at b
  obtain ej := lo_wide len j
  obtain ed := lo_wide len d
  obtain e9 := lo_wide len 9
  obtain e20 := lo_wide len 20
  obtain e19 := lo_wide len 19
  refine WP.mono (copy_ok h (x := .slot .wide j) (d := .slot .wide d) (one_ok .wide) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inl (by omega_arith))) fun u ⟨O, V, K⟩ => ⟨?_, ?_, K⟩
  · rw [cb1] at O; exact O
  · rw [cw1] at V; exact V

/-- The context of p, in the wide slot 9: p in slot 0, one in 3, `R² mod p` in 4 and the inverse. -/
theorem ctxP_ok (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) {P : Nat}
    (hP : safeM (sv s.mem base len .wide 9) = P) :
    WP isa Impl.Ffdh.X86.ctxP s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧
      Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  obtain f0 := h.slot_fit .wide (j := 0) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  unfold Impl.Ffdh.X86.ctxP
  refine WP.seq (WP.mono (copyIn_ok h (j := 9) (d := 0) (by decide) (by decide) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  refine WP.mono (prepCall_ok h₁ (by rw [sp₁]; exact RF)) fun u ⟨C, one, R2, F, K⟩ => ?_
  rw [V₁, hP] at C R2
  rw [sp₁] at F
  obtain F₁ : Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u₁.mem :=
    frameF_of (stR_of_outside h (by decide) O₁ ⟨_, by simp, slot_in h .wide (j := 0) (by decide)⟩)
  obtain F₂ := frameF_widen F (prepR_in h₁ .wide 0)
  exact ⟨C, one, R2, F₁.trans F₂, (keptF_ops h F₁ RF).trans (keptF_ops h F₂ RF),
    (K₁.mono (by decide)).trans K⟩

/-- A prepared context keeps one in its slot 3 through an exponentiation. -/
theorem pwR_sv3 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameF base sp (pwR len .wide)) m m') (R : RoomF sp base bytes) :
    sv m' base len .wide 3 = sv m base len .wide 3 := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain T := h.table_fit .wide
  obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  obtain e20 := lo_wide len 20
  obtain e1 := lo_wide len 1
  obtain e3 := lo_wide len 3
  obtain e5 := lo_wide len 5
  obtain e6 := lo_wide len 6
  obtain e7 := lo_wide len 7
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine frameF_val32 F R nw (by omega_arith) ?_ (pwR_fit h .wide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [winOff] <;> omega_arith

/-- Slot 6 the wide slot `b` to the power of the wide slot `e`, modulo p (in the wide slot 9). -/
theorem powP_ok (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) {P b e : Nat}
    (hb9 : 9 ≤ b) (hb : b ≤ 19) (he9 : 9 ≤ e) (he : e ≤ 19) (hP : safeM (sv s.mem base len .wide 9) = P) :
    WP isa (Impl.Ffdh.X86.powP b e) s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide b ^ sv s.mem base len .wide e % P ∧
      sv u.mem base len .wide 3 = 1 ∧
      Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain e0 := lo_wide len 0
  obtain e3 := lo_wide len 3
  obtain e4 := lo_wide len 4
  obtain e5 := lo_wide len 5
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  unfold Impl.Ffdh.X86.powP
  refine WP.seq (WP.mono (ctxP_ok h RF hP) fun u₁ ⟨C₁, one₁, R₁, F₁, k₁, K₁⟩ => ?_)
  have h₁ := C₁.inp
  refine WP.seq (WP.mono (copyIn_ok h₁ (j := b) (d := 5) hb9 hb (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  obtain h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copyIn_ok h₂ (j := e) (d := 8) he9 he (by decide)) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  obtain sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  obtain sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  obtain G₂ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₁.mem u₂.mem :=
    stR_of_outside h (by decide) O₂ ⟨_, by simp, slot_in h .wide (j := 5) (by decide)⟩
  obtain G₃ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₂.mem u₃.mem :=
    stR_of_outside h (by decide) O₃ ⟨_, by simp, slot_in h .wide (j := 8) (by decide)⟩
  obtain C₃ : CtxOk Ex base bytes len args .wide P u₃ := by
    refine C₁.keepF (regs := [.eax, .ebx, .ecx, .edx, .ebp]) (K₂.trans K₃) (by decide) (by decide)
      (ws := [(lo len (.slot .wide 5), bc len .wide), (lo len (.slot .wide 8), bc len .wide)]) ?_ ?_ ?_
    · rw [sp₁]
      exact (frameR_of_outside O₂ (by omega_arith) (by simp)).trans
        (by rw [← sp₁]; exact frameR_of_outside O₃ (by omega_arith) (by simp))
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  obtain kb : sv u₁.mem base len .wide b = sv s.mem base len .wide b := k₁.slots b hb9 hb (by simp)
  obtain ke : sv u₂.mem base len .wide e = sv s.mem base len .wide e :=
    (slotKeep h₁ he (by omega_arith) O₂).trans (k₁.slots e he9 he (by simp))
  obtain B₃ : sv u₃.mem base len .wide 5 = sv s.mem base len .wide b := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, V₂, kb]
  obtain E₃ : sv u₃.mem base len .wide 8 = sv s.mem base len .wide e := by rw [V₃, ke]
  obtain one₃ : sv u₃.mem base len .wide 3 = 1 := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h₁ (by decide) (by decide) O₂, one₁]
  obtain R₃ : sv u₃.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h₁ (by decide) (by decide) O₂, R₁]
  refine WP.mono (winCall_ok C₃ (by rw [sp₃]; exact RF) one₃ R₃) fun u ⟨C, F, K, Y⟩ => ?_
  rw [B₃, E₃] at Y
  rw [sp₃] at F
  obtain G := frameF_widen F (pwR_in C₃.inp .wide 0)
  refine ⟨C, Y, ?_, ((F₁.trans (frameF_of G₂)).trans (frameF_of G₃)).trans G, ?_, ?_⟩
  · rw [pwR_sv3 C₃.inp F RF, one₃]
  · exact (((k₁.trans (kept_ops h G₂ h.room)).trans (kept_ops h G₃ h.room)).trans (keptF_ops h G RF))
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
  refine wp_storeS (h.scratch.ea (d := d) (by omega_arith)) (h.scratch.write (d := d) (n := 4) (by omega_arith)) fun u M =>
    WP.block_nil ?_
  obtain O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  refine ⟨h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith)), O, ?_, M.zf, M.keeps []⟩
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
  refine wp_logicS (.inl rfl) (readSrc_sc h.scratch (d := d) (by omega_arith)) fun u U => WP.block_nil ⟨?_, U.mem, U.keeps⟩
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
  obtain fa := slot_fit1 h (j := a) (by omega_arith)
  obtain f14 := slot_fit1 h (j := 14) (by decide)
  obtain f15 := slot_fit1 h (j := 15) (by decide)
  obtain ea := lo_wide len a
  obtain e14 := lo_wide len 14
  obtain e15 := lo_wide len 15
  have nb : numBase = 3336 := rfl
  have mo : maskOff = 12 := rfl
  obtain w1 := cw1 len
  unfold Impl.Ffdh.X86.rangeMask
  refine WP.seq (WP.mono (lessThan_ok h (a := .slot .wide 14) (b := .slot .wide a) (one_ok .wide) f14 fa)
    fun u₁ ⟨m₁, e₁, K₁⟩ => ?_)
  obtain h₁ := h.regs K₁ m₁
  refine WP.seq (WP.mono (storeMask_ok h₁ (d := maskOff) (by omega_arith) e₁) fun u₂ ⟨h₂, O₂, W₂, _, K₂⟩ => ?_)
  refine WP.seq (WP.mono (lessThan_ok h₂ (a := .slot .wide a) (b := .slot .wide 15) (one_ok .wide) fa f15)
    fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
  obtain h₃ := h₂.regs K₃ m₃
  have W₃ := W₂
  rw [← m₃] at W₃
  refine WP.mono (andMask_ok h₃ (d := maskOff) (by omega_arith) e₃ W₃) fun u ⟨E, M, K⟩ => ?_
  obtain ce := cb_eq (len := len) (one_ok .wide)
  obtain v : ∀ j, j ≤ 19 → val32 u₂.mem base (lo len (.slot .wide j)) (cw len (one .wide)) =
      sv s.mem base len .wide j := by
    intro j hj
    have := lo_wide len j
    have := slot_fit1 h (j := j) (by omega_arith)
    rw [O₂.val32 (.inr (by omega_arith)) (by omega_arith), m₁, w1]
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
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') : Frame (frameF base sp (fR len)) m m' :=
  fR_of_outside h O (slot_inF ha (by have est : st len .wide = 2 * bc len .wide + 32 := rfl; omega_arith))

/-- A header word written, within `fR`. -/
theorem wordF (h : In Ex base bytes len args s) {sp : BitVec 32} {d : Nat} (hd : d + 4 ≤ 32) {m m' : Mem}
    (O : Outside base d 4 m m') : Frame (frameF base sp (fR len)) m m' :=
  fR_of_outside h O (.inl hd)

/-- A header word written keeps the wide slots. -/
theorem kept_word (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) (h4 : d % 4 = 0) {m m' : Mem}
    (O : Outside base d 4 m m') : Kept base len [] [d] m m' := by
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  refine ⟨fun j hj9 hj _ => ?_, fun e he he' e4 hn => ?_⟩
  · have := slot_fit1 h (j := j) (by omega_arith)
    have := lo_wide len j
    obtain ce := cb_eq (len := len) (one_ok .wide)
    rw [cw1] at ce
    rw [cb1] at *
    exact O.val32 (.inr (by omega_arith)) (by omega_arith)
  · exact O.w32 (by simp only [List.mem_singleton] at hn; omega_arith) (by omega_arith)

/-- What a stage leaves: the status `r`, the changes within `fR`, and the registers. -/
def Res (base : Addr) (len : Nat) (s : State) (r : Nat) (t : State) : Prop :=
  t.gpr .eax = BitVec.ofNat 32 r ∧ Frame (frameF base (s.gpr .esp) (fR len)) s.mem t.mem ∧
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t

/-- A stage's result after one before it. -/
theorem Res.after {u t : State} {r : Nat} (R : Res base len u r t) {rs : List Reg} (K : Keeps rs s u)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide)
    (F : Frame (frameF base (s.gpr .esp) (fR len)) s.mem u.mem) : Res base len s r t := by
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
  frame : Frame (frameF base (s.gpr .esp) (fR len)) s.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u

/-- The room below `esp` through a stage, which keeps `esp`. -/
theorem Step.room {u : State} (S : Step Ex base bytes len args s u) (RF : RoomF (s.gpr .esp) base bytes) :
    RoomF (u.gpr .esp) base bytes := by
  rw [S.keeps.1 _ (by decide)]; exact RF

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
    (O.mono (Nat.zero_le _) (by omega_arith)), slotF h ha O, K.mono hrs⟩

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
    (O.mono (Nat.zero_le _) (by omega_arith)), wordF h hd O, K.mono hrs⟩

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

/-- A stage of the operations of a context, called. -/
theorem Step.opsF (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) {u : State}
    (F : Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u.mem) {rs : List Reg} (K : Keeps rs s u)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    Step Ex base bytes len args s u :=
  ⟨in_keepFF h K (by intro hm; have := hrs _ hm; simp at this) (by intro hm; have := hrs _ hm; simp at this) RF F
    (stR_fit h (by decide)), frameF_widen F fun p hp => by
      rcases stR_inF h p hp with e | e
      · exact ⟨(0, 32), by simp, by omega_using [], by omega_using [e]⟩
      · exact ⟨(48, CrtRt.need len - 48), by simp, by dsimp only; omega_using [e], by dsimp only; omega_using [e]⟩,
    K.mono hrs⟩

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

theorem Gate.congr {u : State} {C C' : Prop} (G : Gate u C) (h : C ↔ C') : Gate u C' :=
  let ⟨b, e, i⟩ := G
  ⟨b, e, i.trans h⟩

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

/-- A number of `L` bytes into the top of the wide context's slot `d`, kept by its context: the bytes'
value times `2^(8 (Bc − L))`. -/
theorem loadTopCtx_ok {M : Nat} (C : CtxOk Ex base bytes len args .wide M s) {d p l L : Nat} (hd1 : 1 ≤ d)
    (hd : d ≤ 8) (hp : p < 18) (hl : l < 18) (hlen : args l = BitVec.ofNat 32 L) (hL : 0 < L) (hLl : L ≤ len)
    (fit : (args p).toNat + L ≤ 2 ^ 32) (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) L)
    (apart : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨base, bytes⟩) :
    WP isa (loadTop (.slot .wide d) (one .wide) p l) s fun u =>
      CtxOk Ex base bytes len args .wide M u ∧
      sv u.mem base len .wide d =
        2 ^ (8 * (bc len .wide - L)) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L) ∧
      Outside base (lo len (.slot .wide d)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have h := C.inp
  have bl := h.bytes_lt
  obtain lb := len_le_bc len
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ed : lo len (.slot .wide d) = numBase + d * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  obtain d8 := Nat.mul_le_mul_right (st len .wide) hd
  obtain d1 := Nat.mul_le_mul_right (st len .wide) hd1
  refine WP.mono (loadTop_ok h (one_ok .wide) (slot_fit1 h (j := d) (by omega_arith)) (p := p) (l := l) (L := L) hp hl hlen
    hL (by rw [cb1]; omega_arith) fit rd apart) fun u ⟨V, O, K⟩ => ?_
  rw [cb1] at O V
  rw [cw1] at V
  exact ⟨C.keepF K (by decide) (by decide) (ws := [(lo len (.slot .wide d), bc len .wide)])
      (frameR_of_outside O (by omega_arith) (by simp))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega_arith)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega_arith), V, O, K⟩

/-- The exponent's top `2 L` windows, of a number of `L` bytes at the top of `Bc`: the number. -/
theorem top_windows {E L B : Nat} (hL : L ≤ B) :
    2 ^ (8 * (B - L)) * E * 16 ^ (2 * L) / 2 ^ (8 * B) = E := by
  rw [show (16 : Nat) ^ (2 * L) = 2 ^ (8 * L) by rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega_arith,
    Nat.mul_comm (2 ^ _) E, Nat.mul_assoc, ← Nat.pow_add, show 8 * (B - L) + 8 * L = 8 * B by omega_arith]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

/-! ## The context of a public modulus

`powerTwoPub` is `powerTwo` (`powerTwoPub_ok`): where the top word of the modulus is not zero, the modulus,
which is odd, is above `2^(8 B − 32)`, and `32 + B / 8` doublings of that are `2^(8 B + B / 8) mod M`
(`seedTwo_ok`). So `preparePub` leaves what `prepare .wide` does (`preparePub_ok`), and so do its call
and `ctxPub` (`prepPubCall_ok`, `ctxPub_ok`). -/

/-- The top word of the wide slot 0, the modulus. -/
abbrev topW (m : Mem) (base : Addr) (len : Nat) : Nat := w32 m base (numBase + (bc len .wide - 4))

/-- The top word of a number of the working space is its high digit. -/
theorem topW_eq (hl : 64 ≤ len) (m : Mem) :
    topW m base len = sv m base len .wide 0 / 2 ^ (32 * (cwc len .wide - 1)) := by
  obtain g := bc_ge hl .wide
  obtain bw := bc_eq_cwc len .wide
  obtain ⟨k, ek⟩ : ∃ k, cwc len .wide = k + 1 := ⟨cwc len .wide - 1, by omega_arith⟩
  obtain z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  obtain e0k : numBase + (bc len .wide - 4) = numBase + 4 * k := by omega_arith
  show w32 m base (numBase + (bc len .wide - 4)) = val32 m base (lo len (.slot .wide 0)) (cwc len .wide) / _
  rw [e0k, z0, ek, Nat.add_sub_cancel, val32_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]

theorem beq_zero_toNat (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have n : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [decide_eq_false n]; exact beq_eq_false_iff_ne.mpr h

section
open VG.Proof.Mont.X86.Rt

theorem topPtr_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 8)
    (kk : ∀ u, Keeps [.eax, .edx] s u → u.mem = s.mem →
      PtrAt u base .eax (lo len (.slot .wide j) + (bc len .wide - 4)) → WP isa (.block is) u Q) :
    WP isa (.block (Impl.Ffdh.X86.topPtr j ++ is)) s Q := by
  have bl := h.bytes_lt
  obtain f := h.slot_fit .wide (j := j) (by omega_arith)
  obtain g := bc_ge h.lower' .wide
  obtain hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e4 : (4 : BitVec 32).toNat = 4 := rfl
  unfold Impl.Ffdh.X86.topPtr
  simp only [List.append_assoc]
  refine ptrTo_ok (r := .eax) (t := .edx) (x := .slot .wide j) (by decide) (by decide) h.edi h.width h.upper'
    (by omega_arith) fun u₁ K₁ m₁ p₁ => ?_
  obtain h₁ := h.regs K₁ m₁
  refine cntTo_ok (r := .edx) (n := one .wide) h₁.width h.upper' (one_ok .wide).extra fun u₂ K₂ m₂ c₂ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_addS rfl fun u₃ a₃ _ => wp_subS rfl fun u₄ a₄ _ => ?_
  obtain p₃ : PtrAt u₃ base .eax (lo len (.slot .wide j) + bc len .wide) := by
    rw [PtrAt, a₃.gpr, K₂.1 _ (by decide), c₂, cb1, ptr_add p₁, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := bc len .wide) (by omega_arith)]
  obtain p₄ : PtrAt u₄ base .eax (lo len (.slot .wide j) + (bc len .wide - 4)) := by
    rw [PtrAt, a₄.gpr, ptr_sub p₃ 4 (by rw [e4]; omega_arith), e4]
    congr 2; omega_arith
  exact kk u₄ ((K₁.trans (K₂.mono (by decide))).trans ((a₃.keeps.mono (by decide)).trans (a₄.keeps.mono (by decide))))
    (by rw [a₄.mem, a₃.mem, m₂, m₁]) p₄

/-- `topTest`: ZF tells whether the top word of the modulus is zero. -/
theorem topTest_ok (h : In Ex base bytes len args s) :
    WP isa Impl.Ffdh.X86.topTest s fun u => u.mem = s.mem ∧ Keeps [.eax, .edx] s u ∧
      isa.eval .e u = some (decide (topW s.mem base len = 0)) := by
  have bl := h.bytes_lt
  obtain f := h.slot_fit .wide (j := 0) (by decide)
  obtain g := bc_ge h.lower' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  unfold Impl.Ffdh.X86.topTest
  refine topPtr_ok h (j := 0) (by decide) fun u K m p => ?_
  refine wp_movS (readSrc_ptr (h.ws.of_keeps K) p (d := 0) (by omega_arith)) fun u₁ a₁ _ => ?_
  refine wp_testS rfl fun u₂ T z => WP.block_nil ⟨by rw [T.mem, a₁.mem, m], ?_, ?_⟩
  · exact K.trans ((a₁.keeps.mono (by decide)).trans (T.keeps [.eax, .edx]))
  · show u₂.zf = _
    rw [z, BitVec.and_self, a₁.gpr, beq_zero_toNat, m, Nat.add_zero, z0]

/-- `seedTwo`: `2^(8 B − 32)`, below an odd modulus whose top word is not zero, doubled `32 + B / 8` times. -/
theorem seedTwo_ok (h : In Ex base bytes len args s) (hodd : sv s.mem base len .wide 0 % 2 = 1)
    (ht : topW s.mem base len ≠ 0) :
    WP isa Impl.Ffdh.X86.seedTwo s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len .wide)) s.mem u.mem ∧
      sv u.mem base len .wide 4 = 2 ^ twoExp len .wide % sv s.mem base len .wide 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  obtain g := bc_ge h.lower' .wide
  obtain hb := bc_le h.upper' .wide
  obtain bw := bc_eq_cwc len .wide
  obtain d8 := bc_dvd len .wide
  obtain s01 : lo len (.slot .wide 0) + st len .wide ≤ lo len (.slot .wide 1) := sl_le (len := len) .wide (by decide)
  obtain s14 : lo len (.slot .wide 1) + st len .wide ≤ lo len (.slot .wide 4) := sl_le (len := len) .wide (by decide)
  obtain s48 : lo len (.slot .wide 4) + st len .wide ≤ lo len (.slot .wide 8) := sl_le (len := len) .wide (by decide)
  obtain z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e32 : (32 : BitVec 32).toNat = 32 := rfl
  obtain fit : ∀ p ∈ powR len .wide, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  obtain ⟨k, ek⟩ : ∃ k, cwc len .wide = k + 1 := ⟨cwc len .wide - 1, by omega_arith⟩
  obtain e4k : lo len (.slot .wide 4) + (bc len .wide - 4) = lo len (.slot .wide 4) + 4 * k := by omega_arith
  obtain e0k : numBase + (bc len .wide - 4) = numBase + 4 * k := by omega_arith
  -- The modulus is above the seed.
  let M := sv s.mem base len .wide 0
  obtain seedLt : 2 ^ (32 * k) < M := by
    have top : 0 < w32 s.mem base (numBase + 4 * k) := by
      have := ht; rw [topW, e0k] at this; exact Nat.pos_of_ne_zero this
    have ge : 2 ^ (32 * k) ≤ M := by
      show _ ≤ val32 s.mem base (lo len (.slot .wide 0)) (cwc len .wide)
      rw [ek, val32_succ, z0]
      exact Nat.le_trans (Nat.le_mul_of_pos_right _ top) (Nat.le_add_left _ _)
    have ev : 2 ^ (32 * k) % 2 = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, 32 * k = j + 1 := ⟨32 * k - 1, by omega_arith⟩
      rw [hj, Nat.pow_succ, Nat.mul_mod_left]
    have od : M % 2 = 1 := hodd
    generalize 2 ^ (32 * k) = P at ge ev ⊢
    omega_using [ge, ev, od]
  unfold Impl.Ffdh.X86.seedTwo
  refine WP.seq (WP.mono (zero_ok (x := .slot .wide 4) h (one_ok .wide) (by rw [cb1]; omega_arith))
    fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  simp only [cb1, cw1] at O₀ V₀
  obtain h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega_arith))
  simp only [List.append_assoc]
  refine WP.seq (topPtr_ok h₀ (j := 4) (by decide) fun u₁ K₁ m₁ p₁ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun u₂ a₂ _ => ?_
  obtain K₂ : Keeps [.eax, .ecx, .edx] u₀ u₂ := (K₁.mono (by decide)).trans (a₂.keeps.mono (by decide))
  obtain ws₂ := h₀.ws.of_keeps K₂
  obtain p₂ : PtrAt u₂ base .eax (lo len (.slot .wide 4) + (bc len .wide - 4)) := by
    rw [PtrAt, a₂.other _ (by decide)]; exact p₁
  refine wp_storeS (ea_ptr ws₂ p₂ (d := 0) (by omega_arith))
    (ws_write ws₂ (y := lo len (.slot .wide 4) + (bc len .wide - 4) + 0) (n := 4) (by omega_arith)) fun u₃ m₃ => ?_
  obtain K₃ : Keeps [.eax, .ecx, .edx] u₀ u₃ := K₂.trans (m₃.keeps _)
  obtain mem₃ : u₃.mem = u₀.mem.writeW (off base (lo len (.slot .wide 4) + 4 * k)) 1 := by
    rw [m₃.mem, a₂.gpr, a₂.mem, m₁, Nat.add_zero, e4k]
  obtain W₃ : Outside base (lo len (.slot .wide 4) + 4 * k) 4 u₀.mem u₃.mem := by
    rw [mem₃]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain h₃ := h₀.keep K₃ (by decide) (by decide) (W₃.mono (Nat.zero_le _) (by omega_arith))
  obtain V₃ : sv u₃.mem base len .wide 4 = 2 ^ (32 * k) := by
    obtain lowk : val32 u₃.mem base (lo len (.slot .wide 4)) k = val32 u₀.mem base (lo len (.slot .wide 4)) k :=
      W₃.val32 (.inl (Nat.le_refl _)) (by omega_arith)
    have V' := V₀
    rw [ek, val32_succ] at V'
    simp only [sv]
    rw [ek, val32_succ, lowk, (Nat.add_eq_zero_iff.mp V').1, Nat.zero_add, mem₃, w32_write_self,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
  -- The count.
  refine widthC_ok (k := 0) (c := .wide) (r := .esi) h₃.width h.upper' fun u₄ K₄ m₄ e₄ => ?_
  refine wp_shr (by decide) fun u₅ a₅ _ => wp_addS rfl fun u₆ a₆ _ => WP.block_nil ?_
  obtain K₆ : Keeps [.esi] u₃ u₆ := (K₄.trans a₅.keeps).trans a₆.keeps
  obtain m₆ : u₆.mem = u₃.mem := by rw [a₆.mem, a₅.mem, m₄]
  obtain esi₆ : (u₆.gpr .esi).toNat = 32 + bc len .wide / 8 := by
    rw [a₆.gpr, a₅.gpr, e₄]
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, e32]
    rw [Nat.mod_eq_of_lt (a := bc len .wide) (by omega_arith)]
    omega_arith
  obtain h₆ := h₃.regs (K₆.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₃ u₆) m₆
  obtain Ks₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₆ :=
    ((K₀.mono (by decide)).trans (K₃.mono (by decide))).trans (K₆.mono (by decide))
  obtain sp₆ : u₆.gpr .esp = s.gpr .esp := Ks₆.1 _ (by decide)
  obtain O₆ : Outside base (lo len (.slot .wide 4)) (bc len .wide) s.mem u₆.mem := by
    rw [m₆]; exact O₀.trans (W₃.mono (by omega_arith) (by omega_arith))
  obtain M₆ : sv u₆.mem base len .wide 0 = M := O₆.val32 (by omega_arith) (by omega_arith)
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₆ t ∧
      Frame (frameR base (s.gpr .esp) (powR len .wide)) u₆.mem t.mem ∧
      sv t.mem base len .wide 4 = 2 ^ (32 * k + j) % M ∧ (t.gpr .esi).toNat = 32 + bc len .wide / 8 - j
  obtain I₀ : I 0 u₆ := ⟨Keeps.refl _ _, Frame.refl _ _, by rw [m₆, V₃]; exact (Nat.mod_eq_of_lt seedLt).symm,
    by rw [esi₆]; rfl⟩
  refine WP.mono (PublicRt.countLoop (N := 32 + bc len .wide / 8) (by omega_arith) I ?_ I₀)
    fun t ⟨Kt, Ft, Vt, _⟩ => ?_
  · rintro j t hj ⟨Kt, Ft, Vt, esit⟩
    obtain ht := h₆.keepF Kt (by decide) (by decide) (by rw [sp₆]; exact Ft) fit
    obtain Mt : sv t.mem base len .wide 0 = M := by
      have := frameR_val32 (d := lo len (.slot .wide 0)) (k := cwc len .wide) Ft h.room nw' (by omega_arith) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) fit
      simp only [sv]; rw [this]; exact M₆
    obtain hM' : 0 < M := by omega_using [seedLt]
    refine WP.mono (doubleStep_ok ht .wide (by rw [Vt, Mt]; exact Nat.mod_lt _ hM'))
      fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
    obtain ⟨c₁, c₂⟩ := PublicRt.count1_zf esit hj
    obtain spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₆]
    refine ⟨⟨Kt.trans Ku, Ft.trans (by rw [← spt]; exact Fu), ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
    show sv u.mem base len .wide 4 = 2 ^ (32 * k + j + 1) % M
    rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]
  · obtain e : 32 * k + (32 + bc len .wide / 8) = twoExp len .wide := by simp only [twoExp]; omega_arith
    exact ⟨(frameR_of_outside O₆ (by omega_arith) (by simp [powR])).trans Ft, by rw [Vt, e], Ks₆.trans Kt⟩

/-- `powerTwoPub` leaves what `powerTwo .wide` does, for an odd modulus. -/
theorem powerTwoPub_ok (h : In Ex base bytes len args s) (hM : 1 < sv s.mem base len .wide 0)
    (hodd : sv s.mem base len .wide 0 % 2 = 1) :
    WP isa Impl.Ffdh.X86.powerTwoPub s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len .wide)) s.mem u.mem ∧
      sv u.mem base len .wide 4 = 2 ^ twoExp len .wide % sv s.mem base len .wide 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  unfold Impl.Ffdh.X86.powerTwoPub
  refine WP.seq (WP.mono (topTest_ok h) fun u₁ ⟨m₁, K₁, z₁⟩ => ?_)
  obtain h₁ := h.regs K₁ m₁
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  refine WP.gate (Gate.of_eval z₁ decide_eq_true_iff) (fun _ => ?_) fun t1 => ?_
  · refine WP.mono (powerTwo_ok h₁ .wide (by rw [m₁]; exact hM)) fun u ⟨F, V, K⟩ => ?_
    rw [m₁, sp₁] at F
    rw [m₁] at V
    exact ⟨F, V, (K₁.mono (by decide)).trans K⟩
  · refine WP.mono (seedTwo_ok h₁ (by rw [m₁]; exact hodd) (by rw [m₁]; exact t1)) fun u ⟨F, V, K⟩ => ?_
    rw [m₁, sp₁] at F
    rw [m₁] at V
    exact ⟨F, V, (K₁.mono (by decide)).trans K⟩

/-- `preparePub` leaves what `prepare .wide` does (`prepCtx_ok`). -/
theorem preparePub_ok (h : In Ex base bytes len args s) :
    WP isa Impl.Ffdh.X86.preparePub s fun u =>
      CtxOk Ex base bytes len args .wide (safeM (sv s.mem base len .wide 0)) u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % safeM (sv s.mem base len .wide 0) ∧
      Frame (frameR base (s.gpr .esp) (prepR len .wide)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw := h.scratch.nowrap
  have fit := prepR_fit2 h .wide
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  obtain z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  obtain s01 : lo len (.slot .wide 0) + st len .wide ≤ lo len (.slot .wide 1) := sl_le (len := len) .wide (by decide)
  obtain s13 : lo len (.slot .wide 1) + st len .wide ≤ lo len (.slot .wide 3) := sl_le (len := len) .wide (by decide)
  obtain s12 : lo len (.slot .wide 1) + st len .wide ≤ lo len (.slot .wide 2) := sl_le (len := len) .wide (by decide)
  obtain s23 : lo len (.slot .wide 2) + st len .wide ≤ lo len (.slot .wide 3) := sl_le (len := len) .wide (by decide)
  obtain s34 : lo len (.slot .wide 3) + st len .wide ≤ lo len (.slot .wide 4) := sl_le (len := len) .wide (by decide)
  obtain s48 : lo len (.slot .wide 4) + st len .wide ≤ lo len (.slot .wide 8) := sl_le (len := len) .wide (by decide)
  have d8 := bc_dvd len .wide
  obtain fitW : ∀ p ∈ powR len .wide, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  unfold Impl.Ffdh.X86.preparePub
  refine WP.seq (WP.mono (prepBasePre_ok h .wide) fun u₁ ⟨h₁, F₁, M₁, one₁, I₁, K₁⟩ => ?_)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  refine WP.seq (WP.mono (powerTwoPub_ok h₁ (by rw [M₁]; exact safeM_gt _) (by rw [M₁]; exact safeM_odd _))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [sp₁] at F₂
  rw [M₁] at V₂
  obtain keepVal : ∀ d, d + 4 * cwc len .wide ≤ bytes → (d + 4 * cwc len .wide ≤ lo len (.slot .wide 1) ∨
      lo len (.slot .wide 1) + (bc len .wide + 4) ≤ d) →
      (d + 4 * cwc len .wide ≤ lo len (.slot .wide 4) ∨ lo len (.slot .wide 4) + bc len .wide ≤ d) →
      val32 u₂.mem base d (cwc len .wide) = val32 u₁.mem base d (cwc len .wide) := fun d hd h1 h2 =>
    frameR_val32 F₂ h.room nw hd (by
      intro p hp
      simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) fitW
  obtain M₂ : sv u₂.mem base len .wide 0 = safeM (sv s.mem base len .wide 0) :=
    (keepVal _ (by omega_arith) (by omega_arith) (by omega_arith)).trans M₁
  obtain one₂ : sv u₂.mem base len .wide 3 = 1 :=
    (keepVal _ (by omega_arith) (by omega_arith) (by omega_arith)).trans one₁
  obtain W₂ : w32 u₂.mem base invOff = w32 u₁.mem base invOff := by
    rw [← w32_val32_one, ← w32_val32_one]
    exact frameR_val32 F₂ h.room nw (by simp only [invOff]; omega_arith) (by
      intro p hp
      simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> simp only [invOff] <;> omega_arith) fitW
  obtain F : Frame (frameR base (s.gpr .esp) (baseR len .wide)) s.mem u₂.mem := F₁.trans (frameR_mono F₂ (by simp))
  obtain K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := K₁.trans K₂
  have C : CtxOk Ex base bytes len args .wide (safeM (sv s.mem base len .wide 0)) u₂ :=
    ⟨h.keepF K (by decide) (by decide) F fit.2, M₂, safeM_gt _, safeM_odd _, by rw [W₂]; exact I₁⟩
  have spu : u₂.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.mono (squares4_ok C (d := bc len .wide / 8) V₂) fun t ⟨Ct, Kt, Ft, Vt⟩ => ⟨Ct, ?_, ?_, ?_, ?_⟩
  · have v := frameR_val32 (d := lo len (.slot .wide 3)) (k := cwc len .wide) Ft C.inp.room nw (by omega_arith) (by
      intro p hp
      simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) (fun p hp => fit.1 p (by
        simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp))
    simp only [sv] at one₂ ⊢
    rw [v, one₂]
  · rw [Vt]; congr 2; omega_arith
  · have W : Frame (frameR base (s.gpr .esp) (prepR len .wide)) s.mem u₂.mem := frameR_widen F fun p hp => by
      simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨(invOff, 4), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot .wide 0), bc len .wide), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot .wide 1), 3 * bc len .wide + 56), by simp, Nat.le_refl _, by dsimp only; omega_using []⟩
      · exact ⟨(lo len (.slot .wide 3), bc len .wide), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot .wide 4), bc len .wide), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(lo len (.slot .wide 7), bc len .wide), by simp, Nat.le_refl _, Nat.le_refl _⟩
    refine W.trans ?_
    rw [← spu]
    exact frameR_mono Ft fun p hp => by
      simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp
  · exact K.trans (Kt.mono (by decide))

/-- A prepared context's memory, modulo `M`. -/
abbrev PrepMem (base : Addr) (len M : Nat) (m : Mem) : Prop :=
  sv m base len .wide 0 = M ∧ (M * w32 m base invOff + 1) % 2 ^ 32 = 0 ∧ sv m base len .wide 3 = 1 ∧
    sv m base len .wide 4 = 2 ^ (16 * bc len .wide) % M

/-- `preparePub`, called: what `prepCall` leaves. -/
theorem prepPubCall_ok (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) :
    WP isa Impl.Ffdh.X86.prepPubCall s (PrepPost Ex base bytes len args s) := by
  unfold Impl.Ffdh.X86.prepPubCall
  refine WP.mono (argCall_ok prepPubBody_noSp h RF (prepR_fit2 h .wide).1
    (R := PrepMem base len (safeM (sv s.mem base len .wide 0))) (fun W F hr => ?_) fun u hu Fs => ?_)
    fun w ⟨I, F, K, a, b, c, d⟩ => ⟨⟨I, a, safeM_gt _, safeM_odd _, b⟩, c, d, F, K⟩
  · obtain ⟨a, b, c, d⟩ := W
    obtain Fs : Frame (frameF base (s.gpr .esp) []) _ _ := frameF_of_sub F hr
    exact ⟨(frameF_sv h RF Fs (by decide)).trans a, by rw [frameF_inv h RF Fs]; exact b,
      (frameF_sv h RF Fs (by decide)).trans c, (frameF_sv h RF Fs (by decide)).trans d⟩
  · refine WP.mono (preparePub_ok hu) fun v ⟨C, one, R2, F, K⟩ => ⟨F, K, ?_⟩
    rw [frameF_sv h RF Fs (by decide)] at C R2
    exact ⟨C.mod, C.inv, one, R2⟩

/-- `ctxPub` leaves what `ctxP` does (`ctxP_ok`). -/
theorem ctxPub_ok (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes) {P : Nat}
    (hP : safeM (sv s.mem base len .wide 9) = P) :
    WP isa Impl.Ffdh.X86.ctxPub s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧
      Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  obtain f0 := h.slot_fit .wide (j := 0) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  unfold Impl.Ffdh.X86.ctxPub
  refine WP.seq (WP.mono (copyIn_ok h (j := 9) (d := 0) (by decide) (by decide) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  refine WP.mono (prepPubCall_ok h₁ (by rw [sp₁]; exact RF)) fun u ⟨C, one, R2, F, K⟩ => ?_
  rw [V₁, hP] at C R2
  rw [sp₁] at F
  obtain F₁ : Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u₁.mem :=
    frameF_of (stR_of_outside h (by decide) O₁ ⟨_, by simp, slot_in h .wide (j := 0) (by decide)⟩)
  obtain F₂ := frameF_widen F (prepR_in h₁ .wide 0)
  exact ⟨C, one, R2, F₁.trans F₂, (keptF_ops h F₁ RF).trans (keptF_ops h F₂ RF),
    (K₁.mono (by decide)).trans K⟩

end

end VG.Proof.Ffdh.X86
