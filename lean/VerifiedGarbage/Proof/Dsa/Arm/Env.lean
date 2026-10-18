module

public import VerifiedGarbage.Proof.Dsa.Arm.Install
public import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on 32-bit ARM: the caller's buffers, and the exit

From the entry until a body starts, memory has changed only inside the
working space, whose header still holds the fields and the saved registers
(`Env`). The operands of the bodies are then slices of the caller's buffers
(`input_of`), and the exit restores the saved registers (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd)

/-- Memory changed only inside the working space, whose header keeps the fields. -/
structure Env (s₀ : State) (base : Addr) (size : Nat) (fields : Fields) (t : State) : Prop where
  ws : Ws t base size
  fields : ∀ f ∈ fields, t.mem.readW (off base f.1) 32 = f.2
  saved : ∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0)
  mem : Outside base 0 size s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp

/-- The header's fields lie in `[64, 112)`. -/
abbrev FieldsOk (fields : Fields) : Prop := ∀ f ∈ fields, 64 ≤ f.1 ∧ f.1 + 4 ≤ 112

theorem Env.of_installed {s₀ u : State} {base : Addr} {size : Nat} {fields : Fields}
    (I : Installed s₀ base size fields u) (hz : 164 ≤ size) : Env s₀ base size fields u :=
  ⟨I.ws, I.fields, I.saved, I.mem.mono (Nat.zero_le _) (by omega), I.rest.rd, I.rest.wr, I.rest.sp⟩

/-- A step that changes registers but `r12`, and memory in ranges of the working space
apart from the fields and the saved registers. -/
theorem Env.keep {s₀ t t' : State} {base : Addr} {size : Nat} {fields : Fields} {ws : List Reg}
    {rs : List (Nat × Nat)} (E : Env s₀ base size fields t) (hf : FieldsOk fields)
    (R : Rest ws t t') (hr : .r12 ∉ ws) (O : Outs base rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ size ∧ (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128))) :
    Env s₀ base size fields t' := by
  have nw := E.ws.nowrap
  refine ⟨E.ws.of_rest R hr, fun f h => ?_, fun i hi => ?_, fun x hx => ?_, R.rd.trans E.rd, R.wr.trans E.wr,
    R.sp.trans E.sp⟩
  · have := hf f h
    rw [← E.fields f h]
    exact hdr_keep (s := t) (t := t') O (fun r hr' => by have := hrs r hr'; omega) (by omega)
  · rw [← E.saved i hi]
    exact hdr_keep (s := t) (t := t') O (fun r hr' => by have := hrs r hr'; omega) (by omega)
  · rw [← E.mem x hx]
    exact O x fun r hr' => .inr (by have := hrs r hr'; omega)

theorem Env.of_mem {s₀ t t' : State} {base : Addr} {size : Nat} {fields : Fields} {ws : List Reg}
    (E : Env s₀ base size fields t) (R : Rest ws t t') (hr : .r12 ∉ ws) (M : t'.mem = t.mem) :
    Env s₀ base size fields t' :=
  ⟨E.ws.of_rest R hr, fun f h => by rw [M]; exact E.fields f h, fun i hi => by rw [M]; exact E.saved i hi,
    by rw [M]; exact E.mem, R.rd.trans E.rd, R.wr.trans E.wr, R.sp.trans E.sp⟩

theorem Env.field {s₀ t : State} {base : Addr} {size : Nat} {fields : Fields} (E : Env s₀ base size fields t)
    {d : Nat} {v : BitVec 32} (h : (d, v) ∈ fields) : hdr base t d = v :=
  E.fields (d, v) h

/-- A byte of the working space is not one of a range apart from it. -/
theorem ofs_apart {base P x : Addr} {L size : Nat} (hd : Region.Disjoint ⟨P, L⟩ ⟨base, size⟩)
    (hx : ofs base x < size) : L ≤ ofs P x := by
  by_contra h
  exact hd x (by simp only [Region.Contains, ofs] at h ⊢; omega) (by simp only [Region.Contains, ofs] at hx ⊢; omega)

/-- The saved registers through a body. -/
theorem Env.saved_body {s₀ t t' : State} {base P : Addr} {size L : Nat} {fields : Fields}
    (E : Env s₀ base size fields t) (B : Body base P L t t') (hd : Region.Disjoint ⟨P, L⟩ ⟨base, size⟩)
    (hz : 164 ≤ size) :
    ∀ i < 9, t'.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0) := by
  have nw := E.ws.nowrap
  intro i hi
  rw [← E.saved i hi]
  refine Mem.readW_congr fun j hj => B.mem _ (fun r hr => ?_) (ofs_apart hd ?_)
  · simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [ofs_off base (by omega)]
    rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega
  · rw [ofs_off base (by omega)]
    omega

/-- The saved registers past a range of the caller. -/
theorem Env.saved_outside {s₀ t t' : State} {base P : Addr} {size L : Nat} {fields : Fields}
    (E : Env s₀ base size fields t) (O : Outside P 0 L t.mem t'.mem) (hd : Region.Disjoint ⟨P, L⟩ ⟨base, size⟩)
    (hz : 164 ≤ size) :
    ∀ i < 9, t'.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0) := by
  have nw := E.ws.nowrap
  intro i hi
  rw [← E.saved i hi]
  refine Mem.readW_congr fun j hj => O _ (.inr ?_)
  have := ofs_apart hd (x := off base (128 + 4 * i) + BitVec.ofNat 64 j) (by rw [ofs_off base (by omega)]; omega)
  omega

/-! ## The operands -/

/-- An operand that is a slice of one of the caller's buffers. -/
theorem input_of {s₀ t : State} {base : Addr} {size : Nat} {fields : Fields} (E : Env s₀ base size fields t)
    {p : Impl.Dsa.Layout.Pointer} (hp : PtrOk p) {P₀ : BitVec 32} {L₀ o len : Nat}
    (hv : pointerValue base t p = P₀ + BitVec.ofNat 32 o)
    (hr : ⟨State.addr P₀, L₀⟩ ∈ s₀.rd ++ s₀.wr) (hfit : P₀.toNat + L₀ ≤ 2 ^ 32) (ho : o + len ≤ L₀) (hl : 0 < len ∨ o = 0)
    (hd : Region.Disjoint ⟨State.addr P₀, L₀⟩ ⟨base, size⟩) (hz : 4960 ≤ size) :
    Input t base size p len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem (State.addr P₀ + BitVec.ofNat 64 o) len)) := by
  have nw := E.ws.nowrap
  have P₀lt := P₀.isLt
  have A : State.addr (pointerValue base t p) = State.addr P₀ + BitVec.ofNat 64 o := by
    rw [hv, VG.Arm.addr_add (by omega)]
  have D : Region.Disjoint ⟨State.addr (pointerValue base t p), len⟩ ⟨base, size⟩ := by
    rw [A]; exact hd.sub_left (Offset.sub_base _ ho)
  refine ⟨⟨hp, ?_, fun e k hek => ?_, D.sub_right (Region.sub_prefix hz)⟩, D, ?_⟩
  · rw [hv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [A, Offset.add_add, E.rd, E.wr]
    exact ⟨_, hr, Offset.contains_base _ (by omega) (by omega)⟩
  · simp only [operand, A]
    rw [bytes_keep E.mem (by rw [← A]; exact D) (by omega) (by omega)]

/-! ## The exit -/

theorem restore_ok {t : State} {base : Addr} {size : Nat} (hs : Ws t base size) (hz : 164 ≤ size)
    {v : Nat → BitVec 32} (hv : ∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = v i) :
    WP isa (.block Entry.restore) t fun u =>
      (∀ i < 9, u.gpr (Entry.savedRegs.getD i .r0) = v i) ∧ Rest Entry.savedRegs t u ∧ u.mem = t.mem := by
  have nw := hs.nowrap
  show WP isa (.block [.ldr .r4 .r12 128, .ldr .r5 .r12 132, .ldr .r6 .r12 136, .ldr .r7 .r12 140,
    .ldr .r8 .r12 144, .ldr .r9 .r12 148, .ldr .r10 .r12 152, .ldr .r11 .r12 156, .ldr .lr .r12 160]) t _
  refine wp_ldr12 hs (by decide) (by omega) fun u₁ v₁ => ?_
  have w₁ := hs.of_upd v₁ (by decide)
  refine wp_ldr12 w₁ (by decide) (by omega) fun u₂ v₂ => ?_
  have w₂ := w₁.of_upd v₂ (by decide)
  refine wp_ldr12 w₂ (by decide) (by omega) fun u₃ v₃ => ?_
  have w₃ := w₂.of_upd v₃ (by decide)
  refine wp_ldr12 w₃ (by decide) (by omega) fun u₄ v₄ => ?_
  have w₄ := w₃.of_upd v₄ (by decide)
  refine wp_ldr12 w₄ (by decide) (by omega) fun u₅ v₅ => ?_
  have w₅ := w₄.of_upd v₅ (by decide)
  refine wp_ldr12 w₅ (by decide) (by omega) fun u₆ v₆ => ?_
  have w₆ := w₅.of_upd v₆ (by decide)
  refine wp_ldr12 w₆ (by decide) (by omega) fun u₇ v₇ => ?_
  have w₇ := w₆.of_upd v₇ (by decide)
  refine wp_ldr12 w₇ (by decide) (by omega) fun u₈ v₈ => ?_
  have w₈ := w₇.of_upd v₈ (by decide)
  refine wp_ldr12 w₈ (by decide) (by omega) fun u v₉ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have m : ∀ d, hdr base u₈ d = hdr base t d := fun d => by
      simp only [hdr, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m' : ∀ d, hdr base u₇ d = hdr base t d := fun d => by
      simp only [hdr, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m6 : ∀ d, hdr base u₆ d = hdr base t d := fun d => by
      simp only [hdr, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m5 : ∀ d, hdr base u₅ d = hdr base t d := fun d => by
      simp only [hdr, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m4 : ∀ d, hdr base u₄ d = hdr base t d := fun d => by simp only [hdr, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m3 : ∀ d, hdr base u₃ d = hdr base t d := fun d => by simp only [hdr, v₃.mem, v₂.mem, v₁.mem]
    have m2 : ∀ d, hdr base u₂ d = hdr base t d := fun d => by simp only [hdr, v₂.mem, v₁.mem]
    have m1 : ∀ d, hdr base u₁ d = hdr base t d := fun d => by simp only [hdr, v₁.mem]
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.gpr]
      exact hv 0 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other, v₂.gpr, m1]
      exact hv 1 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.gpr, m2]
      exact hv 2 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.gpr, m3]
      exact hv 3 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.gpr, m4]
      exact hv 4 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.gpr, m5]
      exact hv 5 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.gpr, m6]
      exact hv 6 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.gpr, m']
      exact hv 7 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.gpr, m]
      exact hv 8 (by decide)
  · exact (((((((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide))).trans
      (v₄.rest (by decide))).trans (v₅.rest (by decide))).trans (v₆.rest (by decide))).trans
      (v₇.rest (by decide))).trans (v₈.rest (by decide))).trans (v₉.rest (by decide)))
  · rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]

/-- The registers the ABI preserves, from their saved words. -/
theorem abi_of_restored {s u : State} (h : ∀ i < 9, u.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0))
    (hsp : u.sp = s.sp) : abiPreserved s u := by
  refine ⟨fun r hr => ?_, hsp⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact h 5 (by decide)
  · exact h 6 (by decide)
  · exact h 7 (by decide)
  · exact h 8 (by decide)

/-- The exit, from a state whose header still holds the saved registers. -/
theorem finish_ok {s t : State} {base : Addr} {size : Nat} (hs : Ws t base size) (hz : 164 ≤ size)
    (hv : ∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = s.gpr (Entry.savedRegs.getD i .r0))
    (hsp : t.sp = s.sp) {Q : State → Prop}
    (hQ : ∀ u, abiPreserved s u → u.gpr .r0 = t.gpr .r0 → u.mem = t.mem → Q u) :
    WP isa (.seq (.block Entry.restore) (.block [])) t Q :=
  WP.seq (WP.mono (restore_ok hs hz hv) fun u ⟨G, R, M⟩ =>
    WP.block_nil (hQ u (abi_of_restored G (R.sp.trans hsp)) (R.gpr .r0 (by decide)) M))

end VG.Proof.Dsa.Arm
