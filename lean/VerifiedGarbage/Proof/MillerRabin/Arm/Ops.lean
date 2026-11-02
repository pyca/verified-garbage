module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Framework.Block

/-! # The Miller–Rabin round on ARMv7: the operations on a stage

The operations of the key working space (`Impl/Rsa/Arm/KeyWs.lean`) from a
stage `KS` to the next, with the value they write recorded: a copy, the top
words of an array cleared, both (`copyClr`, which gives a number of the
working space), a selection and a comparison.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout)

theorem wDs_sep : ∀ d ∈ wDs, ∀ e ∈ wDs, d ≠ e → d + 4 ≤ e ∨ e + 4 ≤ d := by decide
theorem wDs_hdr : ∀ d ∈ wDs, d + 4 ≤ hdr := by decide

/-- The low `k` words of a number of `k + j` words. -/
theorem val32_low (m : Mem) (b : Addr) (d k j : Nat) : val32 m b d k = val32 m b d (k + j) % 2 ^ (32 * k) := by
  rw [val32_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

section
variable {P : MP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.fit (h : KS P σ A live V ls s) {j : Nat} (hj : j < nArr) : arr P.W j + S P.W ≤ 2 ^ 64 := by
  exact Nat.le_trans (arr_end hj) (Nat.le_trans h.pre.fitsK (Nat.le_trans h.pre.Z_le (by decide)))

/-- The arrays a step does not write. -/
theorem KS.arrs_keep {js ds : List Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hl : ∀ j ∈ live, j ∉ js) (hds : ∀ d ∈ ds, d ∈ wDs) : Arrs t.mem P.B P.W A live := by
  intro j hj
  rw [k.num (fun i hi e => hl j hj (by subst e; exact hi)) (fun d hd => wDs_hdr d (hds d hd)) (h.fit (h.live_lt j hj))]
  exact h.arrs j hj

/-- The header words a step does not write. -/
theorem KS.sl_keep {js ds : List Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hls : ∀ d ∈ ls, d ∉ ds) (hds : ∀ d ∈ ds, d ∈ wDs) : ∀ d ∈ ls, slot t.mem P.B d = V d := by
  intro d hd
  rw [k.slot (wDs_hdr d (h.ls_ok d hd)) (fun e he => wDs_sep d (h.ls_ok d hd) e (hds e he)
    (fun x => hls d hd (x ▸ he))), h.sl d hd]

/-- An array the round does not write keeps its value. -/
theorem KS.input (h : KS P σ A live V ls s) {j : Nat} (hj : j < nArr) (hw : j ∉ wJs) :
    num s.mem P.B P.W j = num σ.mem P.B P.W j :=
  h.keep.num (fun _ hi e => hw (by subst e; exact hi)) wDs_hdr (h.fit hj)

/-- An array of the working space the round does not write keeps its number. -/
theorem KS.numAt_input (h : KS P σ A live V ls s) {j : Nat} (hj : j < nArr) (hw : j ∉ wJs) :
    numAt s.mem (State.addr P.ws) P.w j = numAt σ.mem (State.addr P.ws) P.w j := by
  have pre := h.pre
  rw [pre.numAt_val32, pre.numAt_val32, val32_low _ _ _ (2 * P.w) 2, val32_low σ.mem _ _ (2 * P.w) 2]
  have e := h.input hj hw
  simp only [num, MP.W] at e
  rw [show 2 * P.w + 2 = 2 * P.w + 2 from rfl, e]

/-- A step that writes `[o] := x` alone, and header words `ds`. -/
theorem KS.write1 {o x : Nat} {ds : List Nat} (h : KS P σ A live V ls s)
    (k : Keep P.B P.W [o] ds s.mem t.mem) (ho : o ∈ wJs) (hds : ∀ d ∈ ds, d ∈ wDs)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (e : num t.mem P.B P.W o = x)
    (hls : ∀ d ∈ ls, d ∉ ds) : KS P σ (upd A o x) (o :: live) V ls t := by
  refine h.core k (by simpa using ho) hds sp rd wr (fun j hj => ?_) (h.sl_keep k hls hds) (fun j hj => ?_) h.ls_ok
  · by_cases hjo : j = o
    · subst hjo; rw [upd_self]; exact e
    · have hj' : j ∈ live := (List.mem_cons.mp hj).resolve_left hjo
      rw [upd_ne _ _ hjo, k.num (fun i hi ei => hjo (by simp at hi; subst hi; exact ei.symm))
        (fun d hd => wDs_hdr d (hds d hd)) (h.fit (h.live_lt j hj'))]
      exact h.arrs j hj'
  · rcases List.mem_cons.mp hj with rfl | hj'
    · exact (wJs_lt j ho).2
    · exact h.live_lt j hj'

/-- A step that writes the header word `d := x` alone. -/
theorem KS.slot1 {d x : Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W [] [d] s.mem t.mem)
    (hd : d ∈ wDs) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (e : slot t.mem P.B d = x) :
    KS P σ A live (upd V d x) (d :: ls) t := by
  refine h.core k (by simp) (by simpa using hd) sp rd wr (h.arrs_keep k (by simp) (by simpa using hd))
    (fun d' hd' => ?_) h.live_lt (fun d' hd' => ?_)
  · by_cases e' : d' = d
    · subst e'; rw [upd_self]; exact e
    · have hd'' := (List.mem_cons.mp hd').resolve_left e'
      rw [upd_ne _ _ e', k.slot (wDs_hdr d' (h.ls_ok d' hd'')) (fun y hy => by
        simp only [List.mem_singleton] at hy; subst hy
        exact wDs_sep d' (h.ls_ok d' hd'') y hd e'), h.sl d' hd'']
  · rcases List.mem_cons.mp hd' with rfl | hd''
    · exact hd
    · exact h.ls_ok d' hd''

/-- `str t, [r8, #d]` of the round's header word `d`. -/
theorem KS.str {d : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (hd : d ∈ wDs) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd V d (s.gpr r).toNat) (d :: ls) t → Ws t P.B P.Z P.W nArr → Mupd s t
      (s.mem.writeW (off (State.addr P.B) d) (s.gpr r)) → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q :=
  wp_strSlot hw (wDs_hdr d hd) fun t m => by
    have kt : Keep P.B P.W [] [d] s.mem t.mem := by
      rw [m.mem]; exact keep_write _ _ (by simp) (by have := wDs_hdr d hd; simp only [hdr] at this; omega)
    exact k t (h.slot1 kt hd m.sp m.rd m.wr (by rw [m.mem, slot_write_self])) (hw.of_mupd m) m

/-- `ldr t, [r8, #d]` of a header word the stage holds. -/
theorem KS.ldr {d : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (hd : d ∈ ls) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live V ls t → Ws t P.B P.Z P.W nArr → Upd s t r (BitVec.ofNat 32 (V d)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldr r .r8 d :: rest)) s Q :=
  wp_ldrSlot hw (wDs_hdr d (h.ls_ok d hd)) fun t u => by
    have e : s.mem.readW (off (State.addr P.B) d) 32 = BitVec.ofNat 32 (V d) := by
      rw [← h.sl d hd]; simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [e] at u
    exact k t (h.of_rest (u.rest (ws := [r]) (by simp)) u.mem)
      (hw.of_upd u (fun x => hr (by simp [x])) (fun x => hr (by simp [x])) (fun x => hr (by simp [x]))) u

/-- `copy o a`. -/
theorem KS.copy_ok {o a : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (ho : o ∈ wJs)
    (ha : a < nArr) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => KS P σ (upd A o (num s.mem P.B P.W a)) (o :: live) V ls t ∧
      Ws t P.B P.Z P.W nArr ∧ Rest opRegs s t :=
  WP.mono (VG.Proof.Rsa.Arm.Keys.copy_ok hw (wJs_lt o ho).2 ha (by decide) hoa) fun _ ⟨ht, k, e, r, _⟩ =>
    ⟨h.write1 k ho (by simp) r.sp r.rd r.wr e (by simp), ht, r⟩

/-- `clrTop o`: the low `2 w` words of `[o]`. -/
theorem KS.clrTop_ok {o : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (ho : o ∈ wJs)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ (upd A o (val32 s.mem (State.addr P.B) (arr P.W o) (2 * P.w))) (o :: live) V ls t →
      Ws t P.B P.Z P.W nArr → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (Impl.Rsa.Arm.Recover.clrTop o ++ rest)) s Q :=
  VG.Proof.Rsa.Arm.Recover.clrTop_ok hw (wJs_lt o ho).2 (by decide) (by simp only [MP.W]; omega)
    fun t ht k' e r => k t (h.write1 k' ho (by simp) r.sp r.rd r.wr (by rw [e]; rfl) (by simp)) ht r

/-- `copy o a` and `clrTop o`: the number of the working space's array `a`. -/
theorem KS.copyClr_ok {o a : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (ho : o ∈ wJs)
    (ha : a < nArr) (hoa : o ≠ a) :
    WP isa (seqs (copyClr o a)) s fun t =>
      KS P σ (upd A o (numAt s.mem (State.addr P.ws) P.w a)) (o :: live) V ls t ∧ Ws t P.B P.Z P.W nArr := by
  have pre := h.pre
  simp only [copyClr, seqs]
  rw [WP.seq_iff]
  refine WP.mono (h.copy_ok hw ho ha hoa) fun t1 ⟨h1, hw1, r1⟩ => ?_
  rw [← List.append_nil (Impl.Rsa.Arm.Recover.clrTop o)]
  refine h1.clrTop_ok hw1 ho fun t ht hwt _ => WP.block_nil ⟨?_, hwt⟩
  have e : val32 t1.mem (State.addr P.B) (arr P.W o) (2 * P.w) = numAt s.mem (State.addr P.ws) P.w a := by
    rw [pre.numAt_val32, val32_low _ _ _ (2 * P.w) 2, val32_low s.mem _ _ (2 * P.w) 2]
    have e1 := h1.arrs o (by simp)
    rw [upd_self] at e1
    simp only [num, MP.W] at e1
    rw [e1]
  rw [e] at ht
  refine ht.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  by_cases hjo : j = o <;> simp [upd, hjo]

/-- `sel o a b sl`. -/
theorem KS.sel_ok {o a b sl : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr) (ho : o ∈ wJs)
    (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ ls) (bit : V sl ≤ 1) :
    WP isa (sel o a b sl) s fun t =>
      KS P σ (upd A o (if V sl = 0 then A a else A b)) (o :: live) V ls t ∧ Ws t P.B P.Z P.W nArr ∧
        Rest opRegs s t := by
  have hs := h.sl sl hsl
  refine WP.mono (VG.Proof.Rsa.Arm.Keys.sel_ok hw (wJs_lt o ho).2 (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob
    (wDs_hdr sl (h.ls_ok sl hsl)) (by rw [hs]; exact bit)) fun _ ⟨ht, k, e, r⟩ => ?_
  refine ⟨h.write1 k ho (by simp) r.sp r.rd r.wr ?_ (by simp), ht, r⟩
  rw [e, hs, h.arrs a ha, h.arrs b hb]

/-- `eqS d a b t`: the header word `d := [a] = [b]`, through `[t]` and `sT`. -/
theorem KS.eqS_ok {d a b t : Nat} (h : KS P σ A live V ls s) (hw : Ws s P.B P.Z P.W nArr)
    (ha : a ∈ live) (hb : b ∈ live) (hd : d ∈ wDs) (htw : t ∈ wJs) (hT : t ∉ live) (hls : sT ∉ ls)
    (hdT : d ≠ sT) :
    WP isa (eqS d a b t) s fun u =>
      KS P σ A live (upd V d (if A a = A b then 1 else 0)) (d :: ls) u ∧ Ws u P.B P.Z P.W nArr ∧
        Rest opRegs s u := by
  have hTa : t ≠ a := fun e => hT (e ▸ ha)
  have hTb : t ≠ b := fun e => hT (e ▸ hb)
  refine WP.mono (VG.Proof.Rsa.Arm.Keys.eqS_ok hw (t := t) (wJs_lt t htw).2 (h.live_lt a ha) (h.live_lt b hb)
    (by decide) hTa hTb (wDs_hdr d hd)) fun u ⟨hu, k, e, r⟩ => ⟨?_, hu, r⟩
  have hds : ∀ x ∈ [sT, d], x ∈ wDs := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · rw [List.mem_singleton.mp hx]; exact hd
  refine h.core k (by simpa using htw) hds r.sp r.rd r.wr
    (h.arrs_keep k (fun j hj e => by simp at e; exact hT (e ▸ hj)) hds) (fun x hx => ?_) (h.live_lt)
    (fun x hx => ?_)
  · by_cases e' : x = d
    · subst e'; rw [upd_self, e, h.arrs a ha, h.arrs b hb]
    · have hx' := (List.mem_cons.mp hx).resolve_left e'
      rw [upd_ne _ _ e', k.slot (wDs_hdr x (h.ls_ok x hx')) (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact wDs_sep x (h.ls_ok x hx') _ (by decide) (fun x' => hls (x' ▸ hx'))
        · exact wDs_sep x (h.ls_ok x hx') _ hd e'), h.sl x hx']
  · rcases List.mem_cons.mp hx with rfl | hx'
    · exact hd
    · exact h.ls_ok x hx'

end

end VG.Proof.MillerRabin.Arm
