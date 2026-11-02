module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # What the RSA key workspace's operations at a run-time width need of a state

`RtWs`: `Keys.Ws` with the width `kw len = 2 ⌈len / 8⌉` words, the modulus's
length `len` and the working space as arguments on the stack. A pointer to
array `j` (`arrPtr_ok`) is the workspace's `arr`, and `edi` set back from its
argument is the workspace (`restoreEdi_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)
open VG.Proof.Bignum.X86.PublicRt (wb wb_le widthB_ok adds_ok)

/-- The width in 32-bit words: `2 ⌈len / 8⌉`. -/
abbrev kw (len : Nat) : Nat := 2 * Spec.Rsa.modulusWords len

theorem wb_kw (len : Nat) : wb len = 4 * kw len := by simp only [wb, kw]; omega

/-- The length whose width `kw` is the shape's, from the modulus's length `a`. -/
def _root_.VG.Impl.Rsa.X86.KeyRt.Lay.toLen (L : Lay) (a : Nat) : Nat :=
  match L.shape with
  | .base => a
  | .narrow => a + 8
  | .wide => 2 * wb a + 24

theorem kw_bound {len : Nat} (hle : len ≤ 4096) : 4 * kw len ≤ 4104 := by
  simp only [kw, Spec.Rsa.modulusWords]; omega

/-- What every operation needs of a state. -/
structure RtWs (L : Lay) (s : State) (B : Addr) (Z len N : Nat) : Prop where
  ws : Ws s B Z (kw len) N
  lenArg : ∃ a, a ≤ 1024 ∧ kw (L.toLen a) = kw len ∧ CallArgument s B Z L.len (BitVec.ofNat 32 a)
  wsArg : CallArgument s B Z L.ws (BitVec.ofNat 32 B.toNat)
  lenLe : len ≤ 4096
  layLen : 1 ≤ L.len

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- What a frame inside the workspace keeps: everything else. -/
theorem outs_outside {m m' : Mem} {rs : List (Nat × Nat)} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : Outside B 0 Z m m' :=
  fun x hx => h x fun r hm => by have := hr r hm; omega

theorem RtWs.keep {s t : State} (h : RtWs L s B Z len N) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (O : Outside B 0 Z s.mem t.mem) : RtWs L t B Z len N :=
  ⟨h.ws.rest K edi esp, h.lenArg.imp fun _ ⟨a, l, c⟩ => ⟨a, l, c.keep K esp O⟩, h.wsArg.keep K esp O, h.lenLe,
    h.layLen⟩

/-- `edi` is the workspace. -/
theorem RtWs.wsSrc {s : State} (h : RtWs L s B Z len N) :
    readSrc s (.mem (argOp L.ws)) = some (BitVec.ofNat 32 B.toNat) := h.wsArg.readSrc

theorem RtWs.edi {s : State} (h : RtWs L s B Z len N) : (s.gpr .edi).toNat = B.toNat :=
  h.ws.workspace.edi_toNat

/-- The modulus's length argument, as `widthB` reads it. -/
abbrev lenOp (L : Lay) : MemOp := VG.Impl.Bignum.X86.PublicRt.argAt (L.len - 1) 1

theorem lenOp_eq (hL : 1 ≤ L.len) : lenOp L = VG.Impl.Bignum.X86.PublicFn.argument L.len := by
  simp only [lenOp, VG.Impl.Bignum.X86.PublicRt.argAt, VG.Impl.Bignum.X86.PublicFn.argument]
  congr 1; omega

/-- The modulus's length argument, as `widthB` reads it, of the width `kw len` for the shape. -/
def LenSrc (L : Lay) (s : State) (len : Nat) : Prop :=
  ∃ a, a ≤ 1024 ∧ kw (L.toLen a) = kw len ∧ readSrc s (.mem (lenOp L)) = some (BitVec.ofNat 32 a)

theorem lenSrc {s : State} (h : RtWs L s B Z len N) : LenSrc L s len :=
  have ⟨a, l, e, c⟩ := h.lenArg
  ⟨a, l, e, by rw [lenOp_eq h.layLen]; exact c.readSrc⟩

/-- An argument read the same after writes to registers but `esp`, memory kept. -/
theorem src_keep {s t : State} {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs) (m : t.mem = s.mem)
    {d : Nat} : readSrc t (.mem (at_ .esp d)) = readSrc s (.mem (at_ .esp d)) := by
  simp only [readSrc, State.load32, State.ea, at_, K.1 _ esp, m, K.2.1, K.2.2]; rfl

/-- Any operand read the same after writes to `ecx`, memory kept. -/
theorem LenSrc.keep {s t : State} {rs : List Reg} (hl : LenSrc L s len) (K : Keeps rs s t) (esp : .esp ∉ rs)
    (m : t.mem = s.mem) : LenSrc L t len :=
  have ⟨a, l, e, r⟩ := hl
  ⟨a, l, e, (src_keep K esp m).trans r⟩

theorem src_keep' {s t : State} (K : Keeps [.ecx] s t) (m : t.mem = s.mem) {d : Nat} :
    readSrc t (.mem (sc d)) = readSrc s (.mem (sc d)) := by
  have e : t.gpr .edi = s.gpr .edi := K.1 _ (by decide)
  simp only [readSrc, State.load32, State.ea, sc, at_, e, m, K.2.1, K.2.2]; rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `bytesB r`: `r = 4 w`. -/
theorem bytesB_ok {r : Reg} (hl : LenSrc L s len) (_hle : len ≤ 4096)
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * kw len → WP isa (.block is) t Q) :
    WP isa (.block (bytesB L r ++ is)) s Q := by
  obtain ⟨a, ha, he, hr⟩ := hl
  rw [← he] at k
  have hw := wb_le ha
  unfold bytesB
  rw [List.append_assoc]
  refine widthB_ok hr ha fun t K m e => ?_
  have et : (t.gpr r).toNat = wb a := by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Lay.toLen at k
  cases hs : L.shape with
  | base =>
    simp only [hs] at k
    simpa only [Shape.extra, List.nil_append] using k t K m (by rw [et, wb_kw])
  | narrow =>
    simp only [hs] at k
    simp only [Shape.extra, List.cons_append, List.nil_append]
    refine wp_addS rfl fun u U _ => k u (K.trans U.keeps) (U.mem.trans m) ?_
    rw [U.gpr, BitVec.toNat_add, et, show (8 : BitVec 32).toNat = 8 from rfl]
    simp only [wb, kw, Spec.Rsa.modulusWords]
    omega
  | wide =>
    simp only [hs] at k
    simp only [Shape.extra, List.cons_append, List.nil_append]
    refine wp_addS rfl fun u U _ => wp_addS rfl fun v V _ =>
      k v ((K.trans U.keeps).trans V.keeps) (V.mem.trans (U.mem.trans m)) ?_
    rw [V.gpr, U.gpr, BitVec.toNat_add, BitVec.toNat_add, et, show (24 : BitVec 32).toNat = 24 from rfl]
    simp only [wb, kw, Spec.Rsa.modulusWords]
    omega

/-- `count r extra`: `r = 4 w`, or `4 w + 4` with `extra`. -/
theorem count_ok {r : Reg} {extra : Bool} (hl : LenSrc L s len)
    (hle : len ≤ 4096)
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * (kw len + extra.toNat) →
      WP isa (.block is) t Q) :
    WP isa (.block (count L r extra ++ is)) s Q := by
  have hw := kw_bound hle
  unfold count
  cases extra with
  | false => simpa using bytesB_ok hl hle fun t K m e => k t K m (by simpa using e)
  | true =>
    simp only [ite_true, List.append_assoc, List.cons_append, List.nil_append]
    refine bytesB_ok hl hle fun t K m e => wp_addS rfl fun u U _ => k u (K.trans U.keeps) (U.mem.trans m) ?_
    rw [U.gpr, BitVec.toNat_add, e]; simp; omega

/-- `addMul r t fuel j`: `r += j t`, `t` kept, for `j t` below `2^32`. -/
theorem addMul_ok {r t : Reg} (hrt : r ≠ t) : ∀ (fuel j : Nat) {s : State} {is : List Instr}
    {Q : State → Prop}, j * (s.gpr t).toNat < 2 ^ 32 →
    (∀ u, Keeps [r] s u → u.mem = s.mem →
      u.gpr r = s.gpr r + BitVec.ofNat 32 (j * (s.gpr t).toNat) → WP isa (.block is) u Q) →
    WP isa (.block (addMul r t fuel j ++ is)) s Q
  | 0, j, _, _, _, _, k => by simp only [addMul]; exact adds_ok hrt j k
  | fuel + 1, j, s, is, Q, hb, k => by
    simp only [addMul, List.append_assoc]
    have odd : ∀ {is' : List Instr}, (∀ u, Keeps [r] s u → u.mem = s.mem →
        u.gpr r = s.gpr r + BitVec.ofNat 32 (j % 2 * (s.gpr t).toNat) → WP isa (.block is') u Q) →
        WP isa (.block ((if j % 2 = 1 then [.alu .add r (.reg t)] else []) ++ is')) s Q := by
      intro is' k'
      split
      · next h =>
        simp only [List.cons_append, List.nil_append]
        exact wp_addS rfl fun u U _ => k' u U.keeps U.mem (by rw [U.gpr, h, Nat.one_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      · next h =>
        simp only [List.nil_append]
        exact k' s (Keeps.refl _ _) rfl (by rw [show j % 2 = 0 by omega, Nat.zero_mul]; simp)
    refine odd fun u K m e => ?_
    have ut : u.gpr t = s.gpr t := K.1 _ (by simp [hrt.symm])
    have split : j * (s.gpr t).toNat = j % 2 * (s.gpr t).toNat + j / 2 * (2 * (s.gpr t).toNat) := by
      have := Nat.mod_add_div j 2
      grind
    split
    · next h0 =>
      simp only [List.nil_append]
      refine k u K m ?_
      rw [e, split, h0, Nat.zero_mul, Nat.add_zero]
    · next h0 =>
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      have h2 : 2 * (s.gpr t).toNat ≤ j * (s.gpr t).toNat := Nat.mul_le_mul_right _ (by omega)
      refine wp_addS rfl fun v V _ => ?_
      have vt : (v.gpr t).toNat = 2 * (s.gpr t).toNat := by
        rw [V.gpr, BitVec.toNat_add, ut]; omega
      have vr : v.gpr r = u.gpr r := V.other _ hrt
      have hb' : j / 2 * (v.gpr t).toNat < 2 ^ 32 := by rw [vt]; omega
      refine addMul_ok hrt fuel (j / 2) hb' fun w W mw ew => wp_shr (by decide) fun z Z _ => ?_
      have wt : w.gpr t = v.gpr t := W.1 _ (by simp [hrt.symm])
      have zt : z.gpr t = s.gpr t := by
        rw [Z.gpr, wt]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, vt, Nat.shiftRight_eq_div_pow]
        omega
      refine k z ⟨fun x hx => ?_, ?_, ?_⟩ (by rw [Z.mem, mw, V.mem, m]) ?_
      · by_cases hxt : x = t
        · rw [hxt, zt]
        · have hxr : x ≠ r := fun h => hx (by simp [h])
          rw [Z.other _ hxt, W.1 _ (by simp [hxr]), V.other _ hxt, K.1 _ (by simp [hxr])]
      · rw [Z.keeps.2.1, W.2.1, V.keeps.2.1, K.2.1]
      · rw [Z.keeps.2.2, W.2.2, V.keeps.2.2, K.2.2]
      · rw [Z.other _ hrt, ew, vr, e, vt, split, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega

/-- `arrPtr r j t`: `r` at array `j`, `t = 4 w + 8`, for `edi` at the workspace. -/
theorem arrPtr_ok {r t : Reg} {j : Nat} (hl : LenSrc L s len)
    (hle : len ≤ 4096) (hedi : (s.gpr .edi).toNat = B.toNat) (hrt : r ≠ t) (hte : t ≠ .edi)
    (hj : arr (kw len) j < 2 ^ 32)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (arr (kw len) j) →
      (u.gpr t).toNat = 4 * kw len + 8 → WP isa (.block is) u Q) :
    WP isa (.block (arrPtr L r j t ++ is)) s Q := by
  have hw := kw_bound hle
  simp only [arrPtr, List.append_assoc, List.cons_append, List.nil_append]
  refine bytesB_ok hl hle fun s₁ K₁ m₁ e₁ => wp_addS rfl fun s₂ u₂ _ => wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  have et : (s₂.gpr t).toNat = 4 * kw len + 8 := by
    rw [u₂.gpr, BitVec.toNat_add, e₁]; simp; omega
  have et₄ : s₄.gpr t = s₂.gpr t := by rw [u₄.other _ hrt.symm, u₃.other _ hrt.symm]
  have edi₂ : s₂.gpr .edi = s.gpr .edi := by rw [u₂.other _ hte.symm, K₁.1 _ (by simp [hte.symm])]
  have e8 : 4 * (kw len + 2) = 4 * kw len + 8 := by omega
  have this : j * (4 * kw len + 8) < 2 ^ 32 := by
    simp only [arr, S, VG.Impl.Rsa.X86.Keys.hdr] at hj; rw [e8] at hj; omega
  refine addMul_ok hrt _ j (by rw [et₄, et]; exact this) fun u K m e => ?_
  refine k u (((K₁.mono (by simp)).trans (u₂.keeps.mono (by simp))).trans
      (((u₃.keeps.trans u₄.keeps).trans K).mono (by simp)))
    (by rw [m, u₄.mem, u₃.mem, u₂.mem, m₁]) ?_ (by rw [K.1 _ (by simp [hrt.symm]), et₄, et])
  rw [PtrAt, e, u₄.gpr, u₃.gpr, edi₂, et₄]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, et, hedi, arr, S, VG.Impl.Rsa.X86.Keys.hdr]
  rw [Nat.mod_eq_of_lt (a := 160) (by omega), Nat.mod_eq_of_lt (a := j * (4 * kw len + 8)) this,
    Nat.mod_add_mod, e8, Nat.add_assoc]

/-- `restoreEdi`: `edi` the workspace again. -/
theorem restoreEdi_ok (hws : readSrc s (.mem (argOp L.ws)) = some (BitVec.ofNat 32 B.toNat))
    (k : ∀ t, Keeps [.edi] s t → t.mem = s.mem → t.gpr .edi = BitVec.ofNat 32 B.toNat → WP isa (.block is) t Q) :
    WP isa (.block (restoreEdi L ++ is)) s Q := by
  simp only [restoreEdi, List.cons_append, List.nil_append]
  exact wp_movS hws fun t u _ => k t u.keeps u.mem u.gpr

end

end VG.Proof.Rsa.X86.KeyRt
