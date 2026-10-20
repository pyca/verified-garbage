module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

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

/-- What every operation needs of a state. -/
structure RtWs (L : Lay) (s : State) (B : Addr) (Z len N : Nat) : Prop where
  ws : Ws s B Z (kw len) N
  lenArg : CallArgument s B Z L.len (BitVec.ofNat 32 len)
  wsArg : CallArgument s B Z L.ws (BitVec.ofNat 32 B.toNat)
  lenLe : len ≤ 1024
  layLen : 1 ≤ L.len

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- What a frame inside the workspace keeps: everything else. -/
theorem outs_outside {m m' : Mem} {rs : List (Nat × Nat)} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : Outside B 0 Z m m' :=
  fun x hx => h x fun r hm => by have := hr r hm; omega

theorem RtWs.keep {s t : State} (h : RtWs L s B Z len N) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (O : Outside B 0 Z s.mem t.mem) : RtWs L t B Z len N :=
  ⟨h.ws.rest K edi esp, h.lenArg.keep K esp O, h.wsArg.keep K esp O, h.lenLe, h.layLen⟩

/-- `edi` is the workspace. -/
theorem RtWs.wsSrc {s : State} (h : RtWs L s B Z len N) :
    readSrc s (.mem (argOp L.ws)) = some (BitVec.ofNat 32 B.toNat) := h.wsArg.readSrc

theorem RtWs.edi {s : State} (h : RtWs L s B Z len N) : (s.gpr .edi).toNat = B.toNat :=
  h.ws.workspace.edi_toNat

/-- The modulus's length argument, as `widthB` reads it. -/
abbrev lenOp (L : Lay) : MemOp := VG.Impl.Bignum.X86.PublicRt.argAt (L.len - 1) 1

theorem lenSrc {s : State} (h : RtWs L s B Z len N) :
    readSrc s (.mem (lenOp L)) = some (BitVec.ofNat 32 len) := by
  have e : lenOp L = VG.Impl.Bignum.X86.PublicFn.argument L.len := by
    simp only [lenOp, VG.Impl.Bignum.X86.PublicRt.argAt, VG.Impl.Bignum.X86.PublicFn.argument]
    congr 1; have := h.layLen; omega
  rw [e]; exact h.lenArg.readSrc

/-- An argument read the same after writes to registers but `esp`, memory kept. -/
theorem src_keep {s t : State} {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs) (m : t.mem = s.mem)
    {d : Nat} : readSrc t (.mem (at_ .esp d)) = readSrc s (.mem (at_ .esp d)) := by
  simp only [readSrc, State.load32, State.ea, at_, K.1 _ esp, m, K.2.1, K.2.2]; rfl

/-- Any operand read the same after writes to `ecx`, memory kept. -/
theorem src_keep' {s t : State} (K : Keeps [.ecx] s t) (m : t.mem = s.mem) {d : Nat} :
    readSrc t (.mem (sc d)) = readSrc s (.mem (sc d)) := by
  have e : t.gpr .edi = s.gpr .edi := K.1 _ (by decide)
  simp only [readSrc, State.load32, State.ea, sc, at_, e, m, K.2.1, K.2.2]; rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `bytesB r`: `r = 4 w`. -/
theorem bytesB_ok {r : Reg} (hl : readSrc s (.mem (lenOp L)) = some (BitVec.ofNat 32 len)) (hle : len ≤ 1024)
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * kw len → WP isa (.block is) t Q) :
    WP isa (.block (bytesB L r ++ is)) s Q :=
  widthB_ok hl hle fun t K m e => k t K m (by
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wb_le hle; omega), wb_kw])

/-- `count r extra`: `r = 4 w`, or `4 w + 4` with `extra`. -/
theorem count_ok {r : Reg} {extra : Bool} (hl : readSrc s (.mem (lenOp L)) = some (BitVec.ofNat 32 len))
    (hle : len ≤ 1024)
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * (kw len + extra.toNat) →
      WP isa (.block is) t Q) :
    WP isa (.block (count L r extra ++ is)) s Q := by
  have hw := wb_le hle
  rw [wb_kw] at hw
  unfold count
  cases extra with
  | false => simpa using bytesB_ok hl hle fun t K m e => k t K m (by simpa using e)
  | true =>
    simp only [ite_true, List.append_assoc, List.cons_append, List.nil_append]
    refine bytesB_ok hl hle fun t K m e => wp_addS rfl fun u U _ => k u (K.trans U.keeps) (U.mem.trans m) ?_
    rw [U.gpr, BitVec.toNat_add, e]; simp; omega

/-- `arrPtr r j t`: `r` at array `j`, `t = 4 w + 8`, for `edi` at the workspace. -/
theorem arrPtr_ok {r t : Reg} {j : Nat} (hl : readSrc s (.mem (lenOp L)) = some (BitVec.ofNat 32 len))
    (hle : len ≤ 1024) (hedi : (s.gpr .edi).toNat = B.toNat) (hrt : r ≠ t) (hte : t ≠ .edi)
    (hj : arr (kw len) j < 2 ^ 32)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (arr (kw len) j) →
      (u.gpr t).toNat = 4 * kw len + 8 → WP isa (.block is) u Q) :
    WP isa (.block (arrPtr L r j t ++ is)) s Q := by
  have hw := wb_le hle
  rw [wb_kw] at hw
  simp only [arrPtr, List.append_assoc, List.cons_append, List.nil_append]
  refine bytesB_ok hl hle fun s₁ K₁ m₁ e₁ => wp_addS rfl fun s₂ u₂ _ => wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => adds_ok hrt j fun u K m e => ?_
  have et : (s₂.gpr t).toNat = 4 * kw len + 8 := by
    rw [u₂.gpr, BitVec.toNat_add, e₁]; simp; omega
  have et₄ : s₄.gpr t = s₂.gpr t := by rw [u₄.other _ hrt.symm, u₃.other _ hrt.symm]
  have edi₂ : s₂.gpr .edi = s.gpr .edi := by rw [u₂.other _ hte.symm, K₁.1 _ (by simp [hte.symm])]
  refine k u (((K₁.mono (by simp)).trans (u₂.keeps.mono (by simp))).trans
      (((u₃.keeps.trans u₄.keeps).trans K).mono (by simp)))
    (by rw [m, u₄.mem, u₃.mem, u₂.mem, m₁]) ?_ (by rw [K.1 _ (by simp [hrt.symm]), et₄, et])
  rw [PtrAt, e, u₄.gpr, u₃.gpr, edi₂, et₄]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, et, hedi, arr, S, VG.Impl.Rsa.X86.Keys.hdr]
  have e8 : 4 * (kw len + 2) = 4 * kw len + 8 := by omega
  have : j * (4 * kw len + 8) < 2 ^ 32 := by
    simp only [arr, S, VG.Impl.Rsa.X86.Keys.hdr] at hj; rw [e8] at hj; omega
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
