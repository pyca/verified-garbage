module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Omega
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass

/-! # The key workspace's header words at a run-time width

What leaves `edi` and the stack and writes inside the workspace keeps the
arguments (`RtWs.lift`), so `Keys`' lemmas about header words hold on `RtWs`
(`storeSlot_ok`, `andS_ok`); and, through `Ops`, the equality test (`eqS_ok`)
and a header word added to an array's low word (`addLow_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot)
open VG.Proof.Rsa.KeyBits32

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- A frame inside the workspace keeps everything else. -/
theorem keep_outside {s : State} (h : Ws s B Z (kw len) N) {js ds : List Nat} {m m' : Mem}
    (F : Keep B (kw len) js ds m m') (hj : ∀ j ∈ js, j < N) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    Outside B 0 Z m m' := by
  have head := h.hdr_le
  refine outs_outside F fun r hr => ?_
  simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj', rfl⟩ | ⟨d, hd', rfl⟩
  · exact h.arr_fit (hj j hj')
  · have := hd d hd'; dsimp only; omega

/-- A `Keys` lemma on `RtWs`: what keeps `edi` and `esp` and writes in the workspace. -/
theorem RtWs.lift {s : State} (h : RtWs L s B Z len N) {p : Prog isa} {rs : List Reg} {js ds : List Nat}
    {P : State → Prop} (esp : .esp ∉ rs) (hj : ∀ j ∈ js, j < N)
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (k : WP isa p s fun t => Ws t B Z (kw len) N ∧ Keep B (kw len) js ds s.mem t.mem ∧ P t ∧ Keeps rs s t) :
    WP isa p s fun t => RtWs L t B Z len N ∧ Keep B (kw len) js ds s.mem t.mem ∧ P t ∧ Keeps rs s t :=
  WP.mono k fun _ ⟨W, F, p, K⟩ =>
    ⟨⟨W, h.lenArg.imp fun _ ⟨l, e, c⟩ => ⟨l, e, c.keep K esp (keep_outside W F hj hd)⟩, h.wsArg.keep K esp (keep_outside W F hj hd), h.lenLe,
      h.layLen⟩, F, p, K⟩

theorem storeSlot_ok {s : State} (h : RtWs L s B Z len N) {d : Nat} (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [] [d] s.mem t.mem ∧
      slot t.mem B d = (s.gpr r).toNat ∧ Keeps [] s t :=
  h.lift (by decide) (by simp) (by simpa using hd) (VG.Proof.Rsa.X86.Keys.store_slot h.ws hd r)

theorem andS_ok {s : State} (h : RtWs L s B Z len N) {d a b : Nat} (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (ha : a + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (hb : b + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) :
    WP isa (.block (VG.Impl.Rsa.X86.Keys.andS d a b)) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [] [d] s.mem t.mem ∧
      slot t.mem B d = (if slot s.mem B a = 1 ∧ slot s.mem B b = 1 then 1 else 0) ∧ Keeps [.eax] s t :=
  h.lift (by decide) (by simp) (by simpa using hd) (VG.Proof.Rsa.X86.Keys.andS_ok h.ws hd ha hb ba bb)

theorem eqS_ok {s : State} (h : RtWs L s B Z len N) {d a b t : Nat}
    (ht : t < N) (ha : a < N) (hb : b < N) (hta : t ≠ a) (htb : t ≠ b) (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.eqS L d a b t) s fun u => RtWs L u B Z len N ∧
      Keep B (kw len) [t] [VG.Impl.Rsa.X86.Keys.sT, d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B (kw len) a = num s.mem B (kw len) b then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s u := by
  have hT : VG.Impl.Rsa.X86.Keys.sT + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  unfold VG.Impl.Rsa.X86.KeyRt.eqS
  refine WP.seq (WP.mono (sub3_ok h ht ha hb) fun u1 ⟨h1, k1, v1, b1, r1⟩ => ?_)
  refine WP.seq (WP.mono (storeSlot_ok h1 hT .ebx) fun u2 ⟨h2, k2, s2, r2⟩ => ?_)
  refine WP.seq (WP.mono (sub3_ok h2 ht hb ha) fun u3 ⟨h3, k3, v3, b3, r3⟩ => ?_)
  have head := h3.ws.hdr_le
  refine wp_orS (readSrc_sc h3.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.sT VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun s5 u5 => ?_
  refine wp_logicS (.inr rfl) rfl fun s6 u6 => ?_
  have h6 := h3.keep (u5.keeps.trans u6.keeps) (by decide) (by decide)
    (by rw [u6.mem, u5.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok h6 hd .ebx) fun u ⟨h7, k7, e7, r7⟩ => ?_
  have mem : s6.mem = u3.mem := u6.mem.trans u5.mem
  rw [mem] at k7
  have fa := h.ws.fit64 ha
  have fb := h.ws.fit64 hb
  have na2 : num u2.mem B (kw len) a = num s.mem B (kw len) a := by
    rw [k2.num (by simp) (by simp; decide) fa, k1.num (by simpa using hta) (by simp) fa]
  have nb2 : num u2.mem B (kw len) b = num s.mem B (kw len) b := by
    rw [k2.num (by simp) (by simp; decide) fb, k1.num (by simpa using htb) (by simp) fb]
  rw [na2, nb2] at v3
  have sT3 : slot u3.mem B VG.Impl.Rsa.X86.Keys.sT = (u1.gpr .ebx).toNat := by rw [k3.slot hT (by simp), s2]
  refine ⟨h7, (k1.join k2 (js := [t]) (ds := [VG.Impl.Rsa.X86.Keys.sT, d])).join
    (k3.join k7 (js := [t]) (ds := [VG.Impl.Rsa.X86.Keys.sT, d])) (js := [t]) (ds := [VG.Impl.Rsa.X86.Keys.sT, d]),
    ?_, ?_⟩
  · rw [e7, u6.gpr, ite_eq_right (by decide), u5.gpr]
    have e : (u3.mem.readW (off B VG.Impl.Rsa.X86.Keys.sT) 32).toNat = (u1.gpr .ebx).toNat := sT3
    rw [bv_nor_bits b3 (by rw [e]; exact b1), e]
    have p1 := VG.Proof.Rsa.borrow_iff v1 (val32_lt _ _ _ _) b1
    have p3 := VG.Proof.Rsa.borrow_iff v3 (val32_lt _ _ _ _) b3
    by_cases eq : num s.mem B (kw len) a = num s.mem B (kw len) b
    · have c1 := p1.mpr (by omega)
      have c3 := p3.mpr (by omega)
      simp [c1, c3, eq]
    · have c : ¬((u3.gpr .ebx).toNat = 0 ∧ (u1.gpr .ebx).toNat = 0) :=
        fun hh => eq (by have := p1.mp hh.2; have := p3.mp hh.1; omega)
      simp only [c, eq, ↓reduceIte]
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u5.keeps.mono (by decide)).trans ((u6.keeps.mono (by decide)).trans (r7.mono (by decide))))))

/-- `[j]`'s low word plus the header word `sl`, for `[j]` even and the word a bit. -/
theorem addLow_ok {s : State} (h : RtWs L s B Z len N) {j sl : Nat} (hj : j < N)
    (hsl : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (.block (addLow L j sl)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      (num s.mem B (kw len) j % 2 = 0 → slot s.mem B sl ≤ 1 →
        num t.mem B (kw len) j = num s.mem B (kw len) j + slot s.mem B sl) ∧ Keeps [.eax, .ecx, .edx] s t ∧
      w32 t.mem B (arr (kw len) j + 4 * kw len) = w32 s.mem B (arr (kw len) j + 4 * kw len) := by
  have positive := h.kw_pos
  have head := h.ws.hdr_le
  unfold addLow
  refine lowPtr_ok h hj fun u hu K m p => wp_movS (lowSrc hu hj p) fun v V _ => ?_
  have hv := hu.keep V.keeps (by decide) (by decide) (by rw [V.mem]; exact Outside.refl _ _ _ _)
  refine wp_addS (readSrc_sc hv.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at hsl head; omega)) fun x X _ => ?_
  have KX : Keeps [.ecx] u x := V.keeps.trans X.keeps
  have hx := hu.keep KX (by decide) (by decide) (by rw [X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeLow_ok hx hj (by rw [PtrAt, KX.1 _ (by decide)]; exact p)) fun t ⟨ht, F, Vt, Kt, top⟩ => ?_
  have mx : x.mem = s.mem := by rw [X.mem, V.mem, m]
  rw [mx] at F Vt top
  refine ⟨ht, F, ?_, ((K.mono (by decide)).trans (KX.mono (by decide))).trans (Kt.mono (by decide)), top⟩
  intro even bit
  have low := low_word (B := B) (m := s.mem) (j := j) positive
  have sv : (v.mem.readW (off B sl) 32).toNat = slot s.mem B sl := by rw [V.mem, m]
  rw [Vt, X.gpr, V.gpr, m, BitVec.toNat_add, sv, ← low]
  have lowEven : num s.mem B (kw len) j % 2 ^ 32 % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide)]; exact even
  have lt : num s.mem B (kw len) j % 2 ^ 32 + slot s.mem B sl < 2 ^ 32 := by
    have := Nat.mod_lt (num s.mem B (kw len) j) (show 0 < 2 ^ 32 by decide)
    omega
  rw [Nat.mod_eq_of_lt lt]
  omega

end VG.Proof.Rsa.X86.KeyRt
