module

public import VerifiedGarbage.Impl.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Spec.Rsa.Contract
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Weierstrass.BytesLen32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # DSA component decoding, encoding and failure-output masking -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Impl.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem toBytes_encodeBE (n x : Nat) : Spec.Weierstrass.toBytes n x = Spec.Dsa.encodeBE n x := by
  apply List.ext_getElem
  · simp only [Spec.Weierstrass.toBytes, Spec.Dsa.encodeBE, List.length_map, List.length_reverse, List.length_range]
  · intro i hi hj
    simp only [Spec.Weierstrass.toBytes, Spec.Dsa.encodeBE, List.getElem_map, List.getElem_reverse,
      List.length_range, List.getElem_range]

/-- `ebx` after `j` words: `len - 4 (j + 1)` bytes into the component. -/
theorem ebx_at {e x : BitVec 32} {len j : Nat} (h : x + BitVec.ofNat 32 (4 * j) = e + BitVec.ofNat 32 (len - 4))
    (hj : 4 * (j + 1) ≤ len) : x = e + BitVec.ofNat 32 (len - 4 * (j + 1)) := by
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := e.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h' ⊢
  omega

/-- `[ebx]`, at `e` bytes into the component at `x`. -/
theorem ea_ebx {t : State} {x : BitVec 32} {e : Nat} (he : t.gpr .ebx = x + BitVec.ofNat 32 e)
    (h : x.toNat + e < 2 ^ 32) : t.ea (at_ .ebx 0) = x.setWidth 64 + BitVec.ofNat 64 e := by
  show ((t.gpr .ebx + BitVec.ofNat 32 0).setWidth 64) = _
  rw [he, BitVec.add_zero]
  exact addr_eq h

/-- `ebx` a word lower. -/
theorem ebx_down {x e : BitVec 32} {j : Nat} (h : x + BitVec.ofNat 32 (4 * j) = e) :
    x - BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * (j + 1)) = e := by
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Zero words from `[o + 4c]`. -/
theorem zeroPadInline_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o c K : Nat}
    (hK : o + 4 * (c + K) ≤ size) :
    ∀ k ≤ K, WP isa (.block ((List.range k).flatMap fun j =>
      [.mov .eax (.imm 0), .store (sc (o + 4 * (c + j))) .eax])) s fun u =>
      (∀ j < k, w32 u.mem base (o + 4 * (c + j)) = 0) ∧ Keeps [.eax] s u ∧
      Outside base (o + 4 * c) (4 * k) s.mem u.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (zeroPadInline_ok hs hK k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    refine wp_movS (v := 0) rfl fun s₂ u₂ _ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (d := o + 4 * (c + k)) (by omega)) (hs₂.write (d := o + 4 * (c + k)) (n := 4) (by omega))
      fun s₃ m₃ => WP.block_nil ?_
    have O₂ : Outside base (o + 4 * (c + k)) 4 s₁.mem s₃.mem := by
      rw [m₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (u₂.keeps.trans (m₃.keeps _)),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₃.mem, u₂.mem, w32_write_self, u₂.gpr]; rfl

theorem zeroPad_ok {s : State} {base : Addr} {size o k : Nat}
    (hs : Scr s base size) (hz : o + 4 * k ≤ size) :
    WP isa (zeroPad o k) s fun t =>
      (∀ j < k, w32 t.mem base (o + 4 * j) = 0) ∧
      Keeps [.eax, .ebp, .edx] s t ∧ Outside base o (4 * k) s.mem t.mem := by
  unfold zeroPad
  split
  · have H := zeroPadInline_ok hs (o := o) (c := 0) (K := k) (by omega) k (Nat.le_refl _)
    simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at H
    exact WP.mono H fun _ ⟨V, K, O⟩ => ⟨V, K.mono (by decide), O⟩
  · refine WP.mono (zerosW_ok hs (by omega) hz) fun t ⟨O, V, K⟩ => ⟨?_, K, O⟩
    intro j hj
    have h := val32_append t.mem base o j (k - j)
    rw [Nat.add_sub_of_le (by omega), V] at h
    have hk : k - j = (k - j - 1) + 1 := by omega
    rw [hk, val32] at h
    have H : 2 ^ (32 * j) * (w32 t.mem base (o + 4 * j) +
        2 ^ 32 * val32 t.mem base (o + 4 * j + 4) (k - j - 1)) = 0 := by omega
    rcases Nat.mul_eq_zero.mp H with H | H
    · exact absurd H (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · omega

theorem loadComponent_ok {s : State} {base : Addr} {size len n out : Nat}
    (hs : Scr s base size) (ho : out + 8 * n ≤ size)
    (hp : (s.gpr .esi).toNat + len ≤ 2 ^ 32) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (loadComponent len n out) s fun t =>
      wordsVal t.mem base out n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside base out (8 * n) s.mem t.mem := by
  have hn := hs.nowrap
  have hsz := hs.size_lt
  unfold loadComponent
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => wp_addS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  have k₁ : Keeps [.ebx] s s₁ := u₀.keeps.trans u₁.keeps
  have ebx₁ : s₁.gpr .ebx = s.gpr .esi + BitVec.ofNat 32 (len - 4) := by rw [u₁.gpr, u₀.gpr]
  let P := (s.gpr .esi).setWidth 64
  refine WP.seq (wordLoop_ok (fun j t => Keeps [.eax, .ebx, .edx, .ebp] s t ∧
      t.gpr .ebx + BitVec.ofNat 32 (4 * j) = s.gpr .esi + BitVec.ofNat 32 (len - 4) ∧
      Outside base out (4 * j) s.mem t.mem ∧ ∀ i < j, w32 t.mem base (out + 4 * i) = ldWord32 s.mem P len i)
    (by omega) (by omega)
    (fun j u u' ⟨K, e, O, V⟩ ⟨hm, hr', hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr'.trans K.2.1, hw.trans K.2.2⟩,
        by rw [hg _ (by decide) (by decide), e], hm ▸ O, fun i hi => hm ▸ V i hi⟩)
    ⟨k₁.mono (by decide), (by rw [ebx₁, Nat.mul_zero, BitVec.add_zero]),
      (by rw [u₁.mem, u₀.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun j hj t ⟨K, e, O, V⟩ ej => ?_) ?_)
  · have ht := hs.of_keeps K (by decide)
    have ebx : t.gpr .ebx = s.gpr .esi + BitVec.ofNat 32 (len - 4 * (j + 1)) := ebx_at e (by omega)
    have ha : t.ea (at_ .ebx 0) = P + BitVec.ofNat 64 (len - 4 * (j + 1)) := ea_ebx ebx (by omega)
    have hrd : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 4 := by
      rw [K.2.1, K.2.2]; exact hr _ (by omega)
    have hkeep : t.mem.readW (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 =
        s.mem.readW (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 :=
      readW32_keep fun i hi => keep_of_disjoint (O.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine wp_movS (show readSrc t (.mem (at_ .ebx 0)) = some _ by
      show t.load32 _ = _; rw [ha, State.load32, ite_eq_left_iff.mpr fun h => absurd hrd h]) fun s₂ u₂ _ => ?_
    refine wp_bswap fun s₃ u₃ => ?_
    have k₃ : Keeps [.eax] t s₃ := u₂.keeps.trans u₃.keeps
    have hs₃ := ht.of_keeps k₃ (by decide)
    have ej₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [k₃.1 _ (by decide), k₃.1 _ (by decide)]; exact ej
    refine wp_storeS (hs₃.ea_at' ej₃ (d := out) (by omega)) (hs₃.write (d := out + 4 * j) (n := 4) (by omega))
      fun s₄ m₄ => wp_subS rfl fun s₅ u₅ _ => WP.block_nil ?_
    have O₂ : Outside base (out + 4 * j) 4 t.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    have k₅ : Keeps [.eax, .ebx] t s₅ := ((k₃.mono (by decide)).widen (m₄.keeps [])).widen u₅.keeps
    refine ⟨⟨K.trans (k₅.mono (by decide)), ?_, ?_, fun i hi => ?_⟩, k₅.1 _ (by decide), k₅.1 _ (by decide)⟩
    · rw [u₅.gpr, m₄.gpr, k₃.1 _ (by decide)]; exact ebx_down e
    · rw [u₅.mem]; exact (O.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))
    · rw [u₅.mem]
      rcases Nat.lt_or_ge i j with h | h
      · rw [O₂.w32 (by omega) (by omega), V i h]
      · obtain rfl : i = j := by omega
        rw [m₄.mem, w32_write_self, u₃.gpr, u₂.gpr, hkeep, bswap_eq, ldWord32,
          ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  · intro t ⟨K, _, O, V⟩
    have ht := hs.of_keeps K (by decide)
    refine WP.mono (zeroPad_ok ht (o := out + 4 * (len / 4)) (k := 2 * n - len / 4) (by omega))
      fun u ⟨e, K₂, O₂⟩ => ⟨?_, K.trans (K₂.mono (by decide)), ?_⟩
    · rw [wordsVal_eq_val32]
      refine VG.Proof.Weierstrass.val32_eq_ofBytes_len _ _ _ _ out (2 * n) len h4 (by omega) fun j hj => ?_
      rcases Nat.lt_or_ge j (len / 4) with h | h
      · rw [O₂.w32 (by omega) (by omega), V j h]
      · rw [show j = len / 4 + (j - len / 4) by omega, show out + 4 * (len / 4 + (j - len / 4)) = out + 4 * (len / 4) + 4 * (j - len / 4) by omega, e _ (by omega), ldWord32,
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    · exact (O.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))

theorem storeComponent_ok {s : State} {base : Addr} {size len n input : Nat}
    (hs : Scr s base size) (accepted : Bool)
    (hc : s.gpr .ecx = if accepted then BitVec.allOnes 32 else 0)
    (ha : input + 8 * n ≤ size) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hp : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ len → InRegions s.wr ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 e) k)
    (hd : Region.Disjoint ⟨off base input, 8 * n⟩ ⟨(s.gpr .esi).setWidth 64, len⟩) :
    WP isa (storeComponent len input) s fun t =>
      Spec.Rsa.bytesAt t.mem ((s.gpr .esi).setWidth 64) len =
        (if accepted then Spec.Dsa.encodeBE len (wordsVal s.mem base input n) else List.replicate len 0) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside ((s.gpr .esi).setWidth 64) 0 len s.mem t.mem := by
  have hn := hs.nowrap
  have hsz := hs.size_lt
  unfold storeComponent
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => wp_addS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  have k₁ : Keeps [.ebx] s s₁ := u₀.keeps.trans u₁.keeps
  have ebx₁ : s₁.gpr .ebx = s.gpr .esi + BitVec.ofNat 32 (len - 4) := by rw [u₁.gpr, u₀.gpr]
  let P := (s.gpr .esi).setWidth 64
  let mask : BitVec 32 := if accepted then BitVec.allOnes 32 else 0
  have hP : P.toNat + len ≤ 2 ^ 64 := by
    show ((s.gpr .esi).setWidth 64).toNat + len ≤ 2 ^ 64
    rw [BitVec.toNat_setWidth]; have := (s.gpr .esi).isLt; omega
  refine wordLoop_ok (fun j t => Keeps [.eax, .ebx, .edx, .ebp] s t ∧
      t.gpr .ebx + BitVec.ofNat 32 (4 * j) = s.gpr .esi + BitVec.ofNat 32 (len - 4) ∧
      Outside P (len - 4 * j) (4 * j) s.mem t.mem ∧
      ∀ i < j, t.mem.readW (P + BitVec.ofNat 64 (len - 4 * (i + 1))) 32 =
        byteRev32 (s.mem.readW (off base (input + 4 * i)) 32 &&& mask))
    (by omega) (by omega)
    (fun j u u' ⟨K, e, O, V⟩ ⟨hm, hr', hw', hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr'.trans K.2.1, hw'.trans K.2.2⟩,
        by rw [hg _ (by decide) (by decide), e], hm ▸ O, fun i hi => hm ▸ V i hi⟩)
    ⟨k₁.mono (by decide), (by rw [ebx₁, Nat.mul_zero, BitVec.add_zero]),
      (by rw [u₁.mem, u₀.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun j hj t ⟨K, e, O, V⟩ ej => ?_) (fun u ⟨K, _, O, V⟩ => ⟨?_, K, ?_⟩)
  · have ht := hs.of_keeps K (by decide)
    have ebx : t.gpr .ebx = s.gpr .esi + BitVec.ofNat 32 (len - 4 * (j + 1)) := ebx_at e (by omega)
    have hword : t.mem.readW (off base (input + 4 * j)) 32 = s.mem.readW (off base (input + 4 * j)) 32 := by
      show t.mem.readW (base + BitVec.ofNat 64 (input + 4 * j)) 32 = s.mem.readW (base + BitVec.ofNat 64 (input + 4 * j)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => VG.Proof.Weierstrass.keep_of_disjoint' (O.mono (Nat.zero_le _) (by omega)) hd
        (by omega) (by omega) (by omega)
    refine wp_movS (readSrc_at' ht ej (d := input) (by omega)) fun s₂ u₂ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
    refine wp_bswap fun s₄ u₄ => ?_
    have k₄ : Keeps [.eax] t s₄ := (u₂.keeps.trans u₃.keeps).trans u₄.keeps
    have ha₄ : s₄.ea (at_ .ebx 0) = P + BitVec.ofNat 64 (len - 4 * (j + 1)) :=
      ea_ebx (by rw [k₄.1 _ (by decide), ebx]) (by omega)
    have hw₄ : InRegions s₄.wr (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 4 := by
      rw [k₄.2.2, K.2.2]; exact hw _ _ (by omega)
    refine wp_storeS ha₄ hw₄ fun s₅ m₅ => wp_subS rfl fun s₆ u₆ _ => WP.block_nil ?_
    have v₄ : s₄.gpr .eax = byteRev32 (s.mem.readW (off base (input + 4 * j)) 32 &&& mask) := by
      rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), K.1 _ (by decide), hc, hword, bswap_eq]
      simp only [ite_true, mask]
    have mem₄ : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have O₂ : Outside P (len - 4 * (j + 1)) 4 t.mem s₅.mem := by
      rw [m₅.mem, mem₄]; exact writeW32_outside _ _ _ (by omega)
    have k₆ : Keeps [.eax, .ebx] t s₆ := ((k₄.mono (by decide)).widen (m₅.keeps [])).widen u₆.keeps
    refine ⟨⟨K.trans (k₆.mono (by decide)), ?_, ?_, fun i hi => ?_⟩, k₆.1 _ (by decide), k₆.1 _ (by decide)⟩
    · rw [u₆.gpr, m₅.gpr, k₄.1 _ (by decide)]; exact ebx_down e
    · rw [u₆.mem]; exact (O.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))
    · rw [u₆.mem]
      rcases Nat.lt_or_ge i j with h | h
      · rw [m₅.mem, mem₄, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), V i h]
      · obtain rfl : i = j := by omega
        rw [m₅.mem, Mem.readW_writeW_self32, v₄]
  · rw [← toBytes_encodeBE, wordsVal_eq_val32]
    refine VG.Proof.Weierstrass.bytesAt_eq_toBytes_len32 _ _ _ _ accepted (N := 2 * n) (by omega)
      (fun j hj hj4 => V j (by omega)) fun k _ hk1 hk2 => absurd hk2 (by omega)
  · rw [show len - 4 * (len / 4) = 0 by omega, show 4 * (len / 4) = len by omega] at O; exact O

end VG.Proof.Dsa.X86
