module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Pointer
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.RsaKeyGen

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
/-! # The distance to `p` at the run-time width: the subtractions and the select -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/Difference.lean`, which only this module imported.
section

/-! # Selecting the unborrowed difference computes the required absolute value -/

section
namespace VG.Proof.RsaKeyGen

theorem absDiff_select {c p d e r : Nat} {borrow reverse : Bool}
    (forward : d + p = c + r * borrow.toNat)
    (backward : e + c = p + r * reverse.toNat)
    (dBound : d < r) (eBound : e < r) :
    (if borrow then e else d) = Spec.RsaKeyGen.absDiff c p := by
  cases borrow <;> cases reverse <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
      Bool.false_eq_true, ↓reduceIte] at forward backward ⊢ <;>
    unfold Spec.RsaKeyGen.absDiff <;> split <;> omega

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.Mont.X86 (sc at_)

/-- In the distance check's frame at `q`: the workspace pointer saved at its
bottom, the frame apart from the workspace. -/
structure Framed (W : Addr) (L w : Nat) (q : BitVec 32) (s : State) : Prop where
  space : Space W L w s
  stack : VG.Proof.RsaKeyGen.X86.Sieve.StackContext q s
  apart : (⟨W, L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩
  saved : s.mem.readW (off (q.setWidth 64) 0) 32 = BitVec.ofNat 32 W.toNat

/-- The arrays a check uses: 0, 2, 3 and 4. -/
def Arrays (j : Nat) : Prop := j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 4

theorem Arrays.fit {W : Addr} {L w : Nat} {s : State} (S : Space W L w s) {j : Nat} (A : Arrays j) :
    slot w j + 8 * w ≤ L ∧ 256 ≤ slot w j ∧ j < 32 := by
  have space := S.space
  unfold slot stride VG.Impl.Bignum.hdrBytes at space ⊢
  rcases A with rfl | rfl | rfl | rfl <;> omega

theorem Arrays.apart {w : Nat} {i j : Nat} (I : Arrays i) (J : Arrays j) (different : i ≠ j) :
    slot w i + 4 * (2 * w) ≤ slot w j ∨ slot w j + 4 * (2 * w) ≤ slot w i := by
  unfold slot stride VG.Impl.Bignum.hdrBytes
  rcases I with rfl | rfl | rfl | rfl <;> rcases J with rfl | rfl | rfl | rfl <;> first | omega | exact absurd rfl different

/-- Workspace writes beyond the header keep the frame. -/
theorem Framed.keepOutside {W : Addr} {L w : Nat} {q : BitVec 32} {s t : State} (F : Framed W L w q s)
    {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs) {d n : Nat}
    (O : Outside W d n s.mem t.mem) (header : 8 ≤ d) (fit : d + n ≤ L) : Framed W L w q t := by
  have nowrap := F.space.scratch.nowrap
  have Fr := VG.Proof.Bignum.outside_frame O (by omega)
  refine ⟨F.space.keep K edi esp (BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega)) (by omega))),
    F.stack.keep K esp, F.apart, ?_⟩
  rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) ?_ ?_ (by decide)]
  · exact F.saved
  · exact Offset.contains_base _ (by decide) (by decide)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact (F.apart.sub_left (Offset.sub_base W fit)).symm

theorem Framed.keepMem {W : Addr} {L w : Nat} {q : BitVec 32} {s t : State} (F : Framed W L w q s)
    {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs) (M : t.mem = s.mem) :
    Framed W L w q t :=
  ⟨F.space.keepMem K edi esp M, F.stack.keep K esp, F.apart, by rw [M]; exact F.saved⟩

theorem Framed.edi_value {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) :
    s.gpr .edi = BitVec.ofNat 32 W.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := F.space.scratch.nowrap
  have := F.space.header
  rw [F.space.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The frame again once `edi` is back at the workspace. -/
theorem Framed.rebuild {W : Addr} {L w : Nat} {q : BitVec 32} {s t : State} (F : Framed W L w q s)
    {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs) (edi : t.gpr .edi = s.gpr .edi) {d n : Nat}
    (O : Outside W d n s.mem t.mem) (header : 8 ≤ d) (fit : d + n ≤ L) : Framed W L w q t := by
  have nowrap := F.space.scratch.nowrap
  have Fr := VG.Proof.Bignum.outside_frame O (by omega)
  have Sc : Scr t W L := ⟨by rw [edi]; exact F.space.scratch.edi, by rw [K.2.2]; exact F.space.scratch.wr,
    nowrap, by rw [K.1 .esp esp]; exact F.space.scratch.stk⟩
  refine ⟨⟨Sc, F.space.width, F.space.widthBound, F.space.space,
    (BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega)) (by omega))).trans F.space.len⟩,
    ⟨F.stack.ws.of_keeps K, (K.1 .esp esp).trans F.stack.sp⟩, F.apart, ?_⟩
  rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) ?_ ?_ (by decide)]
  · exact F.saved
  · exact Offset.contains_base _ (by decide) (by decide)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact (F.apart.sub_left (Offset.sub_base W fit)).symm

theorem subSetup_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s)
    {out a b : Nat} (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) :
    WP isa (.block (lenPtr .ebp .edx a ++ lenPtr .ebx .edx b ++ lenPtr .eax .edx out ++
      ([.mov .edx (.mem (sc 4)), .mov .edi (.reg .eax), .mov .ecx (.imm 0)] : List Instr))) s fun u =>
      PtrAt u W .ebp (slot w a) ∧ PtrAt u W .ebx (slot w b) ∧ PtrAt u W .edi (slot w out) ∧
      (u.gpr .edx).toNat = 4 * (2 * w) ∧ u.gpr .ecx = cmask false ∧ u.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u := by
  have S := F.space
  have bound := S.widthBound
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (lenPtr_ok S a (Ia.fit S).2.2 (by decide : Reg.edx ≠ .ebp) (by decide) (by decide)) fun s₁ ⟨Pa, M₁, K₁⟩ => ?_)))
  have S₁ := S.keepMem K₁ (by decide) (by decide) M₁
  refine WP.mono (lenPtr_ok S₁ b (Ib.fit S).2.2 (by decide : Reg.edx ≠ .ebx) (by decide) (by decide))
    fun s₂ ⟨Pb, M₂, K₂⟩ => ?_
  have S₂ := S₁.keepMem K₂ (by decide) (by decide) M₂
  refine WP.mono (lenPtr_ok S₂ out (Io.fit S).2.2 (by decide : Reg.edx ≠ .eax) (by decide) (by decide))
    fun s₃ ⟨Po, M₃, K₃⟩ => ?_
  have S₃ := S₂.keepMem K₃ (by decide) (by decide) M₃
  refine wp_movS S₃.lenRead fun s₄ U₄ _ => wp_movS rfl fun s₅ U₅ _ => wp_movS rfl fun u U _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, U.gpr, by rw [U.mem, U₅.mem, U₄.mem, M₃, M₂, M₁], ?_⟩
  · rw [PtrAt, U.other .ebp (by decide), U₅.other .ebp (by decide), U₄.other .ebp (by decide),
      K₃.1 .ebp (by decide), K₂.1 .ebp (by decide)]; exact Pa
  · rw [PtrAt, U.other .ebx (by decide), U₅.other .ebx (by decide), U₄.other .ebx (by decide),
      K₃.1 .ebx (by decide)]; exact Pb
  · rw [PtrAt, U.other .edi (by decide), U₅.gpr, U₄.other .eax (by decide)]; exact Po
  · rw [U.other .edx (by decide), U₅.other .edx (by decide), U₄.gpr, BitVec.toNat_ofNat]; omega
  · exact (((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).widen U₄.keeps).widen
      U₅.keeps).widen U.keeps

/-- A subtraction's pointers, count and borrow set from the frame at `s`. -/
structure SubSet (W : Addr) (L w : Nat) (q : BitVec 32) (out a b : Nat) (s u : State) : Prop where
  framed : Framed W L w q s
  aPtr : PtrAt u W .ebp (slot w a)
  bPtr : PtrAt u W .ebx (slot w b)
  outPtr : PtrAt u W .edi (slot w out)
  count : (u.gpr .edx).toNat = 4 * (2 * w)
  mask : u.gpr .ecx = cmask false
  mem : u.mem = s.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u

/-- The subtraction's loop and `edi` restored. -/
theorem subRest_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s u : State} {out a b : Nat}
    (H : SubSet W L w q out a b s u) (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) (oa : out ≠ a) (ob : out ≠ b) :
    WP isa (.seq subLoop (.block [.mov .edi (.mem (at_ .esp 0))])) u fun t =>
      (∃ c : Bool, t.gpr .ecx = cmask c ∧ val32 t.mem W (slot w out) (2 * w) + val32 s.mem W (slot w b) (2 * w) =
        val32 s.mem W (slot w a) (2 * w) + 2 ^ (32 * (2 * w)) * c.toNat) ∧
      Outside W (slot w out) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Framed W L w q t := by
  have F := H.framed
  have S := F.space
  have width := S.width
  have ⟨fo, lo, _⟩ := Io.fit S
  have ⟨fa, _, _⟩ := Ia.fit S
  have ⟨fb, _, _⟩ := Ib.fit S
  have Mu := H.mem
  have Ku := H.keeps
  have hw : Ws u W L := S.ws.of_keeps Ku
  have hda : slot w out ≤ slot w a ∨ slot w a + 4 * (2 * w) ≤ slot w out := by
    rcases Arrays.apart Io Ia oa with h | h
    · exact Or.inl (Nat.le_trans (Nat.le_add_right _ _) h)
    · exact Or.inr h
  have hdm : slot w out ≤ slot w b ∨ slot w b + 4 * (2 * w) ≤ slot w out := by
    rcases Arrays.apart Io Ib ob with h | h
    · exact Or.inl (Nat.le_trans (Nat.le_add_right _ _) h)
    · exact Or.inr h
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok hw (a := slot w a) (m := slot w b)
    (d := slot w out) (N := 2 * w) (by omega) (by omega) (by omega) (by omega) hda hdm H.aPtr H.bPtr H.outPtr
    H.count H.mask) fun v ⟨Ov, _, ⟨c, mask, value⟩, Kv⟩ => ?_)
  rw [Mu] at Ov value
  have Kuv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s v := Ku.trans Kv
  have stack := F.stack.keep Kuv (by decide)
  have Fr := VG.Proof.Bignum.outside_frame Ov (by have := S.scratch.nowrap; omega)
  have saved : v.mem.readW (off (q.setWidth 64) 0) 32 = BitVec.ofNat 32 W.toNat := by
    rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) (Offset.contains_base _ (by decide) (by decide)) (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact (F.apart.sub_left (Offset.sub_base W (by omega))).symm) (by decide)]
    exact F.saved
  refine wp_movS (stack.read 0 (by decide)) fun t T _ => WP.block_nil ?_
  have edi : t.gpr .edi = s.gpr .edi := by rw [T.gpr, saved, F.edi_value]
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
    refine ⟨fun r mem => ?_, (Kuv.widen T.keeps).2⟩
    by_cases h : r = .edi
    · subst h; exact edi
    · rw [T.other r h]; exact Kuv.1 r (by simp_all)
  have Ot : Outside W (slot w out) (4 * (2 * w)) s.mem t.mem := by rw [T.mem]; exact Ov
  refine ⟨⟨c, by rw [T.other .ecx (by decide)]; exact mask, by rw [T.mem]; exact value⟩, Ot, Kt,
    F.rebuild Kt (by decide) edi Ot (by omega) (by omega)⟩

/-- `[out] := [a] − [b]`, its borrow a mask in `ecx`, and the frame again. -/
theorem sub_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s)
    {out a b : Nat} (Io : Arrays out) (Ia : Arrays a) (Ib : Arrays b) (oa : out ≠ a) (ob : out ≠ b) :
    WP isa (sub out a b) s fun t =>
      (∃ c : Bool, t.gpr .ecx = cmask c ∧ val32 t.mem W (slot w out) (2 * w) + val32 s.mem W (slot w b) (2 * w) =
        val32 s.mem W (slot w a) (2 * w) + 2 ^ (32 * (2 * w)) * c.toNat) ∧
      Outside W (slot w out) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Framed W L w q t := by
  unfold sub
  exact WP.seq (WP.mono (subSetup_ok F Io Ia Ib) fun u ⟨Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩ =>
    subRest_ok ⟨F, Pa, Pb, Po, cnt, ecx0, Mu, Ku⟩ Io Ia Ib oa ob)

theorem arrays0 : Arrays 0 := Or.inl rfl
theorem arrays2 : Arrays 2 := Or.inr (Or.inl rfl)
theorem arrays3 : Arrays 3 := Or.inr (Or.inr (Or.inl rfl))
theorem arrays4 : Arrays 4 := Or.inr (Or.inr (Or.inr rfl))

/-- The select's pointers, count and mask set from the frame at `s`. -/
structure SelectSet (W : Addr) (L w : Nat) (q : BitVec 32) (k : Bool) (s u : State) : Prop where
  framed : Framed W L w q s
  fromPtr : PtrAt u W .ebp (slot w 3)
  toPtr : PtrAt u W .ebx (slot w 2)
  count : (u.gpr .edi).toNat = 4 * (2 * w)
  mask : u.gpr .ecx = cmask k
  mem : u.mem = s.mem
  keeps : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s u

theorem selectSetup_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) {k : Bool}
    (mask : s.gpr .esi = cmask k) :
    WP isa (.block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++
      ([.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)] : List Instr))) s (SelectSet W L w q k s) := by
  have S := F.space
  have width := S.width
  have bound := S.widthBound
  refine WP.block_append (WP.block_append (WP.mono
    (lenPtr_ok S 3 (by decide) (by decide : Reg.edx ≠ .ebp) (by decide) (by decide)) fun s₁ ⟨P₃, M₁, K₁⟩ => ?_))
  have S₁ := S.keepMem K₁ (by decide) (by decide) M₁
  refine WP.mono (lenPtr_ok S₁ 2 (by decide) (by decide : Reg.edx ≠ .ebx) (by decide) (by decide))
    fun s₂ ⟨P₂, M₂, K₂⟩ => ?_
  have S₂ := S₁.keepMem K₂ (by decide) (by decide) M₂
  refine wp_movS S₂.lenRead fun s₃ U₃ _ => wp_movS rfl fun u U _ => WP.block_nil ?_
  refine ⟨F, ?_, ?_, ?_, ?_, by rw [U.mem, U₃.mem, M₂, M₁],
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).widen U₃.keeps).widen U.keeps⟩
  · rw [PtrAt, U.other .ebp (by decide), U₃.other .ebp (by decide), K₂.1 .ebp (by decide)]; exact P₃
  · rw [PtrAt, U.other .ebx (by decide), U₃.other .ebx (by decide)]; exact P₂
  · rw [U.other .edi (by decide), U₃.gpr, BitVec.toNat_ofNat]; omega
  · rw [U.gpr, U₃.other .esi (by decide), K₂.1 .esi (by decide), K₁.1 .esi (by decide), mask]

/-- The select's loop and `edi` restored. -/
theorem selectRest_ok {W : Addr} {L w : Nat} {q : BitVec 32} {k : Bool} {s u : State}
    (H : SelectSet W L w q k s u) :
    WP isa (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))])) u
      fun t => val32 t.mem W (slot w 2) (2 * w) =
          (if k then val32 s.mem W (slot w 3) (2 * w) else val32 s.mem W (slot w 2) (2 * w)) ∧
        Outside W (slot w 2) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
        Framed W L w q t := by
  have F := H.framed
  have S := F.space
  have width := S.width
  have ⟨f2, l2, _⟩ := arrays2.fit S
  have ⟨f3, l3, _⟩ := arrays3.fit S
  have Ku := H.keeps
  have Mu := H.mem
  have apart : slot w 2 + 4 * (2 * w) ≤ slot w 3 ∨ slot w 3 + 4 * (2 * w) ≤ slot w 2 :=
    Arrays.apart arrays2 arrays3 (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok (S.ws.of_keeps Ku) k (x := slot w 3)
    (d := slot w 2) (N := 2 * w) (by omega) (by omega) (by omega) apart H.fromPtr H.toPtr H.count H.mask)
    fun v ⟨Ov, value, _, Kv⟩ => ?_)
  rw [Mu] at Ov value
  have Kuv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s v := (Ku.mono (by decide)).trans (Kv.mono (by decide))
  have stack := F.stack.keep Kuv (by decide)
  have Fr := VG.Proof.Bignum.outside_frame Ov (by have := S.scratch.nowrap; omega)
  have saved : v.mem.readW (off (q.setWidth 64) 0) 32 = BitVec.ofNat 32 W.toNat := by
    rw [Fr.readW (r := ⟨q.setWidth 64, 20⟩) (Offset.contains_base _ (by decide) (by decide)) (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact (F.apart.sub_left (Offset.sub_base W (by omega))).symm) (by decide)]
    exact F.saved
  refine wp_movS (stack.read 0 (by decide)) fun t T _ => WP.block_nil ?_
  have edi : t.gpr .edi = s.gpr .edi := by rw [T.gpr, saved, F.edi_value]
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
    refine ⟨fun r mem => ?_, (Kuv.widen T.keeps).2⟩
    by_cases h : r = .edi
    · subst h; exact edi
    · rw [T.other r h]; exact Kuv.1 r (by simp_all)
  have Ot : Outside W (slot w 2) (4 * (2 * w)) s.mem t.mem := by rw [T.mem]; exact Ov
  exact ⟨by rw [T.mem]; exact value, Ot, Kt, F.rebuild Kt (by decide) edi Ot (by omega) (by omega)⟩

/-- `[2] := [3]` where the mask `ecx` (saved in `esi`) is all ones, and the frame again. -/
theorem select_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) {k : Bool}
    (mask : s.gpr .esi = cmask k) :
    WP isa (.seq (.block (lenPtr .ebp .edx 3 ++ lenPtr .ebx .edx 2 ++
      ([.mov .edi (.mem (sc 4)), .mov .ecx (.reg .esi)] : List Instr))) (.seq selectLoop (.block [.mov .edi (.mem (at_ .esp 0))]))) s
      fun t => val32 t.mem W (slot w 2) (2 * w) =
          (if k then val32 s.mem W (slot w 3) (2 * w) else val32 s.mem W (slot w 2) (2 * w)) ∧
        Outside W (slot w 2) (4 * (2 * w)) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
        Framed W L w q t :=
  WP.seq (WP.mono (selectSetup_ok F mask) fun _ H => selectRest_ok H)

/-- `|c − p|` into array 2, through array 3. -/
theorem difference_ok {W : Addr} {L w : Nat} {q : BitVec 32} {s : State} (F : Framed W L w q s) :
    WP isa difference s fun t =>
      val32 t.mem W (slot w 2) (2 * w) =
        Spec.RsaKeyGen.absDiff (val32 s.mem W (slot w 0) (2 * w)) (val32 s.mem W (slot w 4) (2 * w)) ∧
      Outs W [(slot w 2, 4 * (2 * w)), (slot w 3, 4 * (2 * w))] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Framed W L w q t := by
  have S := F.space
  have nowrap := S.scratch.nowrap
  have ⟨f0, l0, _⟩ := arrays0.fit S
  have ⟨f2, l2, _⟩ := arrays2.fit S
  have ⟨f3, l3, _⟩ := arrays3.fit S
  have ⟨f4, l4, _⟩ := arrays4.fit S
  unfold difference
  refine WP.seq (WP.mono (sub_ok F arrays2 arrays0 arrays4 (by decide) (by decide))
    fun u ⟨⟨borrow, mask, forward⟩, Ou, Ku, Fu⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  have Fv := Fu.keepMem V.keeps (by decide) (by decide) V.mem
  refine WP.seq (WP.mono (sub_ok Fv arrays3 arrays4 arrays0 (by decide) (by decide))
    fun z ⟨⟨reverse, _, backward⟩, Oz, Kz, Fz⟩ => ?_)
  have maskZ : z.gpr .esi = cmask borrow := by rw [Kz.1 .esi (by decide), V.gpr, mask]
  refine WP.mono (select_ok Fz maskZ) fun t ⟨value, Ot, Kt, Ft⟩ => ?_
  have a02 := Arrays.apart arrays0 arrays2 (w := w) (by decide)
  have a42 := Arrays.apart arrays4 arrays2 (w := w) (by decide)
  have a03 := Arrays.apart arrays0 arrays3 (w := w) (by decide)
  have a43 := Arrays.apart arrays4 arrays3 (w := w) (by decide)
  have a23 := Arrays.apart arrays2 arrays3 (w := w) (by decide)
  have aSame : val32 v.mem W (slot w 0) (2 * w) = val32 s.mem W (slot w 0) (2 * w) := by
    rw [V.mem]; exact Ou.val32 a02 (by omega)
  have bSame : val32 v.mem W (slot w 4) (2 * w) = val32 s.mem W (slot w 4) (2 * w) := by
    rw [V.mem]; exact Ou.val32 a42 (by omega)
  rw [aSame, bSame] at backward
  have dSame : val32 z.mem W (slot w 2) (2 * w) = val32 u.mem W (slot w 2) (2 * w) := by
    rw [Oz.val32 (by rcases a23 with h | h; exact Or.inl h; exact Or.inr h) (by omega), V.mem]
  have values : val32 t.mem W (slot w 2) (2 * w) =
      if borrow then val32 z.mem W (slot w 3) (2 * w) else val32 u.mem W (slot w 2) (2 * w) := by
    rw [value]
    cases borrow
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact dSame
    · rfl
  have K₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := (Ku.mono (by decide)).widen V.keeps
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := (K₁.trans (Kz.mono (by decide))).trans (Kt.mono (by decide))
  refine ⟨values.trans (VG.Proof.RsaKeyGen.absDiff_select forward backward (val32_lt ..) (val32_lt ..)), ?_,
    K₂, Ft⟩
  have O₁ : Outs W [(slot w 2, 4 * (2 * w)), (slot w 3, 4 * (2 * w))] s.mem v.mem := by
    rw [V.mem]; exact Outs.of_outside Ou (by simp)
  have O₂ : Outs W [(slot w 2, 4 * (2 * w)), (slot w 3, 4 * (2 * w))] v.mem z.mem :=
    Outs.of_outside Oz (by simp)
  exact (O₁.trans O₂).trans (Outs.of_outside Ot (by simp))

end VG.Proof.RsaKeyGen.X86.FrontRt
