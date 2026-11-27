module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.SelectX
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.Chain
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift

/-! ### `Rsa.X86.InvBatchRt.Ptr`, which only this module used -/

section

/-! # Pointers and counts of the run-time-width batch

`Slots`: the header words `init` fills, the cached arrays' addresses and the
bytes of `n` words. `ptr_ok`: a pointer at a `Ref`,
`offset w arr + 4 n · half + byte` for arrays of `w` words and halves of `n` (by
default `w / 2`, the modulus's primes; prime recovery's GCD takes `n = w / 2 + 1`);
`nBytes_ok`, `nBytesLess_ok` and `wBytes_ok`: the bytes of `n + e`, `n - 1` and
`2 n` words.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (arr)

/-- A `Ref`'s offset in the working space, for arrays of `w` words and halves of `n`. -/
def rv (w : Nat) (x : Ref) (n : Nat := w / 2) : Nat :=
  VG.Impl.Rsa.X86.InvBatchRt.offset w x.arr + x.half * (4 * n) + x.byte

/-- A `Ref` in an array's first half does not depend on the halves' size. -/
theorem rv_h0 {w : Nat} {x : Ref} (hx : x.half = 0) (n n' : Nat) : rv w x n = rv w x n' := by
  simp only [rv, hx, Nat.zero_mul]

theorem offset_eq (w j : Nat) : VG.Impl.Rsa.X86.InvBatchRt.offset w j = arr w j := by
  simp only [VG.Impl.Rsa.X86.InvBatchRt.offset, arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr]
  rw [show 4 * (w + 2) = 4 * w + 8 by omega_using []]

/-- The header words `init` fills: each cached array's address, and `4 n`. -/
structure Slots (m : Mem) (B : Addr) (w : Nat) (n : Nat := w / 2) : Prop where
  addr : ∀ j d, slot j = some d → w32 m B d = (B.toNat + VG.Impl.Rsa.X86.InvBatchRt.offset w j) % 2 ^ 32
  half : w32 m B halfSlot = 4 * n
  small : 4 * n < 2 ^ 32
  pos : 0 < n

theorem Slots.halfW {m : Mem} {B : Addr} {w n : Nat} (h : Slots m B w n) :
    m.readW (off B halfSlot) 32 = BitVec.ofNat 32 (4 * n) :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.small]; exact h.half)

theorem slot_le {j d : Nat} (h : slot j = some d) : slotBase ≤ d ∧ d + 4 ≤ halfSlot := by
  simp only [slot, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  have := List.idxOf?_eq_some_iff.mp hi
  obtain hl : i < 11 := by simpa [cached] using this.1
  simp only [slotBase, halfSlot]; omega_using [hl]

variable {L : Lay} {B : Addr} {Z len N w n : Nat} {is : List Instr} {s : State} {Q : State → Prop}

/-- `r += t`, `j` times. -/
theorem addsReg_ok {r t : Reg} (hrt : r ≠ t) (j : Nat) :
    ∀ {s : State}, (∀ u, Keeps [r] s u → u.mem = s.mem → u.gpr r = s.gpr r + BitVec.ofNat 32 (j * (s.gpr t).toNat) →
      WP isa (.block is) u Q) →
    WP isa (.block (List.replicate j (.alu .add r (.reg t)) ++ is)) s Q := by
  induction j with
  | zero => intro s k; exact k s (Keeps.refl _ _) rfl (by simp)
  | succ j ih =>
    intro s k
    rw [List.replicate_succ, List.cons_append]
    refine wp_addS rfl fun s₁ U₁ _ => ?_
    obtain et : s₁.gpr t = s.gpr t := U₁.other _ (Ne.symm hrt)
    refine ih fun u K m e => k u (U₁.keeps.trans K) (m.trans U₁.mem) ?_
    rw [e, U₁.gpr, et, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.succ_mul]
    generalize j * (s.gpr t).toNat = J
    omega_using []

/-- `ptr r x t`: `r` at `x` (`r` may be `edi` only for a `Ref` with no `n`-word steps). -/
theorem ptr_ok {r t : Reg} {x : Ref} (h : RtWs L s B Z len N) (hsl : Slots s.mem B (kw len) n)
    (hz : halfSlot + 4 ≤ Z) (hrt : r ≠ t) (hte : t ≠ .edi) (hrs : r ≠ .esp) (hts : t ≠ .esp)
    (hre : r = .edi → x.half = 0)
    (hb : rv (kw len) x n < 2 ^ 32)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (rv (kw len) x n) → WP isa (.block is) u Q) :
    WP isa (.block (ptr L r x t ++ is)) s Q := by
  obtain hw := kw_bound h.lenLe
  have hs := h.ws.workspace
  have nw := hs.nowrap
  obtain ha : arr (kw len) x.arr < 2 ^ 32 := by
    have := offset_eq (kw len) x.arr; simp only [rv] at hb; omega
  simp only [ptr, List.append_assoc]
  -- The array's address.
  obtain base : ∀ {is' : List Instr} {Q' : State → Prop}, (∀ v, Keeps [r, t] s v → v.mem = s.mem →
      PtrAt v B r (arr (kw len) x.arr) → WP isa (.block is') v Q') →
      WP isa (.block ((match slot x.arr with
        | some d => [.mov r (.mem (sc d))]
        | none => arrPtr L r x.arr t) ++ is')) s Q' := by
    intro is' Q' k'
    split
    · next d hd =>
      have := slot_le hd
      rw [List.cons_append, List.nil_append]
      refine wp_movS (readSrc_sc hs (d := d) (by omega_using [hz, this])) fun v V _ => k' v (V.keeps.mono (by simp)) V.mem ?_
      rw [PtrAt, V.gpr, ← offset_eq]; exact hsl.addr _ _ hd
    · exact arrPtr_ok (lenSrc h) h.lenLe h.edi hrt hte ha fun v V m p _ => k' v V m p
  refine base fun v V mv pv => ?_
  -- The `n`-word steps.
  obtain half : ∀ {is' : List Instr} {Q' : State → Prop}, (∀ u, Keeps [r, t] s u → u.mem = s.mem →
      PtrAt u B r (arr (kw len) x.arr + x.half * (4 * n)) → WP isa (.block is') u Q') →
      WP isa (.block ((if x.half = 0 then [] else .mov t (.mem (sc halfSlot)) ::
        List.replicate x.half (.alu .add r (.reg t))) ++ is')) v Q' := by
    intro is' Q' k'
    by_cases h0 : x.half = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), List.nil_append]
      exact k' v V mv (by rw [h0, Nat.zero_mul, Nat.add_zero]; exact pv)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), List.cons_append]
      obtain hsv : Scr v B Z := hs.of_keeps V
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            exact fun e => e.elim (fun e => (fun e' => h0 (hre e')) e.symm) (fun e => hte e.symm))
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => e.elim (fun e => hrs e.symm) (fun e => hts e.symm))
      refine wp_movS (readSrc_sc hsv hz) fun v₁ V₁ _ => ?_
      obtain tv : (v₁.gpr t).toNat = 4 * n := by
        rw [V₁.gpr, mv, hsl.halfW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl.small]
      obtain pv₁ : PtrAt v₁ B r (arr (kw len) x.arr) := by rw [PtrAt, V₁.other _ hrt]; exact pv
      refine addsReg_ok hrt x.half fun u U mu eu =>
        k' u (V.trans ((V₁.keeps.mono (by simp)).trans (U.mono (by simp)))) (by rw [mu, V₁.mem, mv]) ?_
      rw [PtrAt, eu, BitVec.toNat_add, pv₁, BitVec.toNat_ofNat, tv]
      generalize x.half * (4 * n) = H
      omega_using []
  refine half fun u U mu pu => ?_
  split
  · next hb0 =>
    rw [List.nil_append]
    refine k u U mu ?_
    rw [show rv (kw len) x n = arr (kw len) x.arr + x.half * (4 * n) by
      simp only [rv, offset_eq, hb0, Nat.add_zero]]
    exact pu
  · next hb0 =>
    rw [List.cons_append, List.nil_append]
    refine wp_addS rfl fun z Z' _ => k z (U.trans (Z'.keeps.mono (by simp))) (by rw [Z'.mem, mu]) ?_
    rw [PtrAt, Z'.gpr, BitVec.toNat_add, pu, rv, offset_eq, BitVec.toNat_ofNat]
    generalize x.half * (4 * n) = H at *
    omega_using []

/-- `nBytes r e`: `r = 4 n + 4 e`, the bytes of `n + e` words. -/
theorem nBytes_ok {r : Reg} {e : Nat} (hs : Scr s B Z) (hsl : Slots s.mem B w n) (hz : halfSlot + 4 ≤ Z)
    (hw : 4 * n + 16 < 2 ^ 32) (he : e ≤ 4)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 4 * n + 4 * e → WP isa (.block is) u Q) :
    WP isa (.block (nBytes r e ++ is)) s Q := by
  simp only [nBytes, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_add, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 4 * n from hsl.half,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * e) (by omega_using [he])]
  omega_using [hw, he]

/-- `nBytesLess r`: `r = 4 n - 4`, the bytes of `n - 1` words. -/
theorem nBytesLess_ok {r : Reg} (hs : Scr s B Z) (hsl : Slots s.mem B w n) (hz : halfSlot + 4 ≤ Z)
    (hw : 4 * n < 2 ^ 32) (h2 : 1 ≤ n)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 4 * n - 4 → WP isa (.block is) u Q) :
    WP isa (.block (nBytesLess r ++ is)) s Q := by
  simp only [nBytesLess, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_subS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_sub, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 4 * n from hsl.half]
  simp only [show (4 : BitVec 32).toNat = 4 from rfl]
  omega_using [hw, h2]

/-- `wBytes r`: `r = 8 n`, the bytes of `2 n` words. -/
theorem wBytes_ok {r : Reg} (hs : Scr s B Z) (hsl : Slots s.mem B w n) (hz : halfSlot + 4 ≤ Z)
    (hw : 8 * n < 2 ^ 32)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 8 * n → WP isa (.block is) u Q) :
    WP isa (.block (wBytes r ++ is)) s Q := by
  simp only [wBytes, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_add, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 4 * n from hsl.half]
  omega_using [hw]

end VG.Proof.Rsa.X86.InvBatchRt

end

end


/-! # The run-time-width batch's operations on its arrays

`Bx`: what every operation needs of a state, `KeyRt`'s `RtWs`, the header words
`Slots` and room for sixteen arrays; `Bx.keep`: kept by writes to the arrays.
`selIn_ok`, `copy_ok`, `zeros_ok`, `chainAdd_ok` and `chainSub_ok`: `KeyRt`'s
loops at `Ref`s, over `n + e` words for halves of `n` words (by default `w / 2`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (arr)

/-- The primes' words, half the modulus's. -/
abbrev nw (len : Nat) : Nat := kw len / 2

theorem kw_eq (len : Nat) : kw len = 2 * nw len := by simp only [nw, kw]; omega_using []

/-- What the batch's operations need of a state, for halves of `n` words (by default the primes'). -/
structure Bx (L : Lay) (s : State) (B : Addr) (Z len N : Nat) (n : Nat := kw len / 2) : Prop where
  ws : RtWs L s B Z len N
  slots : Slots s.mem B (kw len) n
  room : 16 ≤ N

variable {L : Lay} {B : Addr} {Z len N n : Nat}

theorem Bx.fits {s : State} (h : Bx L s B Z len N n) : VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) 16 ≤ Z := by
  have := h.ws.ws.fits
  rw [offset_eq]
  exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.room) _) this

theorem Bx.nowrap {s : State} (h : Bx L s B Z len N n) : B.toNat + Z ≤ 2 ^ 32 := h.ws.ws.workspace.nowrap

theorem Bx.halfZ {s : State} (h : Bx L s B Z len N n) : halfSlot + 4 ≤ Z := by
  have := h.fits; simp only [VG.Impl.Rsa.X86.InvBatchRt.offset, halfSlot] at *; omega_using [this]

/-- Writes to `[o, o + c)` above the header, inside the working space, keep the context. -/
theorem Bx.keep {s t : State} (h : Bx L s B Z len N n) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) {o c : Nat} (O : Outside B o c s.mem t.mem)
    (ho : 160 ≤ o) (hc : o + c ≤ Z) : Bx L t B Z len N n := by
  have nw := h.nowrap
  have e96 : halfSlot = 96 := rfl
  refine ⟨h.ws.keep K edi esp (O.mono (Nat.zero_le _) (by omega_using [hc])), ⟨fun j d hd => ?_, ?_, h.slots.small, h.slots.pos⟩, h.room⟩
  · have := slot_le hd
    rw [O.w32 (.inl (by omega_using [ho, e96, this])) (by omega_using [e96, this])]
    exact h.slots.addr j d hd
  · rw [O.w32 (.inl (by omega_using [ho, e96])) (by omega_using [e96])]
    exact h.slots.half

theorem rv_ge (w : Nat) (x : Ref) (n : Nat := w / 2) : 160 ≤ rv w x n := by
  simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset]; omega_using []

/-! ## Selections and copies -/

/-- `selIn o a (nBytes .edi e)`: `[o] = [a]` where the mask `ecx` is all ones, else kept, `n + e`
words. -/
theorem selIn_ok {s : State} (h : Bx L s B Z len N n) {o a : Ref} {e : Nat} {k : Bool}
    (hk : s.gpr .ecx = cmask k) (he : e ≤ 4)
    (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (sep : rv (kw len) o n + 4 * (n + e) ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n) :
    WP isa (selIn L o a (nBytes .edi e)) s fun t =>
      Bx L t B Z len N n ∧ Outside B (rv (kw len) o n) (4 * (n + e)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o n) (n + e) =
        (if k then val32 s.mem B (rv (kw len) a n) (n + e) else val32 s.mem B (rv (kw len) o n) (n + e)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.nowrap
  obtain hw := kw_bound h.ws.lenLe
  have hpos := h.ws.kw_pos
  obtain ke := kw_eq len
  have hZ := h.halfZ
  have hnp := h.slots.pos
  unfold selIn
  rw [show nBytes .edi e = nBytes .edi e ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [haz, hn, hnp]) fun u₁ K₁ m₁ p₁ => ?_)
  obtain h₁ : Bx L u₁ B Z len N n := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hoz, hn, hnp]) fun u₂ K₂ m₂ p₂ => ?_
  obtain h₂ : Bx L u₂ B Z len N n := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine nBytes_ok h₂.ws.ws.workspace h₂.slots hZ (by omega_using [hoz, haz, sep, hn]) he fun u K₃ m₃ c₃ => WP.block_nil ?_
  obtain K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
  obtain m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  obtain ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (selectLoopX_ok (h.ws.rt.of_keeps K) (x := rv (kw len) a n) (d := rv (kw len) o n)
    (N := n + e) k (by omega_using [haz]) (by omega_using [hoz]) sep
    (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂) (by rw [c₃]; omega_using []) ecx) fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  obtain KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  obtain O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega_using [hoz])
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  exact ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O) (rv_ge _ o n) hoz,
    by rw [U.mem]; exact O, by rw [U.mem]; exact V, K'⟩

/-- `copy o a (nBytes .edi e)`: `[o] = [a]`, `n + e` words. -/
theorem copy_ok {s : State} (h : Bx L s B Z len N n) {o a : Ref} {e : Nat} (he : e ≤ 4)
    (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (sep : rv (kw len) o n + 4 * (n + e) ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytes .edi e)) s fun t =>
      Bx L t B Z len N n ∧ Outside B (rv (kw len) o n) (4 * (n + e)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o n) (n + e) = val32 s.mem B (rv (kw len) a n) (n + e) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  obtain hu : Bx L u B Z len N n := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine WP.mono (selIn_ok hu (k := true) (by rw [U.gpr]; rfl) he hoz haz sep) fun t ⟨H, O, V, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, by rw [V, U.mem]; rfl, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

/-! ## Counts, zeroing, chains, signs -/

/-- Code that sets `r` to `4 c`, the bytes of `c` words, from the header. -/
def CountSpec (cnt : List Instr) (r : Reg) (B : Addr) (Z w c : Nat) (n : Nat := w / 2) : Prop :=
  ∀ (u : State) (is : List Instr) (Q : State → Prop), Scr u B Z → Slots u.mem B w n →
    (∀ v, Keeps [r] u v → v.mem = u.mem → (v.gpr r).toNat = 4 * c → WP isa (.block is) v Q) →
    WP isa (.block (cnt ++ is)) u Q

theorem nBytesN_spec {r : Reg} {e w : Nat} (hz : halfSlot + 4 ≤ Z) (hw : 4 * n + 16 < 2 ^ 32) (he : e ≤ 4) :
    CountSpec (nBytes r e) r B Z w (n + e) n :=
  fun _ _ _ hs hsl k => nBytes_ok hs hsl hz hw he fun v K m c => k v K m (by rw [c]; omega_using [])

theorem wBytesN_spec {r : Reg} {w : Nat} (hz : halfSlot + 4 ≤ Z) (hw : 8 * n < 2 ^ 32) :
    CountSpec (wBytes r) r B Z w (2 * n) n :=
  fun _ _ _ hs hsl k => wBytes_ok hs hsl hz hw fun v K m c => k v K m (by rw [c]; omega_using [])

theorem nBytes_spec {r : Reg} {e w : Nat} (hz : halfSlot + 4 ≤ Z) (hw : 2 * w ≤ 4104) (he : e ≤ 4)
    (hw2 : w % 2 = 0) : CountSpec (nBytes r e) r B Z w (w / 2 + e) :=
  nBytesN_spec hz (by omega) he

theorem wBytes_spec {r : Reg} {w : Nat} (hz : halfSlot + 4 ≤ Z) (hw : 2 * w ≤ 4104) (hw2 : w % 2 = 0) :
    CountSpec (wBytes r) r B Z w w := by
  have := wBytesN_spec (r := r) (B := B) (w := w) (n := w / 2) hz (by omega_using [hw])
  rwa [show 2 * (w / 2) = w by omega_using [hw2]] at this

/-- `zeros o cnt`: `[o]` zeroed, `c` words. -/
theorem zeros_ok {s : State} (h : Bx L s B Z len N n) {o : Ref} {cnt : List Instr} {c : Nat}
    (hc : CountSpec cnt .ecx B Z (kw len) c n) (hc0 : 0 < c) (hoz : rv (kw len) o n + 4 * c ≤ Z) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.zeros L o cnt) s fun t =>
      Bx L t B Z len N n ∧ Outside B (rv (kw len) o n) (4 * c) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o n) c = 0 ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hnp := h.slots.pos
  unfold VG.Impl.Rsa.X86.InvBatchRt.zeros
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hc0, hoz, hn]) fun u₁ K₁ m₁ p₁ => ?_)
  obtain h₁ : Bx L u₁ B Z len N n := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine hc u₁ _ _ h₁.ws.ws.workspace h₁.slots fun u₂ K₂ m₂ c₂ => wp_movS rfl fun u U _ => WP.block_nil ?_
  obtain K : Keeps [.eax, .ecx, .edx, .ebp] s u :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (U.keeps.mono (by decide))
  obtain m : u.mem = s.mem := by rw [U.mem, m₂, m₁]
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.ws.rt.of_keeps K) (x := rv (kw len) o n) (N := c) hc0
    hoz (by rw [PtrAt, U.other _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [U.other _ (by decide)]; exact c₂) U.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  exact ⟨h.keep (K.trans (Kt.mono (by decide))) (by decide) (by decide) O (rv_ge _ o n) hoz, O, V,
    K.trans (Kt.mono (by decide))⟩

/-- The setup of `chain`: the pointers at `a`, `b` and `o`, the count, no carry. -/
theorem chainSetup_ok {s : State} (h : Bx L s B Z len N n) {o a b : Ref} {e : Nat} (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (hbz : rv (kw len) b n + 4 * (n + e) ≤ Z) :
    WP isa (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx e ++ ptr L .edi o .eax ++
      ([.mov .ecx (.imm 0)] : List Instr))) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u ∧ u.mem = s.mem ∧ PtrAt u B .ebp (rv (kw len) a n) ∧
      PtrAt u B .ebx (rv (kw len) b n) ∧ PtrAt u B .edi (rv (kw len) o n) ∧
      (u.gpr .edx).toNat = 4 * (n + e) ∧ u.gpr .ecx = cmask false := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  obtain hw := kw_bound h.ws.lenLe
  obtain ke := kw_eq len
  have hZ := h.halfZ
  have hnp := h.slots.pos
  simp only [List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [haz, hn, hnp]) fun u₁ K₁ m₁ p₁ => ?_
  obtain h₁ : Bx L u₁ B Z len N n := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hbz, hn, hnp]) fun u₂ K₂ m₂ p₂ => ?_
  obtain h₂ : Bx L u₂ B Z len N n := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine nBytes_ok h₂.ws.ws.workspace h₂.slots hZ (by have := rv_ge (kw len) o n; omega_using [hoz, hn, this]) he fun u₃ K₃ m₃ c₃ => ?_
  obtain h₃ : Bx L u₃ B Z len N n := h₂.keep K₃ (by decide) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _)
    (rv_ge _ o n) hoz
  refine ptr_ok h₃.ws h₃.slots hZ (by decide) (by decide) (by decide) (by decide) (fun _ => hoh)
    (by omega_using [hoz, hn, hnp]) fun u₄ K₄ m₄ p₄ => wp_movS rfl fun u U _ => WP.block_nil ?_
  obtain K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u :=
    ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (U.keeps.mono (by decide))
  refine ⟨K, by rw [U.mem, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, U.gpr⟩
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂
  · rw [PtrAt, U.other _ (by decide)]; exact p₄
  · rw [U.other _ (by decide), K₄.1 _ (by decide), c₃]; omega_using []

/-- What `chain` keeps of the context, from the loop's frame and `edi` set back. -/
theorem chain_frame {s t : State} (h : Bx L s B Z len N n) {o : Ref} {c : Nat} (hoz : rv (kw len) o n + 4 * c ≤ Z)
    (O : Outside B (rv (kw len) o n) (4 * c) s.mem t.mem)
    (Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t) (edi : t.gpr .edi = BitVec.ofNat 32 B.toNat) :
    Bx L t B Z len N n ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  obtain K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) Kt
      (edi.trans (RtWs.edi_eq h.ws).symm)
  exact ⟨h.keep K' (by decide) (by decide) O (rv_ge _ o n) hoz, K'⟩

/-- `chain .sbb o a b (nBytes .edx e)`: `[o] = [a] - [b]`, `n + e` words, the borrow as a mask in `ecx`. -/
theorem chainSub_ok {s : State} (h : Bx L s B Z len N n) {o a b : Ref} {e : Nat} (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (hbz : rv (kw len) b n + 4 * (n + e) ≤ Z)
    (da : rv (kw len) o n ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n)
    (db : rv (kw len) o n ≤ rv (kw len) b n ∨ rv (kw len) b n + 4 * (n + e) ≤ rv (kw len) o n) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb o a b (nBytes .edx e)) s fun t =>
      Bx L t B Z len N n ∧ Outside B (rv (kw len) o n) (4 * (n + e)) s.mem t.mem ∧
      (∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem B (rv (kw len) o n) (n + e) + val32 s.mem B (rv (kw len) b n) (n + e) =
          val32 s.mem B (rv (kw len) a n) (n + e) + 2 ^ (32 * (n + e)) * c.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  obtain ke := kw_eq len
  unfold VG.Impl.Rsa.X86.InvBatchRt.chain
  refine WP.seq (WP.mono (chainSetup_ok h he hoh hoz haz hbz) fun u ⟨K, m, pa, pb, po, e', c⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Chain.subLoop_ok (h.ws.rt.of_keeps K) (n := n + e)
    (by have := h.slots.pos; omega_using [this]) haz hbz hoz da db pa pb po e' c) fun t ⟨O, _, V, Kt⟩ => ?_)
  rw [m] at O V
  obtain KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  obtain O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega_using [hoz])
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain ⟨F, Kr⟩ := chain_frame h hoz (by rw [U.mem]; exact O) (KK.trans (U.keeps.mono (by decide))) U.gpr
  refine ⟨F, by rw [U.mem]; exact O, ?_, Kr⟩
  obtain ⟨cb, C, V'⟩ := V
  exact ⟨cb, by rw [U.other _ (by decide)]; exact C, by rw [U.mem]; exact V'⟩

/-- `chain .adc o a b (nBytes .edx e)`: `[o] = [a] + [b]`, `n + e` words, the carry as a mask in `ecx`. -/
theorem chainAdd_ok {s : State} (h : Bx L s B Z len N n) {o a b : Ref} {e : Nat} (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (hbz : rv (kw len) b n + 4 * (n + e) ≤ Z)
    (da : rv (kw len) o n ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n)
    (db : rv (kw len) o n ≤ rv (kw len) b n ∨ rv (kw len) b n + 4 * (n + e) ≤ rv (kw len) o n) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc o a b (nBytes .edx e)) s fun t =>
      Bx L t B Z len N n ∧ Outside B (rv (kw len) o n) (4 * (n + e)) s.mem t.mem ∧
      (∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem B (rv (kw len) o n) (n + e) + 2 ^ (32 * (n + e)) * c.toNat =
          val32 s.mem B (rv (kw len) a n) (n + e) + val32 s.mem B (rv (kw len) b n) (n + e)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hpos := h.ws.kw_pos
  obtain ke := kw_eq len
  unfold VG.Impl.Rsa.X86.InvBatchRt.chain
  refine WP.seq (WP.mono (chainSetup_ok h he hoh hoz haz hbz) fun u ⟨K, m, pa, pb, po, e', c⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Chain.addLoop_ok (h.ws.rt.of_keeps K) (n := n + e)
    (by have := h.slots.pos; omega_using [this]) haz hbz hoz da db pa pb po e' c) fun t ⟨O, _, _, V, Kt⟩ => ?_)
  rw [m] at O V
  obtain KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  obtain O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega_using [hoz])
  unfold restoreEdi
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain ⟨F, Kr⟩ := chain_frame h hoz (by rw [U.mem]; exact O) (KK.trans (U.keeps.mono (by decide))) U.gpr
  refine ⟨F, by rw [U.mem]; exact O, ?_, Kr⟩
  obtain ⟨cb, C, V'⟩ := V
  exact ⟨cb, by rw [U.other _ (by decide)]; exact C, by rw [U.mem]; exact V'⟩

/-- `signOf`: `ecx` the mask of the sign of the word at `ebx`. -/
theorem signOf_ok {s : State} {W : Addr} {Y x : Nat} (hw : Ws s W Y) (p : PtrAt s W .ebx x) (hx : x + 4 ≤ Y)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax, .ecx] s u → u.mem = s.mem →
      u.gpr .ecx = (if 2 ^ 31 ≤ w32 s.mem W x then BitVec.allOnes 32 else 0) → WP isa (.block is) u Q) :
    WP isa (.block (signOf ++ is)) s Q := by
  simp only [signOf, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hw p (d := 0) (by omega_using [hx])) fun s₁ U₁ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₂ U₂ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => wp_subS rfl fun u U₄ _ => ?_
  refine k u (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))) (by rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]) ?_
  rw [U₄.gpr, U₃.gpr, U₃.other _ (by decide), U₂.gpr, U₁.gpr, Nat.add_zero]
  exact VG.Proof.Weierstrass.X86.Inv.signMask_eq _

/-- `maskAt x`: `ecx` the mask of the sign of the word at `x`. -/
theorem maskAt_ok {s : State} (h : Bx L s B Z len N n) {x : Ref} (hxz : rv (kw len) x n + 4 ≤ Z)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax, .ebx, .ecx, .edx] s u → u.mem = s.mem →
      u.gpr .ecx = (if 2 ^ 31 ≤ w32 s.mem B (rv (kw len) x n) then BitVec.allOnes 32 else 0) →
      WP isa (.block is) u Q) :
    WP isa (.block (maskAt L x ++ is)) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hnp := h.slots.pos
  simp only [maskAt, List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hxz, hn]) fun u₁ K₁ m₁ p₁ => ?_
  refine signOf_ok (h.ws.rt.of_keeps K₁) p₁ hxz fun u K₂ m₂ c₂ => k u ((K₁.mono (by decide)).trans (K₂.mono (by decide)))
    (by rw [m₂, m₁]) (by rw [c₂, m₁])

/-- `zeroWord x`: the word at `x` zeroed. -/
theorem zeroWord_ok {s : State} (h : Bx L s B Z len N n) {x : Ref} (hxz : rv (kw len) x n + 4 ≤ Z)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N n → Keeps [.eax, .ebx, .edx] s u → Outside B (rv (kw len) x n) 4 s.mem u.mem →
      w32 u.mem B (rv (kw len) x n) = 0 → WP isa (.block is) u Q) :
    WP isa (.block (zeroWord L x ++ is)) s Q := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hnp := h.slots.pos
  simp only [zeroWord, List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega_using [hxz, hn]) fun u₁ K₁ m₁ p₁ => ?_
  obtain hw₁ := h.ws.rt.of_keeps K₁
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  obtain hw₂ := hw₁.of_keeps U₁.keeps
  obtain p₂ : PtrAt s₁ B .ebx (rv (kw len) x n) := by rw [PtrAt, U₁.other .ebx (by decide)]; exact p₁
  obtain ea : s₁.ea (at_ .ebx 0) = off B (rv (kw len) x n) := by simpa using ea_ptr hw₂ p₂ (d := 0) (by omega_using [hxz])
  refine wp_storeS ea (ws_write hw₂ (by omega_using [hxz])) fun u M => ?_
  obtain K : Keeps [.eax, .ebx, .edx] s u := ((K₁.mono (by decide)).trans (U₁.keeps.mono (by decide))).trans (M.keeps _)
  obtain O : Outside B (rv (kw len) x n) 4 s.mem u.mem := by
    rw [M.mem, U₁.mem, m₁]; exact writeW32_outside _ _ _ (by omega_using [hxz, hn])
  refine k u (h.keep K (by decide) (by decide) O (rv_ge _ x n) hxz) K O ?_
  rw [M.mem, w32_write_self, U₁.gpr]; rfl

end VG.Proof.Rsa.X86.InvBatchRt
