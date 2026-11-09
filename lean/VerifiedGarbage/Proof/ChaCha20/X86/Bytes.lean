module

import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.ChaCha20.X86.Xor
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20 on x86 (32-bit): XORing keystream into data

`xorBytes` XORs the `ecx` bytes at `edx` into those at `esi`, one at a time,
advancing both (`xorLoop` reads the keystream a word at a time and uses its
low byte). `xorBytesTo` XORs the `ecx` bytes at `ebp` with those at `esi`
into those at `edx`, the destination being the source itself or apart from
it, and `xorWide` does the same 16 bytes at a time first: each byte (or 16
bytes) of the source is read before the destination's is written, so in
place the source not yet consumed is intact (`TPre.sbyte`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86.Bytes

open VG VG.X86
open VG.Impl.ChaCha20.X86 (at_ xb)
open VG.Impl.ChaCha20.X86.Xor (xorBody xorLoop xorBytes xorToBody xorToLoop xorBytesTo chunkBody xorWide)

theorem toNat_ofNat_lt32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega_arith
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

/-- The low byte of a word in memory is its first byte. -/
theorem low_byte (m : Mem) (a : Addr) : (m.readW a 32).setWidth 8 = m a := by
  have := Mem.readW_byte m a (i := 0) (by lit_omega)
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  rw [this]
  ext i hi
  simp

theorem xor_low (b : Byte) (w : BitVec 32) : (b.setWidth 32 ^^^ w).setWidth 8 = b ^^^ w.setWidth 8 := by
  ext i hi; simp

/-- `p + k`, as the code computes it, without wrapping around. -/
theorem ptr_add (x : BitVec 32) {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 0).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

theorem add_ofNat_one (x : BitVec 32) (n : Nat) :
    x + BitVec.ofNat 32 n + 1 = x + BitVec.ofNat 32 (n + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read (a
word at a time), not overlapping. -/
structure BPre (s : State) (D K : BitVec 32) (c : Nat) : Prop where
  esi : s.gpr .esi = D
  edx : s.gpr .edx = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 c
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c < 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K.setWidth 64 + BitVec.ofNat 64 k) 4
  sep : ∀ j < c, ∀ k < c, D.setWidth 64 + BitVec.ofNat 64 j ≠ K.setWidth 64 + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, and `esi`, `edx` past them;
only `eax`, `ecx`, `edx` and `esi` are written. -/
structure BPost (s : State) (D K : BitVec 32) (c : Nat) (s' : State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 c
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : BitVec 32) (c i : Nat) (s' : State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 i
  edx : s'.gpr .edx = K + BitVec.ofNat 32 i
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (c - i)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    if k < i then s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
    else s.mem (D.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

theorem D_ne {D : Addr} {c j k : Nat} (hc : c ≤ 2 ^ 32) (hj : j < c) (hk : k < c) (h : j ≠ k) :
    D + BitVec.ofNat 64 j ≠ D + BitVec.ofNat 64 k := by
  intro he
  have e : BitVec.ofNat 64 j = BitVec.ofNat 64 k := by
    have e := congrArg (· - D) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at this
  exact h this

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega_arith) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [toNat_ofNat_lt32 hx] at this
    exact h this

set_option simprocs false in
theorem byte_step {s : State} {D K : BitVec 32} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' => LInv s D K c (i + 1) s' ∧ s'.zf = some (decide (c - (i + 1) = 0)) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have ea₁ : (D + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega_arith)
  have ea₂ : (K + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = K.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega_arith)
  have cd : (⟨D.setWidth 64, c⟩ : Region).Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K.setWidth 64 + BitVec.ofNat 64 i) 4 := by
    rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.load32,
    State.store8, State.setReg, State.setFlags, Reg8.reg, h.esi, h.edx, ea₁, ea₂, i₁, i₂, o₁,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hk' : s₁.mem (K.setWidth 64 + BitVec.ofNat 64 i) = s.mem (K.setWidth 64 + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact not_contains hp.sep hi hcont
  have hd : s₁.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s.mem (D.setWidth 64 + BitVec.ofNat 64 i) := by
    rw [h.data i hi]; simp
  rw [xor_low, low_byte, hd, hk']
  have hfd : Frame [⟨D.setWidth 64, c⟩] s₁.mem (s₁.mem.writeW (D.setWidth 64 + BitVec.ofNat 64 i)
      (s.mem (D.setWidth 64 + BitVec.ofNat 64 i) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 i))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have hsub : BitVec.ofNat 32 (c - i) - 1 = BitVec.ofNat 32 (c - (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by omega_arith)]; simp; omega_arith),
      toNat_ofNat_lt32 (by omega_arith), toNat_ofNat_lt32 (by omega_arith)]
    simp; omega_arith
  refine ⟨⟨?esi, ?edx, ?ecx, fun r h₁ h₂ h₃ h₄ => ?_, h.rd, h.wr, fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  case esi | edx | ecx => simp (config := {decide := true}) only [ite_true, ite_false, h.ecx, hsub, add_ofNat_one]
  · simp only [h₁, h₂, h₃, h₄, ite_false]; exact h.keep r h₁ h₂ h₃ h₄
  · dsimp only; rw [writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · have hne := D_ne (D := D.setWidth 64) (by omega_arith) hk' hi he
      simp only [hne, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega_arith]
      · simp [h₁, show ¬ k < i + 1 by omega_arith]
  · simp only [h.ecx, hsub, ofNat32_beq_zero (show c - (i + 1) < 2 ^ 32 by omega_arith)]

theorem LInv.zero {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) : LInv s D K c 0 s :=
  ⟨by rw [hp.esi]; simp, by rw [hp.edx]; simp, by rw [hp.ecx, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
    fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : BitVec 32} {c : Nat} {s' : State} (h : LInv s D K c c s') :
    BPost s D K c s' :=
  ⟨h.esi, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left hk], h.frame⟩

theorem loop_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) (hc0 : c ≠ 0) :
    WP isa xorLoop s (BPost s D K c) := by
  have hc := hp.d_fit
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ BPost s D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (byte_step hp hi hI) fun s'' ⟨h', hz⟩ => ?_
    have he : isa.eval .ne s'' = some (!decide (c - (i + 1) = 0)) := by
      show eval .ne s'' = _
      simp only [eval, hz, Option.map_some]
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [he]; simp; omega_arith, LInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [he]; simp; omega_arith, c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega_arith, LInv.zero hp⟩

set_option simprocs false in
theorem test_ecx_ok {s : State} {c : Nat} (h : s.gpr .ecx = BitVec.ofNat 32 c) (hc : c < 2 ^ 32) :
    WP isa (.block [.alu .test .ecx (.reg .ecx)]) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (c = 0)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [BitVec.and_self, h, ofNat32_beq_zero hc]

theorem xorBytes_eq : xorBytes = .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) xorLoop) := rfl

theorem xorBytes_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.d_fit
  rw [xorBytes_eq]
  refine WP.seq (WP.mono (test_ecx_ok hp.ecx (by have := hp.k_fit; omega_arith)) fun s₁ ⟨g₁, m₁, r₁, w₁, z₁⟩ => ?_)
  have hp₁ : BPre s₁ D K c := ⟨by rw [g₁, hp.esi], by rw [g₁, hp.edx], by rw [g₁, hp.ecx], hp.d_fit, hp.k_fit,
    fun k hk => by rw [w₁]; exact hp.wD k hk, fun k hk => by rw [r₁, w₁]; exact hp.rK k hk,
    hp.sep⟩
  have conv : ∀ s', BPost s₁ D K c s' → BPost s D K c s' := fun s' h =>
    ⟨h.esi, fun r a b d e => by rw [h.keep r a b d e, g₁], by rw [h.rd, r₁], by rw [h.wr, w₁],
      fun k hk => by rw [h.data k hk, m₁], m₁ ▸ h.frame⟩
  refine WP.ite (decide (c = 0)) (by show eval .e s₁ = _; simp only [eval, z₁])
    (fun h0 => WP.block_nil (M := isa) (conv _ ?_)) (fun h0 => WP.mono (loop_ok hp₁ (by simpa using h0)) conv)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp₁).post


theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem add_ofNat32 (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

/-- The flags of `cmp` and nothing else. -/
theorem cmpi_ok (s : State) (d : Reg) (v : BitVec 32) :
    WP isa (.block [.alu .cmp d (.imm v)]) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) :=
  Wp.cons rfl (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem ofNat32_add_toNat (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    (x + BitVec.ofNat 32 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem setWidth_add (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    (x + BitVec.ofNat 32 n).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-! ## From a source to a destination -/

/-- What `xorBytesTo` and `xorWide` need: `c` bytes of the source at `S` to
read, of the destination at `D` to write, and `c + 3` at `K` to read (the
bytes a word at a time); the keystream apart from the destination, and the
source either the destination itself or apart from it. Where they are only
matters if there are bytes (`c ≠ 0`). -/
structure TPre (s : State) (S D K : BitVec 32) (c : Nat) : Prop where
  esi : s.gpr .esi = S
  edx : s.gpr .edx = D
  ebp : s.gpr .ebp = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 c
  s_fit : S.toNat + c ≤ 2 ^ 32
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c + 3 < 2 ^ 32
  rS : c ≠ 0 → ∀ off n, off + n ≤ c → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 off) n
  wD : c ≠ 0 → ∀ off n, off + n ≤ c → InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 off) n
  rK : c ≠ 0 → ∀ off n, off + n ≤ c + 3 → InRegions (s.rd ++ s.wr) (K.setWidth 64 + BitVec.ofNat 64 off) n
  sep : c ≠ 0 → (⟨D.setWidth 64, c⟩ : Region).Disjoint ⟨K.setWidth 64, c + 3⟩
  alias : c ≠ 0 → S = D ∨ (⟨S.setWidth 64, c⟩ : Region).Disjoint ⟨D.setWidth 64, c⟩

/-- What they leave: the source XORed with the keystream in the destination,
and `esi`, `edx` past them; only `eax`, `ecx`, `edx`, `esi` and `ebp` are
written. -/
structure TPost (s : State) (S D K : BitVec 32) (c : Nat) (s' : State) : Prop where
  esi : s'.gpr .esi = S + BitVec.ofNat 32 c
  edx : s'.gpr .edx = D + BitVec.ofNat 32 c
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    s.mem (S.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

/-- After the first `i` bytes. -/
structure TInv (s : State) (S D K : BitVec 32) (c i : Nat) (s' : State) : Prop where
  esi : s'.gpr .esi = S + BitVec.ofNat 32 i
  edx : s'.gpr .edx = D + BitVec.ofNat 32 i
  ebp : s'.gpr .ebp = K + BitVec.ofNat 32 i
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (c - i)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    if k < i then s.mem (S.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
    else s.mem (D.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

namespace TPre
variable {s : State} {S D K : BitVec 32} {c : Nat} (hp : TPre s S D K c)
include hp

/-- The keystream is outside the destination. -/
theorem kbyte (hc0 : c ≠ 0) {m : Mem} (hf : Frame [⟨D.setWidth 64, c⟩] s.mem m) {k : Nat} (hk : k < c + 3) :
    m (K.setWidth 64 + BitVec.ofNat 64 k) = s.mem (K.setWidth 64 + BitVec.ofNat 64 k) :=
  hf _ fun r hr hc => by
    have := hp.k_fit
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep hc0 _ hc (Offset.contains_base _ (by omega_arith) (by lit_omega))

/-- The source not yet consumed is intact: in place, it is the destination
after the bytes done; otherwise, it is outside the destination. -/
theorem sbyte {i : Nat} {s' : State} (h : TInv s S D K c i s') {k : Nat} (hk : k < c) (hi : i ≤ k) :
    s'.mem (S.setWidth 64 + BitVec.ofNat 64 k) = s.mem (S.setWidth 64 + BitVec.ofNat 64 k) := by
  have := hp.s_fit
  rcases hp.alias (by omega_arith) with he | hd
  · subst he; rw [h.data k hk, ite_eq_right (by omega_arith)]
  · exact h.frame _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base _ (by omega_arith) (by lit_omega)) hc

theorem zero : TInv s S D K c 0 s :=
  ⟨by rw [hp.esi]; simp, by rw [hp.edx]; simp, by rw [hp.ebp]; simp, by rw [hp.ecx, Nat.sub_zero],
    fun _ _ _ _ _ _ => rfl, rfl, rfl, fun k _ => by simp, Frame.refl _ _⟩

end TPre

theorem TInv.post {s : State} {S D K : BitVec 32} {c : Nat} {s' : State} (h : TInv s S D K c c s') :
    TPost s S D K c s' :=
  ⟨h.esi, h.edx, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left hk], h.frame⟩

set_option simprocs false in
theorem byteTo_step {s : State} {S D K : BitVec 32} {c i : Nat} (hp : TPre s S D K c) (hi : i < c) {s₁ : State}
    (h : TInv s S D K c i s₁) :
    WP isa (.block xorToBody) s₁ fun s' => TInv s S D K c (i + 1) s' ∧ s'.zf = some (decide (c - (i + 1) = 0)) := by
  have hs := hp.s_fit
  have hc := hp.d_fit
  have hk := hp.k_fit
  have ea₀ : (S + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = S.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega_arith)
  have ea₁ : (D + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega_arith)
  have ea₂ : (K + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = K.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega_arith)
  have cd : (⟨D.setWidth 64, c⟩ : Region).Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have i₀ : InRegions (s₁.rd ++ s₁.wr) (S.setWidth 64 + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hp.rS (by omega_arith) i 1 (by omega_arith)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K.setWidth 64 + BitVec.ofNat 64 i) 4 := by
    rw [h.rd, h.wr]; exact hp.rK (by omega_arith) i 4 (by omega_arith)
  have o₁ : InRegions s₁.wr (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by
    rw [h.wr]; exact hp.wD (by omega_arith) i 1 (by omega_arith)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorToBody, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.load32,
    State.store8, State.setReg, State.setFlags, Reg8.reg, h.esi, h.edx, h.ebp, ea₀, ea₁, ea₂, i₀, i₂, o₁,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hk' : s₁.mem (K.setWidth 64 + BitVec.ofNat 64 i) = s.mem (K.setWidth 64 + BitVec.ofNat 64 i) :=
    hp.kbyte (by omega_arith) h.frame (by omega_arith)
  have hd : s₁.mem (S.setWidth 64 + BitVec.ofNat 64 i) = s.mem (S.setWidth 64 + BitVec.ofNat 64 i) :=
    hp.sbyte h hi (Nat.le_refl _)
  rw [xor_low, low_byte, hd, hk']
  have hfd : Frame [⟨D.setWidth 64, c⟩] s₁.mem (s₁.mem.writeW (D.setWidth 64 + BitVec.ofNat 64 i)
      (s.mem (S.setWidth 64 + BitVec.ofNat 64 i) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 i))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have hsub : BitVec.ofNat 32 (c - i) - 1 = BitVec.ofNat 32 (c - (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by omega_arith)]; simp; omega_arith),
      toNat_ofNat_lt32 (by omega_arith), toNat_ofNat_lt32 (by omega_arith)]
    simp; omega_arith
  refine ⟨⟨?esi, ?edx, ?ebp, ?ecx, fun r h₁ h₂ h₃ h₄ h₅ => ?_, h.rd, h.wr, fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  case esi | edx | ebp | ecx =>
    simp (config := {decide := true}) only [ite_true, ite_false, h.ecx, hsub, add_ofNat_one]
  · simp only [h₁, h₂, h₃, h₄, h₅, ite_false]; exact h.keep r h₁ h₂ h₃ h₄ h₅
  · dsimp only; rw [writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · have hne := D_ne (D := D.setWidth 64) (by omega_arith) hk' hi he
      simp only [hne, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega_arith]
      · simp [h₁, show ¬ k < i + 1 by omega_arith]
  · simp only [h.ecx, hsub, ofNat32_beq_zero (show c - (i + 1) < 2 ^ 32 by omega_arith)]

theorem loopTo_ok {s : State} {S D K : BitVec 32} {c : Nat} (hp : TPre s S D K c) (hc0 : c ≠ 0) :
    WP isa xorToLoop s (TPost s S D K c) := by
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ TInv s S D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorToBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ TPost s S D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (byteTo_step hp hi hI) fun s'' ⟨h', hz⟩ => ?_
    have he : isa.eval .ne s'' = some (!decide (c - (i + 1) = 0)) := by
      show eval .ne s'' = _
      simp only [eval, hz, Option.map_some]
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [he]; simp; omega_arith, TInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [he]; simp; omega_arith, c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega_arith, hp.zero⟩

theorem TPre.of {s s' : State} {S D K : BitVec 32} {c : Nat} (hp : TPre s S D K c) (hg : s'.gpr = s.gpr)
    (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : TPre s' S D K c :=
  ⟨by rw [hg, hp.esi], by rw [hg, hp.edx], by rw [hg, hp.ebp], by rw [hg, hp.ecx], hp.s_fit, hp.d_fit, hp.k_fit,
    fun hc o n h => by rw [hr, hw]; exact hp.rS hc o n h, fun hc o n h => by rw [hw]; exact hp.wD hc o n h,
    fun hc o n h => by rw [hr, hw]; exact hp.rK hc o n h, hp.sep, hp.alias⟩

theorem TPost.of {s s₁ s' : State} {S D K : BitVec 32} {c : Nat} (h : TPost s₁ S D K c s') (hg : s₁.gpr = s.gpr)
    (hm : s₁.mem = s.mem) (hr : s₁.rd = s.rd) (hw : s₁.wr = s.wr) : TPost s S D K c s' :=
  ⟨h.esi, h.edx, fun r a b d e f => by rw [h.keep r a b d e f, hg], by rw [h.rd, hr], by rw [h.wr, hw],
    fun k hk => by rw [h.data k hk, hm], hm ▸ h.frame⟩

theorem xorBytesTo_eq : xorBytesTo = .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) xorToLoop) := rfl

theorem xorBytesTo_ok {s : State} {S D K : BitVec 32} {c : Nat} (hp : TPre s S D K c) :
    WP isa xorBytesTo s (TPost s S D K c) := by
  rw [xorBytesTo_eq]
  refine WP.seq (WP.mono (test_ecx_ok hp.ecx (by have := hp.k_fit; omega_arith)) fun s₁ ⟨g₁, m₁, r₁, w₁, z₁⟩ => ?_)
  have hp₁ : TPre s₁ S D K c := hp.of g₁ r₁ w₁
  refine WP.ite (decide (c = 0)) (by show eval .e s₁ = _; simp only [eval, z₁])
    (fun h0 => WP.block_nil (M := isa) (TPost.of ?_ g₁ m₁ r₁ w₁))
    (fun h0 => WP.mono (loopTo_ok hp₁ (by simpa using h0)) fun s' h => h.of g₁ m₁ r₁ w₁)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (hp₁.zero).post

/-! ## 16 bytes at a time -/

/-- A byte at offset `k` after a 16-byte write at offset `off`. -/
theorem byte_write16 (m : Mem) (a : Addr) (v : BitVec 128) {off k : Nat} (ho : off + 16 ≤ 2 ^ 32)
    (hk : k < 2 ^ 32) : (m.writeW (a + BitVec.ofNat 64 off) v) (a + BitVec.ofNat 64 k) =
      if off ≤ k ∧ k < off + 16 then v.extractLsb' (8 * (k - off)) 8 else m (a + BitVec.ofNat 64 k) := by
  by_cases h : off ≤ k ∧ k < off + 16
  · rw [ite_eq_left h, show a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 off + BitVec.ofNat 64 (k - off) by
      rw [Offset.add_add, Nat.add_sub_cancel' h.1]]
    exact writeW_byte _ _ _ (by omega_arith) (by lit_omega)
  · rw [ite_eq_right h]
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' a (by lit_omega) (by lit_omega)]
    split <;> omega_arith

theorem chunk_step {s : State} {S D K : BitVec 32} {c i : Nat} (hp : TPre s S D K c) (hi : 16 * (i + 1) ≤ c)
    {s₁ : State} (h : TInv s S D K c (16 * i) s₁) :
    WP isa (.block chunkBody) s₁ fun s' =>
      TInv s S D K c (16 * (i + 1)) s' ∧ s'.cf = some (decide (c - 16 * (i + 1) < 16)) := by
  have hs := hp.s_fit
  have hc := hp.d_fit
  have hk := hp.k_fit
  have ea₀ : s₁.ea (at_ .esi 0) = S.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    show (s₁.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _
    rw [h.esi]; exact ptr_add _ (by omega_arith)
  have ea₁ : s₁.ea (at_ .edx 0) = D.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    show (s₁.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [h.edx]; exact ptr_add _ (by omega_arith)
  have ea₂ : s₁.ea (at_ .ebp 0) = K.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    show (s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = _
    rw [h.ebp]; exact ptr_add _ (by omega_arith)
  have o₁ : InRegions s₁.wr (D.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.wr]; exact hp.wD (by omega_arith) _ _ (by omega_arith)
  have i₀ : InRegions (s₁.rd ++ s₁.wr) (S.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.rd, h.wr]; exact hp.rS (by omega_arith) _ _ (by omega_arith)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.rd, h.wr]; exact hp.rK (by omega_arith) _ _ (by omega_arith)
  rw [show chunkBody = [.movdquLoad .xmm4 (at_ .esi 0), .movdquLoad .xmm5 (at_ .ebp 0), xb .pxor .xmm4 .xmm5,
      .movdquStore (at_ .edx 0) .xmm4] ++ [.alu .add .esi (.imm 16), .alu .add .edx (.imm 16),
      .alu .add .ebp (.imm 16), .alu .sub .ecx (.imm 16), .alu .cmp .ecx (.imm 16)] from rfl, WP.block_append_iff]
  refine WP.mono (Q := fun s₂ : State => s₂.gpr = s₁.gpr ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      s₂.mem = s₁.mem.writeW (D.setWidth 64 + BitVec.ofNat 64 (16 * i))
        (s₁.mem.readW (S.setWidth 64 + BitVec.ofNat 64 (16 * i)) 128 ^^^
          s₁.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (16 * i)) 128)) ?_ fun s₂ ⟨g₂, r₂, w₂, m₂⟩ => ?_
  · apply WP.of_runBlock
    simp only [xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
      State.store128, ea_setXmm, ea₀, ea₁, ea₂, i₀, i₂, RegUpd.wr_setXmm, o₁, ite_true,
      RegUpd.mem_setXmm, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨trivial, trivial, trivial, ?_⟩
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm4 = .xmm5),
      XBinOp.eval]
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_addi fun s₄ u₄ => ?_
  refine Wp.wp_addi fun s₅ u₅ => ?_
  refine Wp.wp_subi fun s₆ u₆ _ _ => ?_
  refine Wp.wp_cmpi fun s₇ u₇ hcf _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, fun r a b d e f => ?_, ?_, ?_,
    fun k hk' => ?_, ?_⟩, ?_⟩
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h.esi,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat32]; rfl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, h.edx,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat32]; rfl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, h.ebp,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat32]; rfl
  · rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, h.ecx,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_ofNat32 (by omega_arith) (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (by omega_arith)
  · rw [u₇.gpr, u₆.other _ b, u₅.other _ f, u₄.other _ d, u₃.other _ e, g₂, h.keep r a b d e f]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, r₂, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂, h.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, byte_write16 _ _ _ (by omega_arith) (by omega_arith)]
    by_cases hin : 16 * i ≤ k ∧ k < 16 * i + 16
    · rw [ite_eq_left hin, ite_eq_left (by omega_arith), BitVec.extractLsb'_xor, byte_readW _ _ (by omega_arith),
        byte_readW _ _ (by omega_arith), Offset.add_add, Offset.add_add, Nat.add_sub_cancel' hin.1,
        hp.sbyte h hk' hin.1, hp.kbyte (by omega_arith) h.frame (by omega_arith)]
    · rw [ite_eq_right hin, h.data k hk']
      by_cases hlt : k < 16 * i
      · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_arith)]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
    exact h.frame.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by lit_omega)))
  · rw [hcf, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, h.ecx,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_ofNat32 (by omega_arith) (by omega_arith),
      toNat_ofNat_lt32 (by omega_arith), toNat_ofNat_lt32 (by omega_arith)]
    exact congrArg (fun n => some (decide (n < 16))) (by omega_arith)

theorem chunks_ok {s : State} {S D K : BitVec 32} {c : Nat} (hp : TPre s S D K c) (hc : 16 ≤ c) :
    WP isa (.loop (.block chunkBody) .ae) s (TInv s S D K c (16 * (c / 16))) := by
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - 16 * i ∧ 16 * (i + 1) ≤ c ∧ TInv s S D K c (16 * i) s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block chunkBody) s' (fun s'' =>
      (isa.eval .ae s'' = some false ∧ TInv s S D K c (16 * (c / 16)) s'') ∨
      (isa.eval .ae s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (chunk_step hp hi hI) fun s'' ⟨h', hcf⟩ => ?_
    have he : isa.eval .ae s'' = some (!decide (c - 16 * (i + 1) < 16)) := by
      show eval .ae s'' = _
      simp only [eval, hcf, Option.map_some]
    by_cases hl : c - 16 * (i + 1) < 16
    · exact .inl ⟨by rw [he]; simp [hl], by rwa [show c / 16 = i + 1 by omega_arith]⟩
    · exact .inr ⟨by rw [he]; simp [hl], c - 16 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega_arith, by simpa using hp.zero⟩

theorem xorWide_eq : xorWide = .seq (.block [.alu .cmp .ecx (.imm 16)])
    (.seq (.ite .b (.block []) (.loop (.block chunkBody) .ae)) xorBytesTo) := rfl

theorem TInv.of {s s₁ s' : State} {S D K : BitVec 32} {c i : Nat} (h : TInv s S D K c i s₁) (hg : s'.gpr = s₁.gpr)
    (hm : s'.mem = s₁.mem) (hr : s'.rd = s₁.rd) (hw : s'.wr = s₁.wr) : TInv s S D K c i s' :=
  ⟨by rw [hg, h.esi], by rw [hg, h.edx], by rw [hg, h.ebp], by rw [hg, h.ecx],
    fun r a b d e f => by rw [hg, h.keep r a b d e f], by rw [hr, h.rd], by rw [hw, h.wr],
    fun k hk => by rw [hm, h.data k hk], hm ▸ h.frame⟩

theorem xorWide_ok {s : State} {S D K : BitVec 32} {c : Nat} (hp : TPre s S D K c) :
    WP isa xorWide s (TPost s S D K c) := by
  have hs := hp.s_fit
  have hc := hp.d_fit
  have hk := hp.k_fit
  rw [xorWide_eq]
  refine WP.seq (WP.mono (cmpi_ok s .ecx 16) fun s₁ ⟨g₁, m₁, _, r₁, w₁, c₁⟩ => ?_)
  rw [hp.ecx, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, toNat_ofNat_lt32 (by omega_arith),
    toNat_ofNat_lt32 (by omega_arith)] at c₁
  have hp₁ : TPre s₁ S D K c := hp.of g₁ r₁ w₁
  refine WP.mono (Q := TPost s₁ S D K c) ?_ fun s' h => h.of g₁ m₁ r₁ w₁
  refine WP.seq (WP.mono (Q := TInv s₁ S D K c (16 * (c / 16))) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (c < 16)) (by show eval .b s₁ = _; simp only [eval, c₁]) (fun h => ?_)
      (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      rw [show 16 * (c / 16) = 0 by omega_arith]; exact WP.block_nil hp₁.zero
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at h
      exact chunks_ok hp₁ h
  -- The bytes after the last multiple of 16.
  have hq : 16 * (c / 16) ≤ c := Nat.mul_div_le c 16
  generalize 16 * (c / 16) = q at hq h₂
  rw [xorBytesTo_eq]
  refine WP.seq (WP.mono (test_ecx_ok h₂.ecx (by omega_arith)) fun s₃ ⟨g₃, m₃, r₃, w₃, z₃⟩ => ?_)
  have h₃ := h₂.of g₃ m₃ r₃ w₃
  by_cases hz : c - q = 0
  · -- Nothing left.
    have hqc : q = c := by omega_arith
    subst hqc
    refine WP.ite (decide (q - q = 0)) (by show eval .e s₃ = _; simp only [eval, z₃])
      (fun _ => WP.block_nil (M := isa) h₃.post) (fun h0 => absurd hz (of_decide_eq_false h0))
  have eX : ∀ (X : BitVec 32) t, X.toNat + c ≤ 2 ^ 32 → t ≤ c - q →
      (X + BitVec.ofNat 32 q).setWidth 64 + BitVec.ofNat 64 t = X.setWidth 64 + BitVec.ofNat 64 (q + t) := by
    intro X t hX _
    rw [setWidth_add _ (by omega_arith), Offset.add_add]
  have eX0 : ∀ (X : BitVec 32), X.toNat + c ≤ 2 ^ 32 →
      (X + BitVec.ofNat 32 q).setWidth 64 = X.setWidth 64 + BitVec.ofNat 64 q :=
    fun X hX => setWidth_add _ (by omega_arith)
  have hb : TPre s₃ (S + BitVec.ofNat 32 q) (D + BitVec.ofNat 32 q) (K + BitVec.ofNat 32 q) (c - q) := by
    refine ⟨h₃.esi, h₃.edx, h₃.ebp, h₃.ecx, by rw [ofNat32_add_toNat _ (by omega_arith)]; omega_arith,
      by rw [ofNat32_add_toNat _ (by omega_arith)]; omega_arith,
      by rw [ofNat32_add_toNat _ (by omega_arith)]; omega_arith,
      fun _ o n hn => ?_, fun _ o n hn => ?_, fun _ o n hn => ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [eX S o hs (by omega_arith), h₃.rd, h₃.wr]; exact hp₁.rS (by omega_arith) _ _ (by omega_arith)
    · rw [eX D o hc (by omega_arith), h₃.wr]; exact hp₁.wD (by omega_arith) _ _ (by omega_arith)
    · rw [eX0 K (by omega_arith), Offset.add_add, h₃.rd, h₃.wr]; exact hp₁.rK (by omega_arith) _ _ (by omega_arith)
    · rw [eX0 D hc, eX0 K (by omega_arith)]
      exact ((hp.sep (by omega_arith)).sub_left (Offset.sub_base _ (by omega_arith))).sub_right
        (Offset.sub_base _ (by omega_arith))
    · rcases hp.alias (by omega_arith) with he | hd
      · exact .inl (by rw [he])
      · rw [eX0 S hs, eX0 D hc]
        exact .inr ((hd.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))
  refine WP.ite (decide (c - q = 0)) (by show eval .e s₃ = _; simp only [eval, z₃])
    (fun h0 => absurd (of_decide_eq_true h0) hz) (fun _ => ?_)
  refine WP.mono (loopTo_ok hb hz) fun s₄ h₄ => ⟨?_, ?_, fun r a b d e f => ?_, ?_, ?_, fun k hk' => ?_, ?_⟩
  · rw [h₄.esi, add_ofNat32, Nat.add_sub_cancel' hq]
  · rw [h₄.edx, add_ofNat32, Nat.add_sub_cancel' hq]
  · rw [h₄.keep r a b d e f, h₃.keep r a b d e f]
  · rw [h₄.rd, h₃.rd]
  · rw [h₄.wr, h₃.wr]
  · by_cases hlt : k < q
    · have hf : s₄.mem (D.setWidth 64 + BitVec.ofNat 64 k) = s₃.mem (D.setWidth 64 + BitVec.ofNat 64 k) := by
        refine h₄.frame _ fun r hr hcon => ?_
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains] at hcon
        rw [eX0 D hc, Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
        split at hcon <;> omega_arith
      rw [hf, h₃.data k hk', ite_eq_left hlt]
    · obtain ⟨t, rfl⟩ : ∃ t, k = q + t := ⟨k - q, by omega_arith⟩
      have e4 := h₄.data t (by omega_arith)
      rw [eX D t hc (by omega_arith), eX S t hs (by omega_arith), eX0 K (by omega_arith), Offset.add_add] at e4
      rw [e4, hp₁.sbyte h₃ hk' (by omega_arith), hp₁.kbyte (by omega_arith) h₃.frame (by omega_arith)]
  · refine h₃.frame.trans (h₄.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [eX0 D hc]
    exact Offset.sub_base _ (by omega_arith)


/-- `and` with `0xfffffff0`: rounding down to a multiple of 16. -/
theorem and_m16 (x : BitVec 32) : x &&& (0xfffffff0 : BitVec 32) = BitVec.ofNat 32 (x.toNat / 16 * 16) := by
  have : (0xfffffff0 : BitVec 32) = BitVec.ofNat 32 ((2 ^ 28 - 1) <<< 4) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega_arith),
    show n / 16 * 16 = (n >>> 4) <<< 4 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 4 ≤ i
  · by_cases h2 : i - 4 < 28
    · simp [hi, h2, show 4 + (i - 4) = i by omega_arith]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 32 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega_arith))
      simp [hi, h2, this, show 4 + (i - 4) = i by omega_arith]
  · simp [hi]

/-- `and` with 15: the remainder modulo 16. -/
theorem and_15 (x : BitVec 32) : x &&& (15 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 16) := by
  have : (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 4 - 1 < 2 ^ 32 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

end VG.Proof.ChaCha20.X86.Bytes
