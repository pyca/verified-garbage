module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on x86-64: copying the digest in a loop

`.loop (.block copyStep) .ne` copies the `4 n` bytes at `rsi` to `rdx`, four
at a time from the last, with `4 n` in `rcx`, when the two ranges are apart:
each step copies the four bytes below `rcx` and sets `ZF` iff `rcx` reaches
zero (`copyStep_ok`), and the loop's invariant is that the bytes from `rcx`
on are copied (`copyLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

theorem ea_idx (t : State) (b i : Reg) : t.ea { base := b, index := some i } = t.gpr b + t.gpr i := by
  simp [State.ea]

theorem bytesAt_copied32 (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem sub4 {k : Nat} (hk : 4 * (k + 1) < 2 ^ 63) :
    BitVec.ofNat 64 (4 * (k + 1)) - (4 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (4 * k) := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sx32 (by decide), Offset.ofNat_sub_ofNat (by omega),
    show 4 * (k + 1) - 4 = 4 * k by omega]

/-- One step: the four bytes below `rcx` copied, and `ZF` set iff none are left. -/
theorem copyStep_ok {u : State} {S D : Addr} {k : Nat} (hc : u.gpr .rcx = BitVec.ofNat 64 (4 * (k + 1)))
    (hk : 4 * (k + 1) < 2 ^ 63) (hs : u.gpr .rsi = S) (hd : u.gpr .rdx = D)
    (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (4 * k)) 4)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block Cfg.copyStep) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      u'.gpr .rcx = BitVec.ofNat 64 (4 * k) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧
      isa.eval .ne u' = some (!decide (k = 0)) ∧ u'.syms = u.syms ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S + BitVec.ofNat 64 (4 * k)) 32) := by
  have e := sub4 hk
  have hz : (BitVec.ofNat 64 (4 * k) == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · have : BitVec.ofNat 64 (4 * k) ≠ 0 := fun h' => by
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      have h₁ : (BitVec.ofNat 64 (4 * k) == 0) = false := by simpa using this
      have h₂ : decide (k = 0) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [h₁, h₂]
  apply WP.of_runBlock
  simp only [Cfg.copyStep, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32,
    State.load32, State.store32, State.setReg32, ea_idx, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc, e, hs, hd, hr, hw, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r h₁ h₂ => by simp only [h₁, h₂, ite_false], ?_, rfl, ?_⟩
  · simp only [eval, RegUpd.zf_setReg, RegUpd.zf_arithFlags, Option.map_some, hz]
  · simp

/-- What holds after the steps down to `rcx = 4 (k + 1)`: the bytes from there on are copied. -/
structure CopyInv (u : State) (S D : Addr) (n k : Nat) (s : State) : Prop where
  rd : s.rd = u.rd
  wr : s.wr = u.wr
  rcx : s.gpr .rcx = BitVec.ofNat 64 (4 * (k + 1))
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = u.gpr r
  syms : s.syms = u.syms
  lt : k < n
  frame : Frame [⟨D, 4 * n⟩] u.mem s.mem
  bytes : Spec.Sha256.bytesAt s.mem (D + BitVec.ofNat 64 (4 * (k + 1))) (4 * n - 4 * (k + 1)) =
    Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (4 * (k + 1))) (4 * n - 4 * (k + 1))

/-- The loop: the `4 n` bytes at `rsi` to `rdx`, with `4 n` in `rcx`, when they are apart. -/
theorem copyLoop_ok {u : State} {S D : Addr} {n : Nat} (hn : 0 < n) (hn' : 4 * n < 2 ^ 63)
    (hsep : Region.Disjoint ⟨S, 4 * n⟩ ⟨D, 4 * n⟩) (hS : S.toNat + 4 * n ≤ 2 ^ 64) (hc : u.gpr .rcx = BitVec.ofNat 64 (4 * n)) (hs : u.gpr .rsi = S)
    (hd : u.gpr .rdx = D) (hr : ∀ i < n, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (4 * i)) 4)
    (hw : ∀ i < n, InRegions u.wr (D + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.loop (.block Cfg.copyStep) .ne) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.syms = u.syms ∧ Frame [⟨D, 4 * n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem D (4 * n) = Spec.Sha256.bytesAt u.mem S (4 * n) := by
  refine WP.loop (M := isa) (CopyInv u S D n) ?_ (n - 1) u
    ⟨rfl, rfl, by rw [hc]; congr 2; omega, fun _ _ _ => rfl, rfl, by omega, Frame.refl _ _, by
      rw [show 4 * n - 4 * (n - 1 + 1) = 0 by omega]; rfl⟩
  intro k s hi
  have hsi : s.gpr .rsi = S := (hi.gpr _ (by decide) (by decide)).trans hs
  have hdx : s.gpr .rdx = D := (hi.gpr _ (by decide) (by decide)).trans hd
  have hk := hi.lt
  -- The bytes of the source, unchanged.
  have hsrc : ∀ {a m : Nat}, a + m ≤ 4 * n →
      Spec.Sha256.bytesAt s.mem (S + BitVec.ofNat 64 a) m = Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 a) m :=
    fun {a m} h => bytesAt_frame hi.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_left (Offset.sub_base _ h)) (by omega)
  refine WP.mono (copyStep_ok (k := k) hi.rcx (by omega) hsi hdx (by rw [hi.rd, hi.wr]; exact hr k hk)
    (by rw [hi.wr]; exact hw k hk)) fun s' ⟨hrd, hwr, hcx, hg, hne, hsy, hm⟩ => ?_
  have hf₁ : Frame [⟨D + BitVec.ofNat 64 (4 * k), 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hfr : Frame [⟨D, 4 * n⟩] u.mem s'.mem := hi.frame.trans (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩)
  -- The bytes copied: the new word, then those from before.
  have hb : Spec.Sha256.bytesAt s'.mem (D + BitVec.ofNat 64 (4 * k)) (4 * n - 4 * k) =
      Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (4 * k)) (4 * n - 4 * k) := by
    rw [show 4 * n - 4 * k = 4 + (4 * n - 4 * (k + 1)) by omega, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add, show 4 * k + 4 = 4 * (k + 1) by omega]
    congr 1
    · rw [hm, bytesAt_copied32, hsrc (by omega)]
    · rw [← hi.bytes]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine .inl ⟨hne, hrd.trans hi.rd, hwr.trans hi.wr, fun r h₁ h₂ => (hg r h₁ h₂).trans (hi.gpr r h₁ h₂),
      hsy.trans hi.syms, hfr, ?_⟩
    have := hb
    rw [Nat.mul_zero, Nat.sub_zero, add_ofNat_zero, add_ofNat_zero] at this
    exact this
  · refine .inr ⟨by rw [hne]; simp only [decide_eq_false (Nat.pos_iff_ne_zero.mp hpos), Bool.not_false],
      k - 1, by omega, ⟨hrd.trans hi.rd, hwr.trans hi.wr, by rw [hcx]; congr 2; omega,
        fun r h₁ h₂ => (hg r h₁ h₂).trans (hi.gpr r h₁ h₂), hsy.trans hi.syms, by omega, hfr, ?_⟩⟩
    rw [show k - 1 + 1 = k by omega]
    exact hb

end VG.Proof.Ecdsa.Rfc6979.X86_64
